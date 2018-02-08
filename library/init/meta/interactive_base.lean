/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.data.option.basic
import init.meta.lean.parser init.meta.tactic init.meta.has_reflect

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def resolve_interactive_tactic_aux (tac_class_name tac_name : name) : tactic name :=
do let full_n := tac_class_name <.> "interactive" ++ tac_name,
   tactic.get_decl full_n >> pure full_n

meta class monad_interactive_tactic (config : out_param Type) (m : Type → Type) extends monad_tactic m :=
(type_name : name)
-- used to resolve an interactive tactic name like `simp`
(resolve_tactic (n : name) : tactic name :=
  -- look up $m.interactive.$n, or else tactic.interactive.$n
  resolve_interactive_tactic_aux type_name n <|> resolve_interactive_tactic_aux `tactic n)
-- emitted around each interactive step
(step {α : Type} (t : m α) : m unit := tactic.step t)
/- Like step, but should scope trace messages at the given position,
   and ensure that the exception position is after pos0.
   This function is called instead of step inside of unquoted begin-end blocks. -/
(istep {α : Type} (line0 col0 line col : nat) (tac : m α) : m unit :=
   interaction_monad_error.clamp_pos line0 line col $
     scope_impure (λ β, @scope_trace _ line col) (step tac))
/- emitted around each interactive step, may cache the output of `t`
   and reuse it if both `fingerprint` (representing the pre-execution state)
   and the fingerprint of the `tactic_state` match -/
(memoize {α : Type} (fingerprint : nat) (t : m α) : m unit := t >> pure ())
-- focus and solve the main goal using `t`, or fail
(solve1 (t : m unit) : m unit := tactic.solve1 t)
-- should call `tactic.save_info_thunk` with a representation of the current state
(save_info {} (p : pos) : m unit := tactic.save_info p)
(execute (cfg : option config) (t : m unit) : tactic unit)

-- note: explicit `m`
meta def execute_interactive_tactic {config : Type} (m : Type → Type) [monad_interactive_tactic config m]
  (cfg : option config) (t : m unit) : tactic unit :=
monad_interactive_tactic.execute cfg t

meta def resolve_interactive_tactic (tac_type tac : name) : tactic name :=
do let tac_type : pexpr := expr.const tac_type [],
   e ← tactic.to_expr ```(monad_interactive_tactic.resolve_tactic %%tac_type),
   t ← tactic.eval_expr (name → tactic name) e,
   t tac

namespace interactive
/-- (parse p) as the parameter type of an interactive tactic will instruct the Lean parser
    to run `p` when parsing the parameter and to pass the parsed value as an argument
    to the tactic. -/
@[reducible] meta def parse {α : Type} [has_reflect α] (p : parser α) : Type := α

/-- (parse_tactic m) as the parameter type of an interactive tactic will instruct the Lean parser
    to parse an interactive tactic block `'{' (tac : m unit) '}'` and to pass the parsed tactic
    as an argument to the outer tactic.
    If `use_solve1` is tt, the parsed tactic is wrapped in calls to
    `monad_interactive_tactic.solve1/istep` with the correct position information. -/
@[reducible] meta def parse_tactic (m : Type → Type) (use_solve1 := ff) : Type := m unit

inductive loc : Type
| wildcard : loc
| ns       : list (option name) → loc

meta def loc.include_goal : loc → bool
| loc.wildcard := tt
| (loc.ns ls)  := (ls.map option.is_none).bor

meta def loc.get_locals : loc → tactic (list expr)
| loc.wildcard := tactic.local_context
| (loc.ns xs)  := xs.mfoldl (λ ls n, match n with
  | none := pure ls
  | some n := do l ← tactic.get_local n, pure $ l :: ls
  end) []

section
variables {m : Type → Type} [monad_tactic m]

meta def loc.apply (hyp_tac : expr → m unit) (goal_tac : m unit) (l : loc) : m unit :=
do hs ← monad_lift l.get_locals,
   hs.mmap' hyp_tac,
   if l.include_goal then goal_tac else pure ()

meta def loc.try_apply (hyp_tac : expr → m unit) (goal_tac : m unit) (l : loc) : m unit :=
do hs ← monad_lift l.get_locals,
   let hts := hs.map hyp_tac,
   tactic.try_lst $ if l.include_goal then hts ++ [goal_tac] else hts
end

/-- Use `desc` as the interactive description of `p`. -/
meta def with_desc {α : Type} (desc : format) (p : parser α) : parser α := p

namespace types
variables {α β : Type}

-- optimized pretty printer
meta def brackets (l r : string) (p : parser α) := tk l *> p <* tk r

meta def list_of (p : parser α) := brackets "[" "]" $ sep_by (skip_info (tk ",")) p

precedence `⊢` : 0
precedence `|-` : 0

/-- The right-binding power 2 will terminate expressions by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
meta def tac_rbp := 2

/-- A 'tactic expression', which uses right-binding power 2 so that it is terminated by
    '<|>' (rbp 2), ';' (rbp 1), and ',' (rbp 0). It should be used for any (potentially)
    trailing expression parameters. -/
meta def texpr := parser.pexpr tac_rbp
/-- Parse an identifier or a '_' -/
meta def ident_ : parser name := ident <|> tk "_" *> return `_
meta def using_ident := (tk "using" *> ident)?
meta def with_ident_list := (tk "with" *> ident_*) <|> return []
meta def without_ident_list := (tk "without" *> ident*) <|> return []
meta def location := (tk "at" *> (tk "*" *> return loc.wildcard <|>
  (loc.ns <$> (((with_desc "⊢" $ tk "⊢" <|> tk "|-") *> return none) <|> some <$> ident)*))) <|> return (loc.ns [none])
meta def pexpr_list := list_of (parser.pexpr 0)
meta def opt_pexpr_list := pexpr_list <|> return []
meta def pexpr_list_or_texpr := pexpr_list <|> list.ret <$> texpr
meta def only_flag : parser bool := (tk "only" *> return tt) <|> return ff
end types

precedence only:0

open expr format tactic types
private meta def maybe_paren : list format → format
| []  := ""
| [f] := f
| fs  := paren (join fs)

private meta def unfold (e : expr) : tactic expr :=
do (expr.const f_name f_lvls) ← return e.get_app_fn,
   decl  ← get_decl f_name,
   new_f ← decl.instantiate_value_univ_params f_lvls,
   head_beta (expr.mk_app new_f e.get_app_args)

private meta def concat (f₁ f₂ : list format) :=
if f₁.empty then f₂ else if f₂.empty then f₁ else f₁ ++ [" "] ++ f₂

private meta def parser_desc_aux : expr → tactic (list format)
| `(ident)  := return ["id"]
| `(ident_) := return ["id"]
| `(parser.pexpr %%v) := return ["expr"]
| `(tk %%c) := list.ret <$> to_fmt <$> eval_expr string c
| `(cur_pos) := return []
| `(pure ._) := return []
| `(._ <$> %%p) := parser_desc_aux p
| `(skip_info %%p) := parser_desc_aux p
| `(set_goal_info_pos %%p) := parser_desc_aux p
| `(with_desc %%desc %%p) := list.ret <$> eval_expr format desc
| `(%%p₁ <*> %%p₂) := do
  f₁ ← parser_desc_aux p₁,
  f₂ ← parser_desc_aux p₂,
  return $ concat f₁ f₂
| `(%%p₁ <* %%p₂) := do
  f₁ ← parser_desc_aux p₁,
  f₂ ← parser_desc_aux p₂,
  return $ concat f₁ f₂
| `(%%p₁ *> %%p₂) := do
  f₁ ← parser_desc_aux p₁,
  f₂ ← parser_desc_aux p₂,
  return $ concat f₁ f₂
| `(many %%p) := do
  f ← parser_desc_aux p,
  return [maybe_paren f ++ "*"]
| `(optional %%p) := do
  f ← parser_desc_aux p,
  return [maybe_paren f ++ "?"]
| `(sep_by %%sep %%p) := do
  f₁ ← parser_desc_aux sep,
  f₂ ← parser_desc_aux p,
  return [maybe_paren f₂ ++ join f₁, " ..."]
| `(%%p₁ <|> %%p₂) := do
  f₁ ← parser_desc_aux p₁,
  f₂ ← parser_desc_aux p₂,
  return $ if f₁.empty then [maybe_paren f₂ ++ "?"] else
    if f₂.empty then [maybe_paren f₁ ++ "?"] else
    [paren $ join $ f₁ ++ [to_fmt " | "] ++ f₂]
| `(brackets %%l %%r %%p) := do
  f ← parser_desc_aux p,
  l ← eval_expr string l,
  r ← eval_expr string r,
  -- much better than the naive [l, " ", f, " ", r]
  return [to_fmt l ++ join f ++ to_fmt r]
| e          := do
  e' ← (do e' ← unfold e,
        guard $ e' ≠ e,
        return e') <|>
       (do f ← pp e,
        fail $ to_fmt "don't know how to pretty print " ++ f),
  parser_desc_aux e'

meta def param_desc : expr → tactic format
| `(parse %%p) := join <$> parser_desc_aux p
| `(parse_tactic %%tac) := return $ to_fmt "{ tactic }"
| `(opt_param %%t ._) := (++ "?") <$> pp t
| e := paren <$> pp e


private meta constant parse_binders_core (rbp : ℕ) : parser (list pexpr)
meta def parse_binders (rbp := std.prec.max) := with_desc "<binders>" (parse_binders_core rbp)

meta constant decl_attributes : Type

meta constant decl_attributes.apply : decl_attributes → name → parser unit

meta structure decl_modifiers :=
(is_private       : bool)
(is_protected     : bool)
(is_meta          : bool)
(is_mutual        : bool)
(is_noncomputable : bool)

meta structure decl_meta_info :=
(attrs      : decl_attributes)
(modifiers  : decl_modifiers)
(doc_string : option string)


meta structure single_inductive_decl :=
(attrs  : decl_attributes)
(sig    : expr)
(intros : list expr)

meta def single_inductive_decl.name (d : single_inductive_decl) : name :=
d.sig.app_fn.const_name

meta structure inductive_decl :=
(u_names     : list name)
(params      : list expr)
(decls       : list single_inductive_decl)

/-- Parses and elaborates a single or multiple mutual inductive declarations (without the `inductive` keyword), depending on `is_mutual` -/
meta constant inductive_decl.parse : decl_meta_info → parser inductive_decl

end interactive

section macros
open lean.parser
open interactive

private meta def parse_format : string → list char → parser pexpr
| acc []            := pure ``(to_fmt %%(reflect acc))
| acc ('\n'::s)     :=
do f ← parse_format "" s,
   pure ``(to_fmt %%(reflect acc) ++ format.line ++ %%f)
| acc ('{'::'{'::s) := parse_format (acc ++ "{") s
| acc ('{'::s) :=
do (e, s) ← with_input (lean.parser.pexpr 0) s.as_string,
   '}'::s ← return s.to_list | fail "'}' expected",
   f ← parse_format "" s,
   pure ``(to_fmt %%(reflect acc) ++ to_fmt %%e ++ %%f)
| acc (c::s) := parse_format (acc.str c) s

reserve prefix `format! `:100
@[user_notation]
meta def format_macro (_ : parse $ tk "format!") (s : string) : parser pexpr :=
parse_format "" s.to_list

private meta def parse_sformat : string → list char → parser pexpr
| acc []            := pure $ pexpr.of_expr (reflect acc)
| acc ('{'::'{'::s) := parse_sformat (acc ++ "{") s
| acc ('{'::s) :=
do (e, s) ← with_input (lean.parser.pexpr 0) s.as_string,
   '}'::s ← return s.to_list | fail "'}' expected",
   f ← parse_sformat "" s,
   pure ``(%%(reflect acc) ++ to_string %%e ++ %%f)
| acc (c::s) := parse_sformat (acc.str c) s

reserve prefix `sformat! `:100
@[user_notation]
meta def sformat_macro (_ : parse $ tk "sformat!") (s : string) : parser pexpr :=
parse_sformat "" s.to_list
end macros
