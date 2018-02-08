/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.meta.interactive init.meta.mk_dec_eq_instance

open lean
open lean.parser
open interactive

local postfix `?`:9001 := optional
local postfix *:9001 := many

/-- Goals can be tagged using a list of names. -/
def ttactic.tag : Type := list name

meta structure ttactic.tag_info :=
(tags_enabled : bool)
(tags         : expr_map ttactic.tag)

@[derive decidable_eq]
meta structure ttactic.goal :=
(tag    : ttactic.tag)
(target : expr)

/-- A 'tagged tactic' -/
@[reducible] meta def ttactic :=
state_t _root_.ttactic.tag_info tactic

namespace ttactic
open tactic

private meta def format_tag (t : tag) : format :=
let t := t.filter (λ n, ¬n.is_internal) in
match t with
| [] := ""
| ns := let ns := (ns.map to_fmt).intersperse ", " in
        format!"case {format.join ns}\n"
end

meta instance : has_to_tactic_format ttactic.goal :=
⟨λ g, (λ f, format_tag g.tag ++ f) <$> tactic.format_goal g.target⟩

meta instance : goal_type ttactic.goal := {
  get_target := goal.target,
  from_target := λ t, ⟨[], t⟩
}

protected meta def goal_cfg {m : Type → Type}
  [has_monad_lift_t tactic m] [has_monad_lift_t ttactic m] [monad m] : goal_cfg m := {
  goal_ty := ttactic.goal,
  get_goals := do {
    s ← get,
    gs ← monad_lift tactic.get_goals,
    pure $ gs.map $ λ g, {tag := (s.tags.find g).get_or_else [], target := g}
  },
  set_goals := λ gs, do {
    --modify $ λ s, {tags := native.rb_map.of_list $ gs.map (λ g, (g.target, g.tag)), ..s},
    monad_lift $ tactic.set_goals (gs.map goal.target)
  }
}

meta instance : monad_tactic ttactic :=
{ goal_cfg := ttactic.goal_cfg }

meta instance : monad_state_lift _ _ ttactic := infer_instance

meta def execute (t : ttactic unit) : tactic unit :=
t.run { tag_info . tags_enabled := false, tags := expr_map.mk _ }

meta instance : monad_interactive_tactic empty ttactic :=
{ type_name := `ttactic,
  execute := λ cfg, ttactic.execute,
  ..ttactic.monad_tactic }

section
parameters {m n : Type → Type}
include n
variables [monad_tactic m] [monad_state_lift tag_info n m] [monad n]

/-- Enable/disable goal tagging -/
meta def enable_tags (b : bool) : m punit :=
modify (λ s, { tags_enabled := b, ..s })

/-- Return tt iff goal tagging is enabled. -/
meta def tags_enabled : m bool :=
tag_info.tags_enabled <$> get

/-- Tag goal `g` with tag `t`. It does nothing is goal tagging is disabled.
    Remark: `set_goal g []` removes the tag -/
meta def set_tag (g : expr) (t : tag) : m unit :=
mwhen tags_enabled $
modify (λ s, { tags := if t = [] then s.tags.erase g
                                 else s.tags.insert g t, ..s }) >> pure ()

/-- Return tag associated with `g`. Return `[]` if there is no tag. -/
meta def get_tag (g : expr) : m tag :=
do s ← get, pure $ (s.tags.find g).get_or_else []

/- Goal tagging support -/
meta def with_enable_tags {α : Type} (t : m α) (b := tt) : m α :=
do old ← tags_enabled,
   enable_tags b,
   r ← t,
   enable_tags old,
   return r

meta def get_main_tag : m tag :=
main_goal >>= get_tag

meta def set_main_tag (t : tag) : m unit :=
do g ← main_goal, set_tag g t

meta def propagate_tags (tac : m unit) : m unit :=
do tag ← get_main_tag,
   if tag = [] then tac
   else focus1 $ do
     tac,
     gs ← get_goals,
     when (bnot gs.empty) $ do
       new_tag ← get_main_tag,
       when new_tag.empty $ with_enable_tags (set_main_tag tag)

meta def concat_tags (tac : m (list (name × expr))) : m (list (name × expr)) :=
mcond tags_enabled
  (do in_tag ← get_main_tag,
      r ← tac,
      /- remove assigned metavars -/
      r ← r.mfilter $ λ ⟨n, m⟩, bnot <$> is_assigned m,
      match r with
      | [(_, m)] := set_tag m in_tag /- if there is only new subgoal, we just propagate `in_tag` -/
      | _        := r.mmap' (λ ⟨n, m⟩, set_tag m (n::in_tag))
      end,
      pure r)
  tac

private meta def revert_new_hyps (input_hyp_uids : name_set) : m unit :=
do ctx ← local_context,
   let to_revert := ctx.foldr (λ h r, if input_hyp_uids.contains h.local_uniq_name then r else h::r) [],
   tag ← get_main_tag,
   m   ← revert_lst to_revert,
   set_main_tag (mk_num_name `_case m :: tag)
end

namespace interactive
section
open tactic.interactive
parameters {m n : Type → Type}
include n
variables [monad_tactic m] [monad_state_lift tag_info n m] [monad n]

local notation `γ` := (monad_tactic.goal_cfg m).goal_ty

private meta def collect_hyps_uids : m name_set :=
do ctx ← local_context,
   return $ ctx.foldl (λ r h, r.insert h.local_uniq_name) mk_name_set

/--
Apply `t` to main goal, and revert any new hypothesis in the generated goals,
and tag generated goals when using supported tactics such as: `induction`, `apply`, `cases`, `constructor`, ...

This tactic is useful for writing robust proof scripts that are not sensitive
to the name generation strategy used by `t`.

```
example (n : ℕ) : n = n :=
begin
  with_cases { induction n },
  case nat.zero { reflexivity },
  case nat.succ : n' ih { reflexivity }
end
```

TODO(Leo): improve docstring
-/
meta def with_cases (t : parse_tactic m) : m unit :=
with_enable_tags $ focus1 $ do
  input_hyp_uids ← collect_hyps_uids,
  t,
  tactic.all_goals (revert_new_hyps input_hyp_uids)

/--
  Given the initial tag `in_tag` and the cases names produced by `induction` or `cases` tactic,
  update the tag of the new subgoals.
-/
private meta def set_cases_tags (in_tag : tag) (rs : list name) : m unit :=
do te ← tags_enabled,
   gs ← tactic.get_goals,
   match gs with
   | [g] := when te (set_tag g in_tag) -- if only one goal was produced, we should not make the tag longer
   | _   := do
     let tgs : list (name × expr) := rs.map₂ (λ n g, (n, g)) gs,
     if te
     then tgs.mmap' (λ ⟨n, g⟩, set_tag g (n::in_tag))
          /- If `induction/cases` is not in a `with_cases` block, we still set tags using `_case_simple` to make
             sure we can use the `case` notation.
             ```
             induction h,
             case c { ... }
             ```
          -/
     else tgs.mmap' (λ ⟨n, g⟩, with_enable_tags (set_tag g (`_case_simple::n::[])))
   end

private meta def set_induction_tags (in_tag : tag) (rs : list (name × list expr × list (name × expr))) : m unit :=
set_cases_tags in_tag (rs.map (λ e, e.1))

private meta def is_case_simple_tag : tag → bool
| (`_case_simple :: _) := tt
| _                    := ff

private meta def is_case_tag : tag → option nat
| (name.mk_numeral n `_case :: _) := some n.val
| _                               := none

private meta def tag_match (t : tag) (pre : list name) : bool :=
pre.is_prefix_of t.reverse &&
((is_case_tag t).is_some || is_case_simple_tag t)

private meta def collect_tagged_goals (pre : list name) : m (list γ) :=
do gs ← get_goals,
   gs.mfoldr (λ g r, do
      t ← get_tag (goal_type.get_target g),
      if tag_match t pre then return (g::r) else return r)
      []

private meta def find_tagged_goal_aux (pre : list name) : m γ :=
do gs ← collect_tagged_goals pre,
   match gs with
   | []  := fail ("invalid `case`, there is no goal tagged with prefix " ++ to_string pre)
   | [g] := return g
   | gs  := do
     tags : list (list name) ← gs.mmap (get_tag ∘ goal_type.get_target),
     fail ("invalid `case`, there is more than one goal tagged with prefix " ++ to_string pre ++ ", matching tags: " ++ to_string tags)
   end

private meta def find_tagged_goal (pre : list name) : m γ :=
match pre with
| [] := do g::gs ← get_goals, return g
| _  :=
  find_tagged_goal_aux pre
  <|>
  -- try to resolve constructor names, and try again
  do env ← get_env,
     pre ← pre.mmap (λ id,
           (do r_id ← resolve_constant id,
               if (env.inductive_type_of r_id).is_none then return id
               else return r_id)
            <|> return id),
     find_tagged_goal_aux pre
end

open expr

private meta def find_case (goals : list expr) (ty : name) (idx : nat) (num_indices : nat) : option expr → expr → option (expr × expr)
| case e := if e.has_meta_var then match e with
  | (mvar _ _ _)    :=
    do case ← case,
       guard $ e ∈ goals,
       pure (case, e)
  | (app _ _)    :=
    let idx :=
      match e.get_app_fn with
      | const (name.mk_string rec ty') _ :=
        guard (ty' = ty) >>
        match mk_simple_name rec with
        | `drec := some idx | `rec := some idx
        -- indices + major premise
        | `dcases_on := some (idx + num_indices + 1) | `cases_on := some (idx + num_indices + 1)
        | _ := none
        end
      | _ := none
      end in
    match idx with
    | none := list.foldl (<|>) (find_case case e.get_app_fn) $ e.get_app_args.map (find_case case)
    | some idx :=
      let args := e.get_app_args in
      do arg ← args.nth idx,
         args.enum.foldl
           (λ acc ⟨i, arg⟩, match acc with
             | some _ := acc
             | _      := if i ≠ idx then find_case none arg else none
             end)
           -- start recursion with likely case
           (find_case (some arg) arg)
    end
  | (lam _ _ _ e) := find_case case e
  | (macro n args) := list.foldl (<|>) none $ args.map (find_case case)
  | _             := none
  end else none

private meta def rename_lams : expr → list name → m unit
| (lam n _ _ e) (n'::ns) := (rename n n' >> rename_lams e ns) <|> rename_lams e (n'::ns)
| _             _        := skip

open interactive
open interactive.types

/--
Focuses on the `induction`/`cases`/`with_cases` subgoal corresponding to the given tag prefix, optionally renaming introduced locals.

```
example (n : ℕ) : n = n :=
begin
  induction n,
  case nat.zero { reflexivity },
  case nat.succ : a ih { reflexivity }
end
```
-/
meta def case (pre : parse ident_*) (ids : parse $ (tk ":" *> ident_*)?) (tac : parse_tactic m tt) : m unit :=
do g   ← find_tagged_goal pre,
   tag ← get_tag (goal_type.get_target g),
   let ids := ids.get_or_else [],
   match is_case_tag tag with
   | some n := do
      let m := ids.length,
      gs ← get_goals,
      set_goals $ g :: gs.filter (≠ g),
      intro_lst ids,
      when (m < n) $ intron (n - m),
      tactic.solve1 tac
   | none   :=
     match is_case_simple_tag tag with
     | tt :=
       /- Use the old `case` implementation -/
       do r         ← result,
          env       ← get_env,
          [ctor_id] ← return pre,
          ctor      ← resolve_constant ctor_id
                      <|> fail ("'" ++ to_string ctor_id ++ "' is not a constructor"),
          ty        ← (env.inductive_type_of ctor).to_monad
                      <|> fail ("'" ++ to_string ctor ++ "' is not a constructor"),
          let ctors := env.constructors_of ty,
          let idx   := env.inductive_num_params ty + /- motive -/ 1 +
                       list.index_of ctor ctors,
          /- Remark: we now use `find_case` just to locate the `lambda` used in `rename_lams`.
             The goal is now located using tags. -/
          (case, _) ← (find_case [goal_type.get_target g] ty idx (env.inductive_num_indices ty) none r ).to_monad
                      <|> fail "could not find open goal of given case",
          gs        ← get_goals,
          set_goals $ g :: gs.filter (≠ g),
          rename_lams case ids,
          tactic.solve1 tac
     | ff := failed
     end
   end

/--
  Given the initial tag `in_tag` and the cases names produced by `induction` or `cases` tactic,
  update the tag of the new subgoals.
-/
private meta def set_cases_tags (in_tag : tag) (rs : list name) : m unit :=
do te ← tags_enabled,
   gs ← tactic.get_goals,
   match gs with
   | [g] := when te (set_tag g in_tag) -- if only one goal was produced, we should not make the tag longer
   | _   := do
     let tgs : list (name × expr) := rs.map₂ (λ n g, (n, g)) gs,
     if te
     then tgs.mmap' (λ ⟨n, g⟩, set_tag g (n::in_tag))
          /- If `induction/cases` is not in a `with_cases` block, we still set tags using `_case_simple` to make
             sure we can use the `case` notation.
             ```
             induction h,
             case c { ... }
             ```
          -/
     else tgs.mmap' (λ ⟨n, g⟩, with_enable_tags (set_tag g (`_case_simple::n::[])))
   end

private meta def set_induction_tags (in_tag : tag) (rs : list (name × list expr × list (name × expr))) : m unit :=
set_cases_tags in_tag (rs.map (λ e, e.1))

meta def induction (hp : parse cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : m unit :=
do in_tag ← get_main_tag,
   rs ← tactic.interactive.induction hp rec_name ids revert,
   set_induction_tags in_tag rs

run_cmd tactic.doc_string `tactic.interactive.induction >>= tactic.add_doc_string `ttactic.interactive.induction

meta def by_cases (a : parse cases_arg_p) : m unit :=
concat_tags $ do
  (tactic.interactive.by_cases a : m unit),
  pos_g :: neg_g :: rest ← tactic.get_goals,
  return [(`pos, pos_g), (`neg, neg_g)]

run_cmd tactic.doc_string `tactic.interactive.by_cases >>= tactic.add_doc_string `ttactic.interactive.by_cases

meta def cases_core (e : expr) (ids : list name := []) : m unit :=
do in_tag ← get_main_tag,
focus1 $ do
 rs ← tactic.cases e ids,
 set_cases_tags in_tag rs
end

open binder_info
open expr
open tactic

meta def instantiate_binding : expr → tactic (expr × expr)
| (pi n bi d b) :=
do l ← mk_local' n bi d,
   pure (l, b.instantiate_var l)
| (lam n bi d b) :=
do l ← mk_local' n bi d,
   pure (l, b.instantiate_var l)
| _ := fail "expr.instaniate_binding: not a binding"

meta def instantiate_bindings : expr → tactic (list expr × expr) :=
λ e, (do (l, e) ← instantiate_binding e,
         (ls, e) ← instantiate_bindings e,
         pure (l::ls, e)) <|> pure ([], e)

private meta def wrap (f d : name) : tactic unit :=
do declaration.defn _ ls t b hints ff ← get_decl (`tactic.interactive ++ d),
   b' ← do {
     (m, b) ← instantiate_binding b,
     (m_monad_tactic, b) ← instantiate_binding b,
     (b_lams, b_bare) ← instantiate_bindings b,
     n ← mk_local' `n implicit `(Type → Type),
     n_state_lift ← to_expr ``(monad_state_lift tag_info %%n %%m) >>= mk_local' `_inst_2 inst_implicit,
     n_monad ← to_expr ``(monad %%n) >>= mk_local' `_inst_3 inst_implicit,
     fc ← mk_const f,
     let b' := fc m n m_monad_tactic n_state_lift n_monad b_bare,
     let b'_lams := [m, n, m_monad_tactic, n_state_lift, n_monad] ++ b_lams,
     pure $ lambdas b'_lams b'
   },
   t' ← infer_type b',
   add_decl (declaration.defn (`ttactic.interactive ++ d) ls t' b' hints ff),
   try $ tactic.doc_string (`tactic.interactive ++ d) >>= tactic.add_doc_string (`ttactic.interactive ++ d)

run_cmd [`intro, `intros, `introv, `rename, `revert, `rewrite, `rw, `rwa, `erewrite, `erw, `generalize, `simp].mmap (wrap ``propagate_tags)

run_cmd [`apply, `fapply, `eapply, `apply_with, `mapply, `constructor, `econstructor, `left, `right, `split].mmap (wrap ``concat_tags)

private meta def copy (d : name) : tactic unit :=
do declaration.defn _ ls t b hints ff ← get_decl (`tactic.interactive ++ d),
   t' ← do {
     (m, t) ← instantiate_binding t,
     (m_monad_tactic, t) ← instantiate_binding t,
     (t_pis, t) ← instantiate_bindings t,
     n ← mk_local' `n implicit `(Type → Type),
     n_state_lift ← to_expr ``(monad_state_lift tag_info %%n %%m) >>= mk_local' `_inst_2 inst_implicit,
     n_monad ← to_expr ``(monad %%n) >>= mk_local' `_inst_3 inst_implicit,
     let t'_pis := [m, n, m_monad_tactic, n_state_lift, n_monad] ++ t_pis,
     pure $ pis t'_pis t
   },
   b' ← do {
     (m, b) ← instantiate_binding b,
     (m_monad_tactic, b) ← instantiate_binding b,
     (b_lams, b_bare) ← instantiate_bindings b,
     n ← mk_local' `n default `(Type → Type),
     n_state_lift ← to_expr ``(monad_state_lift tag_info %%n %%m) >>= mk_local' `_inst_2 inst_implicit,
     n_monad ← to_expr ``(monad %%n) >>= mk_local' `_inst_3 inst_implicit,
     env ← get_env,
     let b' := b_bare.replace $ λ e _, do {
       let f := e.get_app_fn,
       (m::m_monad_tactic::args) ← pure e.get_app_args | none,
       guard f.is_constant,
       let n' := f.const_name.replace_prefix `tactic.interactive `ttactic.interactive,
       guard $ n' ≠ f.const_name ∧ env.contains n',
       let f' : expr := expr.const n' [],
       pure $ mk_app f' ([m, n, m_monad_tactic, n_state_lift, n_monad] ++ args)
     },
     let b'_lams := [m, n, m_monad_tactic, n_state_lift, n_monad] ++ b_lams,
     pure $ lambdas b'_lams b'
   },
   add_decl (declaration.defn (`ttactic.interactive ++ d) ls t' b' hints ff),
   try $ tactic.doc_string (`tactic.interactive ++ d) >>= tactic.add_doc_string (`ttactic.interactive ++ d)

run_cmd [`constructor_matching_aux, `constructor_matching, `cases, `cases_matching, `casesm, `try_cases_for_types, `cases_type].mmap copy

end interactive
end ttactic
