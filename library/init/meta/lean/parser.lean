/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic

namespace lean

-- TODO: make inspectable (and pure)
meta constant parser_state : Type
meta constant parser_state.env     : parser_state → environment
meta constant parser_state.options : parser_state → options
meta constant parser_state.cur_pos : parser_state → pos

@[reducible] meta def parser := interaction_monad parser_state

namespace parser
variable {α : Type}

meta constant set_env : environment → parser unit

/-- Make sure the next token is an identifier, consume it, and
    produce the quoted name `t, where t is the identifier. -/
meta constant ident : parser name
/-- Make sure the next token is a small nat, consume it, and produce it -/
meta constant small_nat : parser nat
/-- Check that the next token is `tk` and consume it. `tk` must be a registered token. -/
meta constant tk (tk : string) : parser unit
/-- Parse an unelaborated expression using the given right-binding power. -/
protected meta constant pexpr (rbp := std.prec.max) : parser pexpr

/-- Do not report info from content parsed by `p`. -/
meta constant skip_info (p : parser α) : parser α
/-- Set goal info position of content parsed by `p` to current position. Nested calls take precedence. -/
meta constant set_goal_info_pos (p : parser α) : parser α

/-- Return the current parser position without consuming any input. -/
meta def cur_pos : parser pos :=
parser_state.cur_pos <$> get

/-- Temporarily replace input of the parser state, run `p`, and return remaining input. -/
meta constant with_input (p : parser α) (input : string) : parser (α × string)

/-- Parse a top-level command. -/
meta constant command_like : parser unit

meta def parser_orelse (p₁ p₂ : parser α) : parser α :=
do s ← get,
   let pos₁ := s.cur_pos,
   catch p₁ $ λ e,
   do pos₂ ← cur_pos,
      if pos₁ ≠ pos₂ then
        throw e
      else put s >> p₂

meta instance : alternative parser :=
{ failure := @interaction_monad.failed _,
  orelse  := @parser_orelse,
  ..interaction_monad.monad }


-- TODO: move
meta def {u v} many {f : Type u → Type v} [monad f] [alternative f] {a : Type u} : f a → f (list a)
| x := (do y ← x,
           ys ← many x,
           return $ y::ys) <|> pure list.nil

local postfix `?`:100 := optional
local postfix `*`:100 := many

meta def sep_by : parser unit → parser α → parser (list α)
| s p := (list.cons <$> p <*> (s *> p)*) <|> return []

meta def tactic_to_parser (t : tactic α) : parser α :=
do s ← get,
   match t.run (tactic_state.mk_empty s.env s.options) with
   | (except.ok a, ts) := set_env ts.env >> pure a
   | (except.error e, _) := throw e
   end

meta instance : has_coe (tactic α) (parser α) :=
⟨tactic_to_parser⟩

end parser
end lean
