@[reducible] meta def mytac :=
state_t (name_map nat) tactic

meta instance (α : Type) : has_coe (tactic α) (mytac α) :=
⟨monad_lift⟩

namespace mytac

meta def step {α : Type} (t : mytac α) : mytac unit :=
t >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (t : mytac α) : mytac unit :=
catch (scope_impure (λ β, @scope_trace _ line col) (step t)) $ λ e,
  do v ← get,
     s ← tactic.get,
     let msg := λ _ : unit, e.msg () ++ format.line ++ to_fmt "value: " ++ to_fmt v ++ format.line ++ to_fmt "state:" ++ format.line ++ s.to_format,
     throw { msg := msg, ..e }

meta def execute (tac : mytac unit) : tactic unit :=
tac.run (name_map.mk nat) >> return ()

meta def save_info (p : pos) : mytac unit :=
do v ← get,
   s ← tactic.get,
   tactic.save_info_thunk p
      (λ _, to_fmt "Custom state: " ++ to_fmt v ++ format.line ++
                tactic_state.to_format s)

namespace interactive
meta def intros : mytac unit :=
tactic.intros >> return ()

meta def constructor : mytac unit :=
tactic.constructor >> return ()

meta def trace (s : string) : mytac unit :=
tactic.trace s

meta def assumption : mytac unit :=
tactic.assumption

open lean.parser
open interactive
open interactive.types

meta def add (n : parse ident) (v : nat) : mytac punit :=
modify (λ m, m.insert n v)

end interactive
end mytac

lemma ex₁ (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  add x 10,
  trace "test",
--^ "command": "info"
  constructor,
  add y 20,
  assumption,
--^ "command": "info"
  assumption
end

#print ex₁

lemma ex₂ (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  add x 10,
  trace "test",
  constructor,
  add y 20,
  assumption,
--^ "command": "info"
  assumption
end

#print ex₂
