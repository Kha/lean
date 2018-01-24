@[reducible] meta def mytac :=
state_t nat tactic

meta instance (α : Type) : has_coe (tactic α) (mytac α) :=
⟨monad_lift⟩

meta instance : monad_tactic mytac := {}

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
tac.run 0 >> return ()

meta def save_info (p : pos) : mytac unit :=
do v ← get,
   s ← tactic.get,
   tactic.save_info_thunk p
      (λ _, to_fmt "Custom state: " ++ to_fmt v ++ format.line ++
                tactic_state.to_format s)

meta instance : monad_interactive_tactic empty mytac :=
{ type_name := `mytac, istep := @istep, save_info := @save_info,
  execute := λ cfg, execute, ..mytac.monad_tactic }

namespace interactive
meta def intros : mytac unit :=
tactic.intros >> return ()

meta def constructor : mytac unit :=
tactic.constructor >> return ()

meta def trace (s : string) : mytac unit :=
tactic.trace s

meta def assumption : mytac unit :=
tactic.assumption

meta def inc : mytac punit :=
modify (+1)

end interactive
end mytac

example (p q : Prop) : p → q → p ∧ q :=
begin [mytac]
  intros,
  inc,
  trace "test",
  constructor,
  inc,
  assumption,
  assumption
end
