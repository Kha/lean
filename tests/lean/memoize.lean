meta instance memo : monad_interactive_tactic empty tactic :=
{ memoize := λ _ h t, tactic.trace h >> t >> pure (), ..tactic.monad_interactive_tactic }

example : ℕ → ℕ → ℕ → true :=
begin
  intro,
  intro,
  intro x,
  trivial
end
