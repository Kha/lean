import standard

example : ∃(b : nat), b = 1 ∧ 0 ≤ b :=
begin
  apply exists.intro,
  apply and.intro,
  apply rfl,
  generalize : 1 = z,
  apply nat.zero_le
end
