structure foo :=
(a b : ℕ := 2)

structure bar :=
(foo : foo)
(c : ℕ)

example (b : bar) : b.foo = {c := 2, ..b}.foo := rfl
