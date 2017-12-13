local infixr ` $> `:100  := λ a b, b <$ a
example (m : Type → Type) [monad m] : m ℕ := pure 0 $> 1
