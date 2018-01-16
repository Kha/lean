open list

meta definition e := environment.mk_std 0

definition hints := reducibility_hints.regular 10 tt

#eval environment.trust_lvl e

#eval (environment.add e (declaration.defn `foo []
                                             (expr.sort (level.succ (level.zero)))
                                             (expr.sort (level.succ (level.zero)))
                                             hints tt) : exceptional environment)

meta definition e1 := (environment.add e (declaration.defn `foo []
                                            (expr.sort (level.succ (level.zero)))
                                            (expr.sort level.zero)
                                            hints tt) : exceptional environment)

#print "-----------"
open name

#eval do
   e₁ ← environment.add e (declaration.defn `foo []
                                            (expr.sort (level.succ (level.zero)))
                                            (expr.sort level.zero)
                                            hints tt),
   e₂ ← environment.add_inductive e₁ `Two [] 0 (expr.sort (level.succ level.zero))
                                  [(`Zero, expr.const `Two []),
                                   (`One,  expr.const `Two [])] tt,
   d₁ ← environment.get e₂ `Zero,
   d₂ ← environment.get e₂ `foo,
   pure (declaration.type d₁, declaration.type d₂,
         environment.is_recursor e₂ `Two.rec,
         environment.constructors_of e₂ `Two,
         environment.fold e₂ (to_fmt "") (λ d r, r ++ format.line ++ to_fmt (declaration.to_name d)))
