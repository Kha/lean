/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.interactive
import init.category.lawful

namespace native

inductive result (E : Type) (R : Type) : Type
| err {} : E → result
| ok {} : R → result

def unwrap_or {E T : Type} : result E T → T → T
| (result.err _) default := default
| (result.ok t) _ := t

def result.and_then {E T U : Type} : result E T → (T → result E U) → result E U
| (result.err e) _ := result.err e
| (result.ok t) f := f t

local attribute [simp] result.and_then
instance (E : Type) : monad (result E) :=
{ pure := @result.ok E, bind := @result.and_then E }

instance (E : Type) : is_lawful_monad (result E) :=
{ id_map := by intros; cases x; simp [has_map.map]; refl,
  pure_bind := by intros; apply rfl,
  bind_assoc := by intros; cases x; simp [has_map.map, bind] }

inductive resultT (M : Type → Type) (E : Type) (A : Type) : Type
| run : M (result E A) → resultT

namespace resultT
  variable {M : Type → Type}

  protected def pure [monad : monad M] {E A : Type} (x : A) : resultT M E A :=
    resultT.run $ pure (result.ok x)

  protected def and_then [monad : monad M] {E A B : Type} : resultT M E A → (A → resultT M E B) → resultT M E B
  | (resultT.run action) f := resultT.run (do
  res_a ← action,
  -- a little ugly with this match
  match res_a with
  | result.err e := pure (result.err e)
  | result.ok a := let (resultT.run actionB) := f a in actionB
  end)

  local attribute [simp] resultT.and_then bind_pure pure_bind

  instance [m : monad M] (E : Type) : monad (resultT M E) :=
  {pure := @resultT.pure M m E, bind := @resultT.and_then M m E}

  instance [monad M] [is_lawful_monad M] (E : Type) : is_lawful_monad (resultT M E) :=
  { id_map := begin
      intros, cases x,
      rw resultT.monad,
      simp [function.comp],
      have : @resultT.and_then._match_1 M _ E α _ resultT.pure = pure,
      { funext x,
        cases x; simp [resultT.pure] },
      simp [this]
    end,
    pure_bind := begin
      intros,
      simp [bind, pure, has_pure.pure, resultT.pure],
      cases f x,
      simp [resultT.and_then]
    end,
    bind_assoc := begin
      intros,
      cases x, simp [bind],
      rw [bind_assoc],
      apply congr_arg, funext,
      cases x with e a; simp,
      { cases f a, refl },
    end }
end resultT

end native
