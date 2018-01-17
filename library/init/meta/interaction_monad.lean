/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.function init.data.option.basic init.util
import init.category.combinators init.category.except init.category.state init.category.alternative init.category.monad_fail
import init.data.nat.div init.meta.format init.meta.environment
import init.meta.pexpr init.data.repr init.data.string.basic init.data.to_string

universes u v

meta def interaction_monad_error :=
(unit → format) × option pos

meta def interaction_monad_error.clamp_pos {m : Type u → Type v} [monad_except interaction_monad_error m] {α : Type u} (line0 line col : ℕ) (x : m α) : m α :=
catch x $ λ e,
  match e with
  | (msg, some p) := throw (msg, some $ if p.line < line0 then ⟨line, col⟩ else p)
  | (msg, none)   := throw (msg, (some ⟨line, col⟩))
  end

section
variables {st : Type} {α : Type}
variables [has_to_string α]

/-meta def interaction_monad.result_to_string : result state α → string
| (success a s)              := to_string a
| (exception (some t) ref s) := "Exception: " ++ to_string (t ())
| (exception none ref s)     := "[silent exception]"

meta instance interaction_monad.result_has_string : has_to_string (result state α) :=
⟨interaction_monad.result_to_string⟩-/
end

@[irreducible] meta def interaction_monad (st : Type) :=
except_t interaction_monad_error $ state st

def infer_instance {α : Type u} [i : α] : α := i

namespace interaction_monad
section
parameter {st : Type}
variables {α : Type} {β : Type u}
local notation `m` := interaction_monad st

section
local attribute [reducible] interaction_monad
meta instance : monad m := infer_instance
meta instance : monad_run _ m := infer_instance
meta instance : monad_except _ m := infer_instance
meta instance : monad_state_lift _ _ m := infer_instance
meta instance : has_scope_impure m := infer_instance
end

meta def run := monad_run.run

meta def mk_exception [has_to_format β] (msg : β) (ref : option expr) : m α :=
throw ((λ _, to_fmt msg), none)

meta def fail [has_to_format β] (msg : β) : m α :=
interaction_monad.mk_exception msg none

meta def failed {α : Type} : m α :=
interaction_monad.fail "failed"

meta def orelse (t₁ t₂ : m α) : m α :=
do s ← get,
   catch t₁ $ λ _, put s >> t₂

/- Alternative orelse operator that allows to select which exception should be used.
   The default is to use the first exception since the standard `orelse` uses the second. -/
meta def orelse' (t₁ t₂ : m α) (use_first_ex := tt) : m α :=
do s ← get,
   catch t₁ $ λ e₁,
   do s₁ ← get,
      put s,
      catch t₂ $ λ e₂, if use_first_ex then put s₁ >> throw e₁ else throw e₂

meta instance : monad_fail m :=
{ fail := λ α s, interaction_monad.fail (to_fmt s), ..interaction_monad.monad }
end
end interaction_monad
