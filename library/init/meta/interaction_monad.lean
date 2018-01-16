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

meta def interaction_monad (st : Type) :=
except_t interaction_monad_error $ state st

section
parameter {st : Type}
variables {α : Type} {β : Type u}
local notation `m` := interaction_monad st

local attribute [reducible] interaction_monad
def infer_instance {α : Type u} [i : α] : α := i
meta instance interaction_monad.monad : monad m := infer_instance
meta instance interaction_monad.monad_except : monad_except interaction_monad_error m := infer_instance
meta instance interaction_monad.monad_state_lift : monad_state_lift st id m := infer_instance

meta def interaction_monad.clamp_pos (line0 line col : ℕ) (x : m α) : m α :=
⟨do a ← x.run,
    pure $ match a with
    | ok@(except.ok _)             := ok
    | (except.error (msg, some p)) := except.error (msg, some $ if p.line < line0 then ⟨line, col⟩ else p)
    | (except.error (msg, none))   := except.error (msg, (some ⟨line, col⟩))
    end⟩

meta def interaction_monad.mk_exception [has_to_format β] (msg : β) (ref : option expr) : m α :=
throw ((λ _, to_fmt msg), none)

meta def interaction_monad.fail [has_to_format β] (msg : β) : m α :=
interaction_monad.mk_exception msg none

meta def interaction_monad.failed {α : Type} : m α :=
interaction_monad.fail "failed"

meta def interaction_monad.orelse (t₁ t₂ : m α) : m α :=
⟨⟨λ s, match t₁.run.run s with
       | e₁@(except.error _, _) := t₂.run.run s
       | x := x
       end⟩⟩

/- Alternative orelse operator that allows to select which exception should be used.
   The default is to use the first exception since the standard `orelse` uses the second. -/
meta def interaction_monad.orelse' (t₁ t₂ : m α) (use_first_ex := tt) : m α :=
⟨⟨λ s, match t₁.run.run s with
       | e₁@(except.error _, _) := match t₂.run.run s with
         | e₂@(except.error _, _) := if use_first_ex then e₁ else e₂
         | x := x
         end
       | x := x
       end⟩⟩

meta instance interaction_monad.monad_fail : monad_fail m :=
{ fail := λ α s, interaction_monad.fail (to_fmt s), ..interaction_monad.monad }

-- TODO: unify `parser` and `tactic` behavior?
-- meta instance interaction_monad.alternative : alternative m :=
-- ⟨@interaction_monad_fmap, (λ α a s, success a s), (@fapp _ _), @interaction_monad.failed, @interaction_monad_orelse⟩
end
