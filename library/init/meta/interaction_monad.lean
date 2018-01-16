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

meta structure interaction_monad_error (st : Type) :=
(msg : unit → format)
(pos : option pos)
(state : st)

meta def interaction_monad_error.clamp_pos {m st α} [monad_except (interaction_monad_error st) m] (line0 line col : ℕ) (x : m α) : m α :=
catch x $ λ e,
  match e.pos with
  | some p := throw { pos := some $ if p.line < line0 then ⟨line, col⟩ else p, ..e }
  | none   := throw { pos := some ⟨line, col⟩, ..e }
  end

@[irreducible] meta def interaction_monad (st : Type) :=
state_t st $ except_t (interaction_monad_error st) id

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

meta def run := interaction_monad.monad_run.run

meta def mk_exception [has_to_format β] (msg : β) (ref : option expr) : m α :=
do s ← get, throw ⟨(λ _, to_fmt msg), none, s⟩

meta def fail [has_to_format β] (msg : β) : m α :=
interaction_monad.mk_exception msg none

meta def failed {α : Type} : m α :=
interaction_monad.fail "failed"

meta instance : monad_fail m :=
{ fail := λ α s, interaction_monad.fail (to_fmt s), ..interaction_monad.monad }
end
end interaction_monad
