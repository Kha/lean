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

meta structure interaction_monad_error :=
(msg : unit → format)
(pos : option pos)

meta def interaction_monad_error.clamp_pos {m α} [monad_except interaction_monad_error m] (line0 line col : ℕ) (x : m α) : m α :=
catch x $ λ e,
  match e.pos with
  | some p := throw { pos := some $ if p.line < line0 then ⟨line, col⟩ else p, ..e }
  | none   := throw { pos := some ⟨line, col⟩, ..e }
  end

@[irreducible] meta def interaction_monad (st : Type) :=
state_t st $ except_t interaction_monad_error id

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
end
end interaction_monad
