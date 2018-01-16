/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.category.except init.meta.format init.util
/-
Remark: we use a function that produces a format object as the exception information.
Motivation: the formatting object may be big, and we may create it on demand.
-/
@[reducible] meta def exceptional (α : Type) := except (options → format) α

section
variables {α : Type}
variables [has_to_string α]

protected meta def exceptional.to_string : exceptional α → string
| (except.ok a)    := to_string a
| (except.error e) := "Exception: " ++ to_string (e options.mk)

meta instance : has_to_string (exceptional α) :=
has_to_string.mk exceptional.to_string
end

namespace exceptional
variables {α β : Type}

@[inline] meta def fail (f : format) : exceptional α :=
except.error (λ u, f)
end exceptional
