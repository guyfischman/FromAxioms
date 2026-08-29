/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import FromAxioms.SetTheory.ZFSet

/-! # Dependent choice down a binary tree

Dependent choice down a binary tree, at set level and at type level. -/

namespace SetTheory

-- A hypothesis naming an unimported principle is auto-bound as a variable, so the
-- statement constrains nothing and still elaborates. This file declares its own
-- universe, which is the only thing the tower relies on auto-binding for.
set_option autoImplicit false

universe u

/-- The two-element set of digits. -/
def two : ZFSet.{u} := pair empty.{u} (succ empty.{u})

end SetTheory

namespace ZFSet
export SetTheory (two)
end ZFSet
