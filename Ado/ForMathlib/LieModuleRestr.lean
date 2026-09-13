/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Submodule

public section

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

namespace LieSubmodule

@[simp]
lemma restr_top (L' : LieSubalgebra R L) : restr (⊤ : LieSubmodule R L M) L' = ⊤ := by
  simp [← toSubmodule_inj]

@[simp]
lemma restr_bot (L' : LieSubalgebra R L) : restr (⊥ : LieSubmodule R L M) L' = ⊥ := by
  simp [← toSubmodule_inj]

end LieSubmodule
