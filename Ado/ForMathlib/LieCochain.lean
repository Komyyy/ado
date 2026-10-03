/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Cochain

public section

variable {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

namespace LieModule.Cohomology

@[simp]
lemma twoCochain_mk_apply (f hf x) : (⟨f, hf⟩ : twoCochain R L M) x = f x :=
  rfl

end LieModule.Cohomology
