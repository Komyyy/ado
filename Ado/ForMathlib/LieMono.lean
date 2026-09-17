/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Submodule

public section LieMono

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]

namespace LieSubmodule

@[gcongr]
lemma toSubmodule_mono {N N' : LieSubmodule R L M} (h : N ≤ N') : (N : Submodule R M) ≤ N' :=
  (LieSubmodule.toSubmodule_le_toSubmodule _ _).mp h

end LieSubmodule
