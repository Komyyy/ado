/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent

public section

variable {R} (A) {L M}
variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open Function Module TensorProduct LieSubmodule

namespace LieSubmodule

variable (R L M) in
lemma baseChange_injective [FaithfullyFlat R A] :
    Injective (baseChange A : LieSubmodule R L M → LieSubmodule A (A ⊗[R] L) (A ⊗[R] M)) := by
  intro x₁ x₂ hx
  rwa [← toSubmodule_inj, coe_baseChange, coe_baseChange, Submodule.baseChange_inj,
    toSubmodule_inj] at hx

variable {A} in
@[simp]
lemma baseChange_inj [FaithfullyFlat R A] (I J : LieSubmodule R L M) :
    baseChange A I = baseChange A J ↔ I = J :=
  baseChange_injective R A L M |>.eq_iff

end LieSubmodule

namespace LieIdeal

variable (M) in
@[simp]
lemma lcs_baseChange (I : LieIdeal R L) (n : ℕ) :
    lcs (baseChange A I) (A ⊗[R] M) n = baseChange A (lcs I M n) := by
  induction n with
  | zero => simp
  | succ n hn => simp [hn, lie_baseChange]

end LieIdeal
