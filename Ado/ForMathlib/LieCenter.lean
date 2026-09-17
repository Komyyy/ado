/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieHom
public import Mathlib.Algebra.Lie.Abelian

public section

open Function LieIdeal

variable {R : Type*} [CommRing R]
variable {L L₂ : Type*} [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

namespace LieAlgebra

@[simp]
lemma comap_equiv_center (e : L ≃ₗ⁅R⁆ L₂) : comap e (center R L₂) = center R L := by
  ext; simp [e.surjective.forall, ← e.map_lie]

@[simp]
lemma map_equiv_center (e : L ≃ₗ⁅R⁆ L₂) : map e (center R L) = center R L₂ := by
  simp [LieEquiv.map_equiv_eq_comap_symm]

end LieAlgebra
