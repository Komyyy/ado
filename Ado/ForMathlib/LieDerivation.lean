/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Ideal

@[expose] public section

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

namespace LieDerivation

@[simps ! apply_apply]
def adIdeal (I : LieIdeal R L) : L →ₗ⁅R⁆ LieDerivation R I I where
  toFun x :=
    { toLinearMap := LieModule.toEnd R L I x
      leibniz' y z := by
        conv => equals ⁅x, ⁅y.1, z.1⁆⁆ = ⁅y.1, ⁅x, z.1⁆⁆ - ⁅z.1, ⁅x, y.1⁆⁆ =>
          simp [Subtype.ext_iff]
        grind only [= lie_lie, =_ lie_skew] }
  map_add' x y := by ext; simp
  map_smul' t x := by ext; simp
  map_lie' {x y} := by ext; simp

@[simps !]
def compCodomain (D : LieDerivation R L M) (f : M →ₗ⁅R,L⁆ M₂) : LieDerivation R L M₂ where
  toLinearMap := f.toLinearMap ∘ₗ D.toLinearMap
  leibniz' x y := by simp

end LieDerivation
