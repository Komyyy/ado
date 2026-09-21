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
variable {K L : Type*} [LieRing L] [LieAlgebra R L]

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

end LieDerivation
