/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent

@[expose] public section

open Function

namespace LieIdeal.Quotient

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simps]
def mk' (s : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ s :=
  { s.toSubmodule.mkQ with
    toFun := LieSubmodule.Quotient.mk
    map_lie' {_ _} := rfl }

@[simp]
theorem surjective_mk' (s : LieIdeal R L) : Surjective (mk' s) :=
  Quot.mk_surjective

@[simp]
theorem mk'_ker (s : LieIdeal R L) : (mk' s).ker = s := by
  ext; simp

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing.IsNilpotent L] (s : LieIdeal R L) : LieRing.IsNilpotent (L ⧸ s) :=
  (LieIdeal.Quotient.surjective_mk' s).lieAlgebra_isNilpotent

end LieIdeal.Quotient
