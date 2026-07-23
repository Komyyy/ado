/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib
public import Ado.ForMathlib.LieModuleProd

public section

open LieHom

variable {R L M N : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [LieRingModule L M] [LieRingModule L N]
variable [LieModule R L M] [LieModule R L N]


@[simp]
lemma Prod.lieModule_ker_eq :
    LieModule.ker R L (M × N) = LieModule.ker R L M ⊓ LieModule.ker R L N := by
  ext x; simp [forall_and]

@[simp]
lemma LieSubalgebra.ker_eq (L' : LieSubalgebra R L) :
    LieModule.ker R L' M = comap L'.incl (LieModule.ker R L M) := by
  ext x; simp

@[simp]
lemma LieIdeal.ker_eq (I : LieIdeal R L) :
    LieModule.ker R I M = comap I.incl (LieModule.ker R L M) := by
  ext x; simp
