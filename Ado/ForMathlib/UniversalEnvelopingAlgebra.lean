/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Tactic.NoncommRing

public section

open LieRing LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

namespace UniversalEnvelopingAlgebra

instance : LieRingModule L (UniversalEnvelopingAlgebra R L) where
  bracket x a := ι R x * a
  add_lie x y a := by simp [add_mul]
  lie_add x a b := by simp [mul_add]
  leibniz_lie x y a := by
    simp only [ι_apply, LieHom.map_lie, of_associative_ring_bracket]; noncomm_ring

@[simp]
lemma bracket_eq (x : L) (a : UniversalEnvelopingAlgebra R L) : ⁅x, a⁆ = ι R x * a :=
  rfl

instance : LieModule R L (UniversalEnvelopingAlgebra R L) where
  smul_lie t x a := by simp
  lie_smul t x a := by simp

end UniversalEnvelopingAlgebra
