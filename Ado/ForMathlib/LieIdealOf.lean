/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Ideal

@[expose] public section

open LieIdeal

namespace LieIdeal

def lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (p q : LieIdeal R L) :
    LieIdeal R q :=
  comap (incl q) p

@[simp]
lemma comap_incl {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (p q : LieIdeal R L) :
    comap (incl q) p = lieIdealOf p q :=
  rfl

@[simp]
lemma mem_lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} {x} : x ∈ lieIdealOf p q ↔ (x : L) ∈ p :=
  Iff.rfl

@[simps]
def lieIdealOfEquivOfLe {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} (h : p ≤ q) : lieIdealOf p q ≃ₗ⁅R⁆ p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, h x.2⟩, x.2⟩
  map_add' x y := rfl
  map_smul' x y := rfl
  map_lie' {x y} := rfl

end LieIdeal
