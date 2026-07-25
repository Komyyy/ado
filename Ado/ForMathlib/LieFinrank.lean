/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Ado.ForMathlib.LieIdealOf
public import Ado.ForMathlib.ModuleRank

@[expose] public section

open Function Module LieIdeal

universe u

@[congr]
lemma LieSubalgebra.finrank_congr {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieSubalgebra R L} (h : p = q) : finrank R p = finrank R q :=
  (LieEquiv.ofEq p q (by simp [h])).toLinearEquiv.finrank_eq

namespace LieIdeal

@[congr]
lemma finrank_congr {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} (h : p = q) : finrank R p = finrank R q :=
  (LieEquiv.ofEq p.toLieSubalgebra q.toLieSubalgebra (by simp [h])).toLinearEquiv.finrank_eq

@[simp]
lemma finrank_toLieSubalgebra {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R p.toLieSubalgebra = finrank R p :=
  rfl

@[simp]
lemma finrank_toSubmodule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R p.toSubmodule = finrank R p :=
  rfl

lemma finrank_lt_iff {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    {p : LieIdeal K L} :
    finrank K p < finrank K L ↔ p < ⊤ := by
  simpa [lt_top_iff_ne_top] using p.toSubmodule.finrank_lt_iff

@[simp]
lemma finrank_top {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] :
    finrank R (⊤ : LieIdeal R L) = finrank R L :=
  _root_.finrank_top R L

@[simp]
lemma finrank_lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p q : LieIdeal R L) (h : p ≤ q) : finrank R (lieIdealOf p q) = finrank R p :=
  (lieIdealOfEquivOfLe h).toLinearEquiv.finrank_eq

@[simp]
lemma finrank_quotient_toSubmodule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R (L ⧸ p.toSubmodule) = finrank R (L ⧸ p) :=
  rfl

@[simp]
lemma finrank_quotient {R : Type*} {L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Nontrivial R] [HasRankNullity.{u} R] [Module.Finite R L] (p : LieIdeal R L) :
    finrank R (L ⧸ p) = finrank R L - finrank R p := by
  simpa using p.toSubmodule.finrank_quotient (R := R)

@[simp]
lemma finrank_le {R : Type*} {L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Nontrivial R] [HasRankNullity.{u} R] [Module.Finite R L] (p : LieIdeal R L) :
    finrank R p ≤ finrank R L :=
  p.toSubmodule.finrank_le

end LieIdeal

namespace LieHom

lemma finrank_range_add_finrank_ker {K L L₂ : Type*} [Field K]
    [LieRing L] [LieAlgebra K L] [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L]
    (f : L →ₗ⁅K⁆ L₂) : Module.finrank K f.range + Module.finrank K f.ker = Module.finrank K L :=
  f.toLinearMap.finrank_range_add_finrank_ker

lemma finrank_idealRange_add_finrank_ker {K L L₂ : Type*} [Field K]
    [LieRing L] [LieAlgebra K L] [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L]
    (f : L →ₗ⁅K⁆ L₂) (hf : IsIdealMorphism f) :
    Module.finrank K f.idealRange + Module.finrank K f.ker = Module.finrank K L := by
  convert f.finrank_range_add_finrank_ker using 2; simp [← hf.eq]

end LieHom
