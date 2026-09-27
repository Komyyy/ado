/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Solvable

public section

open LieAlgebra

variable {R L} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simp]
lemma LieIdeal.isSolvable_derivedSeriesOfIdeal_iff (I : LieIdeal R L) (n : ℕ) :
    IsSolvable (derivedSeriesOfIdeal R L n I) ↔ IsSolvable I where
  mpr := le_solvable_ideal_solvable (derivedSeriesOfIdeal_le_self I n)
  mp h := by
    simp only [isSolvable_iff R, LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap,
      LieIdeal.comap_incl_eq_bot, disjoint_iff, ← derivedSeriesOfIdeal_add,
      inf_eq_right.mpr, derivedSeriesOfIdeal_le, le_refl, le_add_self,
      derivedSeriesOfIdeal_le_self] at h ⊢
    exact h.imp' (· + n) (fun _ h ↦ h)

variable (R L) in
@[simp]
lemma LieIdeal.isSolvable_top_iff : IsSolvable (⊤ : LieIdeal R L) ↔ IsSolvable L :=
  solvable_iff_equiv_solvable LieIdeal.topEquiv

variable (R) in
lemma LieAlgebra.isSolvable_derivedSeries_iff (n : ℕ) :
    IsSolvable (derivedSeries R L n) ↔ IsSolvable L := by
  simp
