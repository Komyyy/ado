/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Solvable

public section

namespace LieAlgebra

variable {R L} [CommRing R] [LieRing L] [LieAlgebra R L]

variable (R) in
@[simp]
lemma isSolvable_derivedSeries_iff (n : ℕ) : IsSolvable (derivedSeries R L n) ↔ IsSolvable L where
  mpr _ := inferInstance
  mp h := by
    simp only [isSolvable_iff R, LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap,
      LieIdeal.comap_incl_eq_bot, disjoint_iff, ← derivedSeriesOfIdeal_add,
      inf_eq_right.mpr, derivedSeriesOfIdeal_le, le_refl, le_add_self] at h ⊢
    exact h.imp' (· + n) (fun _ h ↦ h)

end LieAlgebra
