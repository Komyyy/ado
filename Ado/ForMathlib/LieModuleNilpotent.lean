/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

open Filter Function

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

namespace LieModule

omit [LieModule R L M] in
@[gcongr]
lemma lowerCentralSeries_mono (m n : ℕ) (h : n ≤ m) :
    lowerCentralSeries R L M m ≤ lowerCentralSeries R L M n :=
  antitone_lowerCentralSeries R L M h

variable (R) in
lemma isNilpotent_iff_eventually :
    IsNilpotent L M ↔ ∀ᶠ (k : ℕ) in atTop, lowerCentralSeries R L M k = ⊥ := by
  rw [isNilpotent_iff R L M, eventually_atTop]
  congr! with k
  constructor
  case mpr => intro h; exact h k le_rfl
  intro hk n hn
  rw [eq_bot_iff] at hk ⊢
  grw [← hn, hk]

lemma isNilpotent_iff_eventually_int :
    IsNilpotent L M ↔ ∀ᶠ (k : ℕ) in atTop, lowerCentralSeries ℤ L M k = ⊥ :=
  isNilpotent_iff_eventually ℤ

lemma isNilpotent_of_lieIdeal_le_left (I₁ I₂ : LieIdeal R L) (h : I₁ ≤ I₂) [IsNilpotent I₂ M] :
    IsNilpotent I₁ M :=
  Function.Injective.lieModuleIsNilpotent (f := LieIdeal.inclusion h) (g := LinearMap.id)
    (by simp) injective_id

@[congr]
lemma isNilpotent_lieIdeal_congr_left (I₁ I₂ : LieIdeal R L) (h : I₁ = I₂) :
    IsNilpotent I₁ M ↔ IsNilpotent I₂ M where
  mp _ := isNilpotent_of_lieIdeal_le_left I₂ I₁ h.ge
  mpr _ := isNilpotent_of_lieIdeal_le_left I₁ I₂ h.le

@[simp]
theorem isNilpotent_of_top_lieIdeal_iff :
    IsNilpotent (⊤ : LieIdeal R L) M ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff LieIdeal.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

instance (I : LieIdeal R L) [IsNilpotent L M] : IsNilpotent I M :=
  Function.Injective.lieModuleIsNilpotent (f := LieIdeal.incl I) (g := LinearMap.id)
    (by simp) injective_id

end LieModule
