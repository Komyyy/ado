/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.Fitting
public import Ado.ForMathlib.LieModuleHom

public section

open Set

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [IsArtinian R M] [IsNoetherian R M]

namespace LieModuleHom

lemma fitting_explicit (f : M →ₗ⁅R,L⁆ M) :
    letI N₀ := ⨆ n : ℕ, ker (f ^ n); letI N₁ := ⨅ n : ℕ, range (f ^ n)
    IsCompl N₀ N₁ ∧
      (∃ (hN₀ : MapsTo f N₀ N₀), IsNilpotent (restrict f hN₀.imp)) ∧ BijOn f N₁ N₁ := by
  have h := f.toLinearMap.fitting_explicit
  norm_cast at h
  convert h
  simp only [← isNilpotent_toLinearMap, restrict_toLinearMap]
  -- ここ狂気、`LinearMap.restrict` の依存型地獄
  constructor <;> intro h <;> refine Module.End.isNilpotent_restrict_of_le ?_ h <;> simp

theorem fitting (f : M →ₗ⁅R,L⁆ M) : ∃ (N₀ N₁ : LieSubmodule R L M), IsCompl N₀ N₁ ∧
    (∃ (hN₀ : MapsTo f N₀ N₀), IsNilpotent (restrict f hN₀.imp)) ∧ BijOn f N₁ N₁ :=
  ⟨⨆ n : ℕ, ker (f ^ n), ⨅ n : ℕ, range (f ^ n), f.fitting_explicit⟩

end LieModuleHom
