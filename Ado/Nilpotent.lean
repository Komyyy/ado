/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set
open Module
open scoped Pointwise

namespace LieAlgebra

universe u

variable {K : Type u} {𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]
variable [LieRing.IsNilpotent 𝔤]

-- TODO: 後でインスタンスにする
attribute [local instance 100] LieRing.ofAssociativeRing

public theorem ado_of_isNilpotent :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : 𝔤 →ₗ⁅K⁆ End K V), Injective ρ ∧ ∃ k : ℕ, Set.range ρ ^ k = {0} := by
  -- まず最初に宇宙の階層を下げる (大変すぎ！ `equiv_rw` 復刻して欲しい！)
  rsuffices ⟨V, _, _, _, ρ, hρi, hρz⟩ :
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (ρ : 𝔤 →ₗ⁅K⁆ End K (𝔤 × V)), Injective ρ ∧ ∃ k : ℕ, Set.range ρ ^ k = {0}
  · haveI : Small.{u} 𝔤 := Module.Finite.small K 𝔤
    existsi Shrink.{u} 𝔤 × V, by infer_instance, by infer_instance, by infer_instance
    existsi ((Shrink.linearEquiv K 𝔤).symm.prodCongr (LinearEquiv.refl K V)).conjAlgEquiv K
      |>.toLieEquiv.toLieHom.comp ρ
    constructor
    · simp [hρi]
    · conv =>
        enter [1, k]
        conv =>
          lhs
          rw [LieHom.coe_comp, LieEquiv.coe_coe, range_comp]
          -- ここ補題にしたい
          conv => enter [1, 1]; ext x; rw [AlgEquiv.toLieEquiv_apply]
          rw [← image_pow]
          conv => enter [1]; rw [← AlgEquiv.coe_toEquiv]
        rw [← Equiv.eq_preimage_iff_image_eq, ← Equiv.image_symm_eq_preimage]
      simp [hρz]
  -- 次に、直積表現を使って単射性条件を中心に弱める。
  rsuffices ⟨V, _, _, _, ρ, hρi, hρz⟩ :
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (ρ : 𝔤 →ₗ⁅K⁆ End K V), InjOn ρ (center K 𝔤) ∧ ∃ k : ℕ, Set.range ρ ^ k = {0}
  · existsi V, by infer_instance, by infer_instance, by infer_instance
    existsi (LinearMap.prodMapAlgHom K 𝔤 V).toLieHom.comp (LieHom.prod (ad K 𝔤) ρ)
    simp only [LieHom.coe_comp, AlgHom.coe_toLieHom, LieHom.coe_prod]
    conv =>
      enter [1]
      tactic =>
        rw [Injective.of_comp_iff ?_]
        rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
        simp [DFunLike.ext_iff, forall_and]
    conv =>
      enter [2, 1, k]
      conv =>
        rw [range_comp, ← image_pow]
        tactic =>
          rw [← Set.Nonempty.subset_singleton_iff ?_]
          -- `Set.Nonempty.pow` を改良したら `simp` で一発
          exact image_nonempty.mpr <| Set.Nonempty.pow <| range_nonempty _
      conv =>
        rw [image_subset_iff]
        rhs
        equals {0} => ext ⟨x₁, x₂⟩; simp [DFunLike.ext_iff, forall_and]
      conv =>
        tactic =>
          rw [Set.Nonempty.subset_singleton_iff ?_]
          exact Set.Nonempty.pow <| range_nonempty _
    sorry
  sorry

end LieAlgebra
