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

section ForMathlib

section LieTransferInstance

-- ここらへん全部不要になった、どんまい

-- TODO: 今見たけど `Function.Injective.addCommGroup` はまだ `NSMul` じゃなく `SMul ℕ` を使ってた
--       修正した方がいいかも ついでに `abbrev (reducible)` から `instance_reducible` にした方がいい

variable (R : Type*) {L₁ L₂ : Type*}

@[instance_reducible]
protected def Function.Injective.lieRing
    [Add L₁] [Zero L₁] [SMul ℕ L₁] [Neg L₁] [Sub L₁] [SMul ℤ L₁] [Bracket L₁ L₁] [LieRing L₂]
    (f : L₁ → L₂) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (bracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) : LieRing L₁ where
  __ := hf.addCommGroup f zero add neg sub nsmul zsmul
  add_lie x y z := hf <| by simp [*]
  lie_add x y z := hf <| by simp [*]
  lie_self x := hf <| by simp [*]
  leibniz_lie x y z := hf <| by simp [*]

@[instance_reducible]
protected def Function.Injective.lieAlgebra
    [CommRing R] [LieRing L₁] [SMul R L₁] [LieRing L₂] [LieAlgebra R L₂]
    (f : L₁ →+ L₂) (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x)
    (bracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) : LieAlgebra R L₁ where
  __ := hf.module R f smul
  lie_smul t x y := hf <| by simp [*]

@[instance_reducible]
protected def Equiv.bracketSelf (e : L₁ ≃ L₂) [Bracket L₂ L₂] : Bracket L₁ L₁ where
  bracket x y := e.invFun ⁅e.toFun x, e.toFun y⁆

@[instance_reducible]
protected def Equiv.lieRing (e : L₁ ≃ L₂) [LieRing L₂] : LieRing L₁ := by
  let add := e.add
  let zero := e.zero
  let nsmul := e.smul ℕ
  let neg := e.Neg
  let sub := e.sub
  let zsmul := e.smul ℤ
  let bracket := e.bracketSelf
  apply e.injective.lieRing _ <;> intros <;> exact e.apply_symm_apply _

@[instance_reducible]
protected def Equiv.lieAlgebra (e : L₁ ≃ L₂) [CommRing R] [LieRing L₂]
    [LieAlgebra R L₂] : by
    let := e.lieRing
    exact LieAlgebra R L₁ := by
  let := e.lieRing
  let smul := e.smul R
  let bracket := e.bracketSelf
  refine e.injective.lieAlgebra R ⟨⟨e, ?_⟩, ?_⟩ ?_ ?_ <;> intros <;> exact e.apply_symm_apply _

def Equiv.lieEquiv (e : L₁ ≃ L₂) [CommRing R] [LieRing L₂]
    [LieAlgebra R L₂] : by
    let := e.lieRing
    let := e.lieAlgebra R
    exact L₁ ≃ₗ⁅R⁆ L₂ := by
  intros
  exact
    { e.linearEquiv R with
      map_lie' {x y} := e.symm.injective <| by
        simp [Equiv.linearEquiv, show ⁅x, y⁆ = e.symm ⁅e x, e y⁆ from rfl] }

-- これ自動で生成できるようにならないかな

end LieTransferInstance

noncomputable section LieShrink

namespace Shrink

universe u

variable (R L : Type*) [Small.{u} L]

instance [LieRing L] : LieRing (Shrink.{u} L) :=
  (equivShrink L).symm.lieRing

instance [CommRing R] [LieRing L] [LieAlgebra R L] :
    LieAlgebra R (Shrink.{u} L) :=
  (equivShrink L).symm.lieAlgebra R

def lieEquiv [CommRing R] [LieRing L] [LieAlgebra R L] : Shrink.{u} L ≃ₗ⁅R⁆ L :=
  (equivShrink L).symm.lieEquiv R

end Shrink

end LieShrink

end ForMathlib

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
