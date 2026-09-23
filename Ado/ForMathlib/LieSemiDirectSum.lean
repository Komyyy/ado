/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieDerivation
public import Mathlib.Algebra.Lie.SemiDirect
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section LieSemiDirectSum

-- TODO: `SemidirectProduct` と同様に、`SemidirectSum` に変名

variable {R : Type*} [CommRing R]
variable {K : Type*} [LieRing K] [LieAlgebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {L₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]
variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

open LieHom LieSubalgebra LieDerivation

namespace LieAlgebra

namespace SemiDirectSum

@[simp]
lemma isIdealMorphism_inl : IsIdealMorphism (inl ψ) := by
  simp [isIdealMorphism_iff]

instance [Module.Finite R K] [Module.Finite R L] : Module.Finite R (K ⋊⁅ψ⁆ L) :=
  Module.Finite.equiv (toProdl ψ).symm

def equivIdealRangeInl : K ≃ₗ⁅R⁆ idealRange (inl ψ) where
  toLieHom :=
    comp (LieEquiv.ofEq (range (inl ψ)) (idealRange (inl ψ)) (by ext; simp)).toLieHom
      (rangeRestrict (inl ψ))
  invFun x := x.1.left
  right_inv := by
    rintro ⟨x, hx⟩
    simp only [isIdealMorphism_inl, mem_idealRange_iff, inl_eq_mk] at hx
    obtain ⟨x, rfl⟩ := hx
    rfl

@[simp]
lemma equivIdealRangeInl_apply_coe (x) : (equivIdealRangeInl ψ x).1 = inl ψ x :=
  rfl

@[simp]
lemma incl_idealRange_inl_equivIdealRangeInl :
    LieHom.comp (LieIdeal.incl (idealRange (inl ψ))) (equivIdealRangeInl ψ).toLieHom = inl ψ := by
  ext : 1; simp

@[simp]
lemma equivIdealRangeInl_symm_apply (x) : (equivIdealRangeInl ψ).symm x = x.1.left :=
  rfl

def equivRangeInr : L ≃ₗ⁅R⁆ LieHom.range (inr ψ) where
  toLieHom := rangeRestrict (inr ψ)
  invFun x := x.1.right
  right_inv := by
    rintro ⟨x, hx⟩
    simp only [LieHom.mem_range, inr_eq_mk] at hx
    obtain ⟨x, rfl⟩ := hx
    rfl

@[simp]
lemma equivRangeInr_apply_coe (x) : (equivRangeInr ψ x).1 = inr ψ x :=
  rfl

@[simp]
lemma equivRangeInr_symm_apply (x) : (equivRangeInr ψ).symm x = x.1.right :=
  rfl

lemma inr_lie_inl (x y) : ⁅inr ψ x, inl ψ y⁆ = inl ψ (ψ x y) := by
  simp

lemma inl_lie_inr (x y) : ⁅inl ψ x, inr ψ y⁆ = -inl ψ (ψ y x) := by
  simp

@[simps !]
def lift (f : K →ₗ⁅R⁆ L₂) (g : L →ₗ⁅R⁆ L₂)
    (h : ∀ (x : L), f.toLinearMap ∘ₗ (ψ x).toLinearMap = ad R L₂ (g x) ∘ₗ f.toLinearMap) :
    (K ⋊⁅ψ⁆ L) →ₗ⁅R⁆ L₂ where
  toLinearMap := LinearMap.coprod f g ∘ₗ (toProdl ψ).toLinearMap
  map_lie' {x y} := by
    convert_to ∀ (x : L) (y : K), f ((ψ x) y) = ⁅g x, f y⁆ at h
    · simp [DFunLike.ext_iff]
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    convert_to ⁅f x₁, f y₁⁆ + ⁅g x₂, f y₁⁆ - ⁅g y₂, f x₁⁆ + ⁅g x₂, g y₂⁆ =
        ⁅f x₁, f y₁⁆ + ⁅g x₂, f y₁⁆ + (⁅f x₁, g y₂⁆ + ⁅g x₂, g y₂⁆) using 0
    · simp [h]
    grind [=_ lie_skew]

end SemiDirectSum

def IsInnerSemiDirectSum (I : LieIdeal R L) (L' : LieSubalgebra R L) : Prop :=
  IsCompl I.toSubmodule L'.toSubmodule

variable {I : LieIdeal R L} {L' : LieSubalgebra R L}

lemma isInnerSemiDirectSum_iff :
    IsInnerSemiDirectSum I L' ↔ IsCompl I.toSubmodule L'.toSubmodule :=
  Iff.rfl

alias ⟨IsInnerSemiDirectSum.isCompl, _root_.IsCompl.isInnerSemidirectSum⟩ :=
  isInnerSemiDirectSum_iff

namespace SemiDirectSum

noncomputable def lieEquivLieSubalgebra (h : IsInnerSemiDirectSum I L') :
    (I ⋊⁅comp (adIdeal I) (incl L')⁆ L') ≃ₗ⁅R⁆ L where
  __ := LinearEquiv.trans (toProdl _) (Submodule.prodEquivOfIsCompl _ _ h.isCompl)
  map_lie' {x y} := by
    -- `SetLike` の defeq に対処
    have haux (x : I × L') :
        Submodule.prodEquivOfIsCompl _ _ h.isCompl x = (x.1 : L) + (x.2 : L) :=
      Submodule.coe_prodEquivOfIsCompl' ..
    conv => equals
        ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ -
          ⁅y.right.1, x.left.1⁆ + ⁅x.right.1, y.right.1⁆ =
            ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ +
              (⁅x.left.1, y.right.1⁆ + ⁅x.right.1, y.right.1⁆) =>
      -- `SetLike` の defeq に対処
      have haux (x : I × L') :
          Submodule.prodEquivOfIsCompl _ _ h.isCompl x = (x.1 : L) + (x.2 : L) :=
        Submodule.coe_prodEquivOfIsCompl' ..
      simp [haux]
    grind only [=_ lie_skew]

@[simp]
lemma lieEquivLieSubalgebra_apply (h : IsInnerSemiDirectSum I L')
    (x : I ⋊⁅comp (adIdeal I) (incl L')⁆ L') : lieEquivLieSubalgebra h x = (x.1 : L) + (x.2 : L) :=
  rfl

lemma isInnerSemiDirectSum_self : IsInnerSemiDirectSum (idealRange (inl ψ)) (range (inr ψ)) := by
  simp_rw [isInnerSemiDirectSum_iff, isCompl_iff]
  constructor
  · simp [Submodule.disjoint_def]
  · rw [Submodule.codisjoint_iff_exists_add_eq]; simp

end SemiDirectSum

end LieAlgebra
