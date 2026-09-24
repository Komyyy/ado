/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Solvable

/-!
## 一般の場合の Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section ForMathlib

public section BilinFormDualBasis

open Module

namespace LinearMap.BilinForm

@[simp]
lemma dualBasis_reindex {K V} [Field K] [AddCommGroup V] [Module K V]
    {ι ι'} [DecidableEq ι] [DecidableEq ι'] [Finite ι] [Finite ι']
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (e : ι ≃ ι') :
    dualBasis B hB (Basis.reindex b e) = Basis.reindex (dualBasis B hB b) e := by
  ext; simp [dualBasis, LinearMap.ext_iff]

end LinearMap.BilinForm

end BilinFormDualBasis

public section Casimir

open Module LinearMap.BilinForm
open LieAlgebra hiding Basis

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [IsKilling K L]

namespace UniversalEnvelopingAlgebra

private noncomputable def casimirOfBasis {n : Type*} [Fintype n] [DecidableEq n] (B : Basis n K L) :
    UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (B i) * ι K (dualBasis (killingForm K L) (IsKilling.killingForm_nondegenerate K L) B i)

-- `dualBasis B hB (Basis.map b f)` という式が簡単に表せないため証明がこのように複雑になっている。
private lemma casimirOfBasis_eq_of_same_index {n : Type*} [Fintype n] [DecidableEq n]
    (B B' : Basis n K L) : casimirOfBasis B = casimirOfBasis B' := by
  unfold casimirOfBasis
  set DB := dualBasis (ι := n) (killingForm K L) (IsKilling.killingForm_nondegenerate K L)
  have h i : Basis.equivFun (DB B) (DB B' i) = fun j ↦ Basis.repr B' (B j) i
  · ext j : 1
    convert_to
        killingForm K L (DB B' i) (∑ i, Basis.repr B' (B j) i • B' i) = Basis.repr B' (B j) i
    · simp [DB]
    simp_rw [map_sum]
    simp [DB, apply_dualBasis_left]
  simp_rw [← LinearEquiv.eq_symm_apply, Basis.equivFun_symm_apply] at h
  simp_rw [h]
  convert_to _ = ∑ j, (∑ i, Basis.repr B' (B j) i • ι K (B' i)) * ι K (DB B j)
  · simp [Finset.mul_sum, Finset.sum_mul, iff_true_intro Finset.sum_comm, - ι_apply]
  simp_rw [← map_smul, ← map_sum, Basis.sum_repr]

private lemma casimirOfBasis_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Basis m K L) (B' : Basis n K L) : casimirOfBasis B = casimirOfBasis B' := by
  convert_to _ = casimirOfBasis (Basis.reindex B' (Basis.indexEquiv B' B))
  · simp [casimirOfBasis, ← Basis.indexEquiv B' B |>.sum_comp, - ι_apply]
  apply casimirOfBasis_eq_of_same_index

variable (K L) in
noncomputable def casimir [FiniteDimensional K L] : UniversalEnvelopingAlgebra K L :=
  casimirOfBasis (finBasis K L)

lemma casimir_eq {_ : FiniteDimensional K L} {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K L) :
    casimir K L = ∑ i, ι K (B i) *
      ι K (dualBasis (killingForm K L) (IsKilling.killingForm_nondegenerate K L) B i) :=
  casimirOfBasis_eq ..

end UniversalEnvelopingAlgebra

end Casimir

public section WeylReducibility

open Module LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubmodule

@[instance]
public axiom complementedLattice {K L V}
    [Field K] [LieRing L] [LieAlgebra K L] [IsKilling K L] [IsSemisimple K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    ComplementedLattice (LieSubmodule K L V) -- where
  -- exists_isCompl W := by
  --   let LW : Submodule K (End K V) :=
  --     { carrier := {t | LinearMap.range t ≤ W ∧ Submodule.map t W = ⊥}
  --       add_mem' := by
  --         simp_rw [Set.mem_ofPred]
  --         rintro t u ⟨ht₁, ht₂⟩ ⟨hu₁, hu₂⟩
  --         split_ands
  --         · grw [LinearMap.range_add_le, ht₁, hu₁, sup_idem]
  --         · grw [_root_.eq_bot_iff, Submodule.map_add_le, ht₂, hu₂, sup_idem]
  --       zero_mem' := by simp
  --       smul_mem' := by
  --         simp_rw [Set.mem_ofPred]
  --         rintro c t ⟨ht₁, ht₂⟩
  --         split_ands
  --         · grw [LinearMap.range_smul_le_range, ht₁]
  --         · grw [_root_.eq_bot_iff, Submodule.map_smul_le_map, ht₂] }
  --   let : LieRingModule L LW :=
  --     { bracket x t := ⟨⁅toEnd K L V x, (t : End K V)⁆, sorry⟩
  --       add_lie := sorry
  --       lie_add := sorry
  --       leibniz_lie := sorry }
  --   sorry

end LieSubmodule

end WeylReducibility

end ForMathlib

section Levi

open Function LieAlgebra

-- 正直もっと良い書き方があるかもしれないけど暫定的にこれで
public axiom LieHom.exists_levi_splitting (K 𝔤 : Type*)
    [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤] :
    ∃ (s : 𝔤 ⧸ radical K 𝔤 →ₗ⁅K⁆ 𝔤), LeftInverse LieIdeal.Quotient.mk s

end Levi

open Function LieAlgebra LieIdeal SemiDirectSum

variable {K 𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]

attribute [local instance] LieAlgebra.IsAdo.of_isSolvable_of_charZero in
public instance LieAlgebra.IsAdo.of_charZero : IsAdo K 𝔤 := by
  obtain ⟨s, hs⟩ := LieHom.exists_levi_splitting K 𝔤
  let ψ : 𝔤 ⧸ radical K 𝔤 →ₗ⁅K⁆ LieDerivation K (radical K 𝔤) (radical K 𝔤) :=
    LieHom.comp (LieDerivation.adIdeal (radical K 𝔤)) s
  let f : 𝔤 →ₗ[K] radical K 𝔤 :=
    show 𝔤 →ₗ[K] (radical K 𝔤).toSubmodule from
    LinearMap.codRestrict _ (LinearMap.id - (LieHom.comp s (LieIdeal.Quotient.mk' _)).toLinearMap)
      (by simp [← LieSubmodule.Quotient.mk_eq_zero, hs.eq])
  have hf x : (f x : 𝔤) = x - s (LieIdeal.Quotient.mk x) :=
    rfl
  let e : (radical K 𝔤 ⋊⁅ψ⁆ 𝔤 ⧸ radical K 𝔤) ≃ₗ⁅K⁆ 𝔤 :=
    { toLieHom := lift ψ (incl (radical K 𝔤)) s (by intro x; ext y; simp [ψ, - incl_coe])
      invFun x := ⟨f x, LieIdeal.Quotient.mk x⟩
      left_inv x := by ext <;> simp [hf, hs.eq, LieSubmodule.Quotient.mk_eq_zero'.mpr]
      right_inv x := by simp [hf] }
  have he x : e.symm x = ⟨f x, LieIdeal.Quotient.mk x⟩ := rfl
  rw [← e.isAdo_iff]
  apply IsAdo.semiDirectSum_of_isSolvable
  grw [← map_equiv_nilradical e.symm, map_le_iff_le_comap, nilradical_le_radical,
    IsConcreteLE.le_iff, Subtype.forall']
  simp +contextual [he, eq_comm (a := (0 : 𝔤 ⧸ radical K 𝔤))]
