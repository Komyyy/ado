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

section WhiteheadFirst

open Function LieAlgebra

variable {K L V} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V]

namespace LieDerivation

public axiom surjective_inner_of_isKilling [IsKilling K L] : Surjective (inner K L V)

end LieDerivation

end WhiteheadFirst

public section WeylReducibility

open Module LieAlgebra LieModule
open Submodule (projection)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubmodule

set_option maxHeartbeats 300000 in
-- `LinearMap.IsProj (W : Submodule K V) pt.toLinearMap` での `simp` で失敗する
instance complementedLattice_of_isKilling {K L V}
    [Field K] [LieRing L] [LieAlgebra K L] [IsKilling K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    ComplementedLattice (LieSubmodule K L V) where
  exists_isCompl W := by
    let LW : Submodule K (End K V) :=
      { carrier := {t | LinearMap.range t ≤ W ∧ Submodule.map t W = ⊥}
        add_mem' := by
          simp_rw [Set.mem_ofPred]
          rintro t u ⟨ht₁, ht₂⟩ ⟨hu₁, hu₂⟩
          split_ands
          · grw [LinearMap.range_add_le, ht₁, hu₁, sup_idem]
          · grw [_root_.eq_bot_iff, Submodule.map_add_le, ht₂, hu₂, sup_idem]
        zero_mem' := by simp
        smul_mem' := by
          simp_rw [Set.mem_ofPred]
          rintro c t ⟨ht₁, ht₂⟩
          split_ands
          · grw [LinearMap.range_smul_le_range, ht₁]
          · grw [_root_.eq_bot_iff, Submodule.map_smul_le_map, ht₂] }
    have hLW₁ t : t ∈ LW ↔ LinearMap.range t ≤ W ∧ Submodule.map t W = ⊥ :=
      Iff.rfl
    have hLW₂ (t : LW) : LinearMap.range t.val ≤ W ∧ Submodule.map t.val W = ⊥ :=
      hLW₁ t.val |>.mp t.property
    let : Bracket L LW :=
      { bracket x t := ⟨⁅toEnd K L V x, (t : End K V)⁆, by
          simp_rw [hLW₁, LieRing.of_associative_ring_bracket, End.mul_eq_comp, sub_eq_add_neg]
          split_ands
          · grw [LinearMap.range_add_le, LinearMap.range_neg, LinearMap.range_comp,
              LinearMap.range_comp, (hLW₂ t).1, coe_map_toEnd_le, LinearMap.map_le_range,
              (hLW₂ t).1, sup_idem]
          · grw [_root_.eq_bot_iff, Submodule.map_add_le, Submodule.map_neg, Submodule.map_comp,
              Submodule.map_comp, (hLW₂ t).2, Submodule.map_bot, coe_map_toEnd_le, (hLW₂ t).2,
              sup_idem]⟩ }
    have hLW₃ (x : L) (t : LW) : (↑⁅x, t⁆ : End K V) = ⁅toEnd K L V x, (t : End K V)⁆ :=
      rfl
    let : LieRingModule L LW :=
      { add_lie x y t := by ext; simp [hLW₃]
        lie_add x t u := by ext; simp [hLW₃]
        leibniz_lie x y t := by ext; simp [hLW₃] }
    have : LieModule K L LW :=
      { smul_lie r x t := by ext; simp [hLW₃]
        lie_smul r x t := by ext; simp [hLW₃] }
    obtain ⟨Wc, hWc⟩ := W.toSubmodule.exists_isCompl
    let f : LieDerivation K L LW :=
      { toFun x := ⟨⁅projection W Wc hWc, toEnd K L V x⁆, by
          simp_rw [hLW₁]
          split_ands
          · simp_rw [LieRing.of_associative_ring_bracket, End.mul_eq_comp, sub_eq_add_neg]
            grw [LinearMap.range_add_le, LinearMap.range_neg, LinearMap.range_comp,
              LinearMap.range_comp, Submodule.range_projection, coe_map_toEnd_le,
              LinearMap.map_le_range, Submodule.range_projection, sup_idem]
          · convert_to ∀ y ∈ W, projection W Wc hWc ⁅x, y⁆ - ⁅x, projection W Wc hWc y⁆ = 0 using 0
            · simp [Submodule.eq_bot_iff]
            intro y hy
            simp [Submodule.projection_apply_of_mem_left, hy, show ⁅x, y⁆ ∈ W from W.lie_mem hy]⟩
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp
        leibniz' x y := by
          ext : 1
          simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_sub, LieHom.map_lie,
            hLW₃, ← lie_skew (projection W Wc hWc), lie_lie, lie_neg]
          abel }
    obtain ⟨t, ht⟩ := LieDerivation.surjective_inner_of_isKilling f
    convert_to ∀ (x : L) , ⁅toEnd K L V x, projection W Wc hWc + (t : End K V)⁆ = 0 using 0 at ht
    · simp [DFunLike.ext_iff, Subtype.ext_iff, hLW₃, f]; grind only
    let pt : V →ₗ⁅K, L⁆ V :=
      { toLinearMap := projection W Wc hWc + t
        map_lie' {x} := by
          convert ht x using 0
          simp [DFunLike.ext_iff]; grind only }
    have hpt : LinearMap.IsProj (W : Submodule K V) pt.toLinearMap
    · constructor
      · convert_to LinearMap.range (projection W Wc hWc + (t : End K V)) ≤ (W : Submodule K V)
          using 0
        · simp [IsConcreteLE.le_iff, pt]
        grw [LinearMap.range_add_le, Submodule.range_projection, (hLW₂ t).1, sup_idem]
      · replace hLW₂ : ∀ (x) (hx : x ∈ W), (t : End K V) x = 0
        · simpa [Submodule.eq_bot_iff] using (hLW₂ t).2
        simp +contextual [pt, Submodule.projection_apply_of_mem_left, hLW₂]
    existsi LieModuleHom.ker pt
    simp_rw [← LieSubmodule.isCompl_toSubmodule, LieModuleHom.ker_toSubmodule, hpt.isCompl]

end LieSubmodule

end WeylReducibility

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
