/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Nilpotent

/-!
## 可解 Lie 代数に対する Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Set Module LieAlgebra LieModule LieHom LieSubmodule SemiDirectSum UniversalEnvelopingAlgebra

variable {K 𝔯 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔯] [LieAlgebra K 𝔯] [FiniteDimensional K 𝔯]

-- 注意: 正標数では成り立たない。別ファイルの反例を参照。
public axiom LieIdeal.lieIdealOf_nilradical_eq_of_le (I : LieIdeal K 𝔯) (hN : nilradical K 𝔯 ≤ I) :
    nilradical K I = lieIdealOf (nilradical K 𝔯) I

variable [LieAlgebra.IsSolvable 𝔯]

omit [CharZero K] in
variable (K 𝔯) in
lemma LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔯r : finrank K (𝔯 ⧸ nilradical K 𝔯) = n + 1) :
    ∃ 𝔞 : LieIdeal K 𝔯, finrank K (𝔞 ⧸ nilradical K 𝔞) = n ∧ nilradical K 𝔯 ≤ 𝔞 := by
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K (𝔯 ⧸ nilradical K 𝔯),
      finrank K 𝔞' + 1 = finrank K (𝔯 ⧸ nilradical K 𝔯)
  · existsi comap (LieIdeal.Quotient.mk' (nilradical K 𝔯)) 𝔞'
    have h𝔞'n : nilradical K 𝔯 ≤ comap (Quotient.mk' (nilradical K 𝔯)) 𝔞'
    · grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    constructor
    case right => assumption
    simp_rw [finrank_quotient,
      ← (LieIdeal.Quotient.mk' (nilradical K 𝔯)).lieIdealComap 𝔞'
        |>.finrank_idealRange_add_finrank_ker
          (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
          (LieIdeal.Quotient.surjective_mk' _))),
      idealRange_eq_top_of_surjective _
        (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
      LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker,
      lieIdealOf_nilradical_eq_of_le _ h𝔞'n, finrank_lieIdealOf _ _ h𝔞'n]
    lia
  let 𝔯' := (𝔯 ⧸ nilradical K 𝔯) ⧸ derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K 𝔯', finrank K 𝔞' + 1 = finrank K 𝔯'
  · existsi comap (LieIdeal.Quotient.mk' (derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1)) 𝔞'
    simp_rw [
      ← (LieIdeal.Quotient.mk' (derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1)).lieIdealComap 𝔞'
        |>.finrank_idealRange_add_finrank_ker
          (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
          (LieIdeal.Quotient.surjective_mk' _))),
      idealRange_eq_top_of_surjective _
        (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
      LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker]
    conv =>
      enter [1, 1, 2]
      apply finrank_lieIdealOf
      tactic => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    rw [finrank_quotient, eq_tsub_iff_add_eq_of_le (by simp [- finrank_quotient])] at h𝔞'
    subst 𝔯'
    lia
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : Submodule K 𝔯', finrank K 𝔞' + 1 = finrank K 𝔯'
  · have : IsLieAbelian 𝔯' := by
      subst 𝔯'
      refine { trivial x y := ?_ }
      obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
      obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
      simp [← Quotient.mk_bracket, lie_mem_lie]
    existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
    simp_rw [← finrank_toSubmodule, h𝔞']
  suffices h𝔯' : 0 < finrank K 𝔯' by
    rw [← Order.one_le_iff_pos] at h𝔯'
    apply Nat.exists_eq_add_of_le' at h𝔯'
    obtain ⟨m, hm⟩ := h𝔯'
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (by lia : m ≤ finrank K 𝔯')
    existsi Submodule.span K (range f)
    simp [finrank_span_eq_card hf, hm]
  subst 𝔯'
  have : Nontrivial (𝔯 ⧸ LieAlgebra.nilradical K 𝔯)
  · simp [← finrank_pos_iff (R := K), h𝔯r]
  have h𝔯' := derivedSeries_lt_top_of_solvable K (𝔯 ⧸ nilradical K 𝔯)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔯'
  exact h𝔯'

section Step

variable {𝔞 𝔥 : Type*}
variable [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥] [IsAdo K 𝔞]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)
variable (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (SemiDirectSum.inl ψ).idealRange)

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K 𝔞) in
noncomputable def annihilatingIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  RingHom.ker (UniversalEnvelopingAlgebra.lift K (toEnd K 𝔞 (AdoSpace K 𝔞)))
deriving Ideal.IsTwoSided

public axiom map_leftLieUE_annihilatingIdeal_le_annihilatingIdeal [CharZero K] (x : 𝔥) :
    Submodule.map (leftLieUE ψ x) (Submodule.restrictScalars K (annihilatingIdeal K 𝔞)) ≤
      Submodule.restrictScalars K (annihilatingIdeal K 𝔞)

lemma leftLieUE_mem_annihilatingIdeal (x : 𝔥) {a : UniversalEnvelopingAlgebra K 𝔞}
    (ha : a ∈ annihilatingIdeal K 𝔞) : leftLieUE ψ x a ∈ annihilatingIdeal K 𝔞 := by
  have h := map_leftLieUE_annihilatingIdeal_le_annihilatingIdeal ψ x
  rw [Submodule.map_le_iff_le_comap] at h
  apply mem_of_le_of_mem at h
  simp_all

variable (K 𝔞) in
noncomputable def nilIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  annihilatingIdeal K 𝔞 ^ nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)
deriving Ideal.IsTwoSided

lemma map_leftLieUE_nilIdeal_le_nilIdeal (x : 𝔥) :
    Submodule.map (leftLieUE ψ x) (Submodule.restrictScalars K (nilIdeal K 𝔞)) ≤
      Submodule.restrictScalars K (nilIdeal K 𝔞) := by
  unfold nilIdeal
  generalize nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) = n
  induction n with
  | zero => simp [Submodule.pow_zero]
  | succ n hn =>
    simp only [Submodule.map_le_iff_le_comap] at hn ⊢
    -- `Submodule.restrictScalars_mem` という名前はよく無い
    simp only [IsConcreteLE.le_iff, Submodule.mem_comap, Submodule.restrictScalars_mem] at hn
    simp_rw [Submodule.pow_succ, Submodule.restrictScalars_mul, Submodule.mul_le,
      Submodule.mem_comap, ← Submodule.restrictScalars_mul, Submodule.restrictScalars_mem]
    intro a ha b hb
    rw [leftLieUE_mul]
    solve_by_elim (maxDepth := 10) (transparency := .instances)
      [hn, add_mem, Submodule.mul_mem_mul, leftLieUE_mem_annihilatingIdeal]

lemma leftLieUE_mem_nilIdeal (x : 𝔥) {a : UniversalEnvelopingAlgebra K 𝔞}
    (ha : a ∈ nilIdeal K 𝔞) : leftLieUE ψ x a ∈ nilIdeal K 𝔞 := by
  have h := map_leftLieUE_nilIdeal_le_nilIdeal ψ x
  rw [Submodule.map_le_iff_le_comap] at h
  apply mem_of_le_of_mem at h
  simp_all

noncomputable def nilLieSubmodule : LieSubmodule K (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  __ := Submodule.restrictScalars K (nilIdeal K 𝔞)
  lie_mem {x a} ha := by
    simp_all only [Submodule.toAddSubmonoid_restrictScalars, Submodule.carrier_eq_coe,
      SetLike.mem_coe]
    obtain ⟨x, y⟩ := x
    simp only [lieUE_def, bracket_eq]
    solve_by_elim (transparency := .reducible) [add_mem, Ideal.mul_mem_left, leftLieUE_mem_nilIdeal]

end UniversalEnvelopingAlgebra

abbrev SolStepAdoSpace :=
  UniversalEnvelopingAlgebra K 𝔞 ⧸ nilLieSubmodule ψ

end Step

-- 一般の場合でも使うので公開
public axiom LieAlgebra.IsAdo.semiDirectSum_of_isSolvable [CharZero K] {𝔞 𝔥 : Type*}
    [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
    [FiniteDimensional K 𝔞] [FiniteDimensional K 𝔥] [IsAdo K 𝔞]
    (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞) [IsSolvable (𝔞 ⋊⁅ψ⁆ 𝔥)]
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (inl ψ).idealRange) :
    IsAdo K (𝔞 ⋊⁅ψ⁆ 𝔥)

lemma LieAlgebra.IsAdo.of_isInnerSemiDirectSum_of_isSolvable
    (𝔞 : LieIdeal K 𝔯) (𝔥 : LieSubalgebra K 𝔯)
    (hi : IsInnerSemiDirectSum 𝔞 𝔥) (hn : nilradical K 𝔯 ≤ 𝔞) [IsAdo K 𝔞] : IsAdo K 𝔯 := by
  rw [(lieEquivLieSubalgebra hi).symm.isAdo_iff]
  have := (lieEquivLieSubalgebra hi).injective.lieAlgebra_isSolvable
  apply (LieIdeal.map_mono (f := (lieEquivLieSubalgebra hi).symm.toLieHom)).imp at hn
  rw [map_equiv_nilradical] at hn
  conv_rhs at hn => equals idealRange (inl ((LieDerivation.adoIdeal 𝔞).comp 𝔥.incl)) =>
    ext ⟨x, y⟩
    have h : y.1 ∈ 𝔞 ↔ y = 0 :=
      Submodule.mem_left_iff_eq_zero_of_disjoint hi.disjoint
    simp [add_mem_cancel_left, eq_comm (a := 0) (b := y), h]
  exact .semiDirectSum_of_isSolvable _ hn

public local instance LieAlgebra.IsAdo.of_isSolvable : IsAdo K 𝔯 := by
  generalize hn : finrank K (𝔯 ⧸ nilradical K 𝔯) = n
  induction n generalizing 𝔯 with
  | zero =>
    rw [LieIdeal.finrank_quotient, Nat.sub_eq_zero_iff_le, ← not_lt, LieIdeal.finrank_lt_iff,
      not_lt_top_iff, ← top_le_iff, ← LieIdeal.isNilpotent_iff_le_nilradical,
      LieRing.isNilpotent_lieIdeal_top_iff] at hn
    exact IsAdo.of_isNilpotent
  | succ n hin =>
    rsuffices ⟨𝔞, 𝔥, hi, hc, _⟩ : ∃ (𝔞 : LieIdeal K 𝔯) (𝔥 : LieSubalgebra K 𝔯),
        IsInnerSemiDirectSum 𝔞 𝔥 ∧ nilradical K 𝔯 ≤ 𝔞 ∧ IsAdo K 𝔞
    · exact .of_isInnerSemiDirectSum_of_isSolvable 𝔞 𝔥 hi hc
    obtain ⟨𝔞, hn𝔞, h𝔞⟩ := LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian K 𝔯 n hn
    specialize hin hn𝔞
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔯, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      simp_rw [← hn𝔞, LieIdeal.finrank_quotient, 𝔞.lieIdealOf_nilradical_eq_of_le h𝔞,
        LieIdeal.finrank_lieIdealOf _ _ h𝔞, ← Submodule.finrank_add_eq_of_isCompl h𝔥',
        LieIdeal.finrank_toSubmodule] at hn
      conv at hn => equals finrank K 𝔥' = 1 => grind only [LieIdeal.finrank_mono h𝔞]
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨𝔞, 𝔥, h𝔥₁.isInnerSemidirectSum, h𝔞, hin⟩
