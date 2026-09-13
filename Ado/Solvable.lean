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

open Set Module LieAlgebra LieModule LieHom LieSubmodule

variable {K 𝔰 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔰] [LieAlgebra K 𝔰] [FiniteDimensional K 𝔰]

-- 注意: 正標数では成り立たない。別ファイルの反例を参照。
public axiom LieIdeal.lieIdealOf_nilradical_eq_of_le (I : LieIdeal K 𝔰) (hN : nilradical K 𝔰 ≤ I) :
    nilradical K I = lieIdealOf (nilradical K 𝔰) I

variable [LieAlgebra.IsSolvable 𝔰]

omit [CharZero K] in
variable (K 𝔰) in
lemma LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔰r : finrank K (𝔰 ⧸ nilradical K 𝔰) = n + 1) :
    ∃ 𝔞 : LieIdeal K 𝔰, finrank K (𝔞 ⧸ nilradical K 𝔞) = n ∧ nilradical K 𝔰 ≤ 𝔞 := by
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K (𝔰 ⧸ nilradical K 𝔰),
      finrank K 𝔞' + 1 = finrank K (𝔰 ⧸ nilradical K 𝔰)
  · existsi comap (LieIdeal.Quotient.mk' (nilradical K 𝔰)) 𝔞'
    have h𝔞'n : nilradical K 𝔰 ≤ comap (Quotient.mk' (nilradical K 𝔰)) 𝔞'
    · grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    constructor
    case right => assumption
    simp_rw [finrank_quotient,
      ← (LieIdeal.Quotient.mk' (nilradical K 𝔰)).lieIdealComap 𝔞'
        |>.finrank_idealRange_add_finrank_ker
          (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
          (LieIdeal.Quotient.surjective_mk' _))),
      idealRange_eq_top_of_surjective _
        (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
      LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker,
      lieIdealOf_nilradical_eq_of_le _ h𝔞'n, finrank_lieIdealOf _ _ h𝔞'n]
    lia
  let 𝔰' := (𝔰 ⧸ nilradical K 𝔰) ⧸ derivedSeries K (𝔰 ⧸ nilradical K 𝔰) 1
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K 𝔰', finrank K 𝔞' + 1 = finrank K 𝔰'
  · existsi comap (LieIdeal.Quotient.mk' (derivedSeries K (𝔰 ⧸ nilradical K 𝔰) 1)) 𝔞'
    simp_rw [
      ← (LieIdeal.Quotient.mk' (derivedSeries K (𝔰 ⧸ nilradical K 𝔰) 1)).lieIdealComap 𝔞'
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
    subst 𝔰'
    lia
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : Submodule K 𝔰', finrank K 𝔞' + 1 = finrank K 𝔰'
  · have : IsLieAbelian 𝔰' := by
      subst 𝔰'
      refine { trivial x y := ?_ }
      obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
      obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
      simp [← Quotient.mk_bracket, lie_mem_lie]
    existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
    simp_rw [← finrank_toSubmodule, h𝔞']
  suffices h𝔰' : 0 < finrank K 𝔰' by
    rw [← Order.one_le_iff_pos] at h𝔰'
    apply Nat.exists_eq_add_of_le' at h𝔰'
    obtain ⟨m, hm⟩ := h𝔰'
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (by lia : m ≤ finrank K 𝔰')
    existsi Submodule.span K (range f)
    simp [finrank_span_eq_card hf, hm]
  subst 𝔰'
  have : Nontrivial (𝔰 ⧸ LieAlgebra.nilradical K 𝔰)
  · simp [← finrank_pos_iff (R := K), h𝔰r]
  have h𝔰' := derivedSeries_lt_top_of_solvable K (𝔰 ⧸ nilradical K 𝔰)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔰'
  exact h𝔰'

structure SolStepAdoData (K 𝔰 : Type*)
    [Field K] [CharZero K] [LieRing 𝔰] [LieAlgebra K 𝔰] [FiniteDimensional K 𝔰]
    [LieAlgebra.IsSolvable 𝔰] where
  protected 𝔞 : LieIdeal K 𝔰
  protected 𝔥 : LieSubalgebra K 𝔰
  nilradical_le_𝔞 : nilradical K 𝔰 ≤ 𝔞
  isCompl_toSubmodule : IsCompl 𝔞.toSubmodule 𝔥.toSubmodule
  [instIsAdo𝔞 : IsAdo K 𝔞]

attribute [instance] SolStepAdoData.instIsAdo𝔞

public axiom SolStepAdoData.isAdo (D : SolStepAdoData K 𝔰) : IsAdo K 𝔰

public local instance LieAlgebra.IsAdo.of_isSolvable : IsAdo K 𝔰 := by
  generalize hn : finrank K (𝔰 ⧸ nilradical K 𝔰) = n
  induction n generalizing 𝔰 with
  | zero =>
    rw [LieIdeal.finrank_quotient, Nat.sub_eq_zero_iff_le, ← not_lt, LieIdeal.finrank_lt_iff,
      not_lt_top_iff, ← top_le_iff, ← LieIdeal.isNilpotent_iff_le_nilradical,
      LieRing.isNilpotent_lieIdeal_top_iff] at hn
    exact IsAdo.of_isNilpotent
  | succ n hin =>
    rsuffices ⟨D⟩ : Nonempty (SolStepAdoData K 𝔰)
    · exact D.isAdo
    obtain ⟨𝔞, hn𝔞, h𝔞⟩ := LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian K 𝔰 n hn
    specialize hin hn𝔞
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔰, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      simp_rw [← hn𝔞, LieIdeal.finrank_quotient, 𝔞.lieIdealOf_nilradical_eq_of_le h𝔞,
        LieIdeal.finrank_lieIdealOf _ _ h𝔞, ← Submodule.finrank_add_eq_of_isCompl h𝔥',
        LieIdeal.finrank_toSubmodule] at hn
      conv at hn => equals finrank K 𝔥' = 1 => grind only [LieIdeal.finrank_mono h𝔞]
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨{ 𝔞, 𝔥, nilradical_le_𝔞 := h𝔞, isCompl_toSubmodule := h𝔥₁ }⟩
