/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib
public import Ado.ForMathlib.LieModulePUnit
public import Ado.ForMathlib.LieModuleSubsingleton
public import Ado.ForMathlib.LieModuleKer
public import Ado.ForMathlib.LieFinrank
public import Ado.ForMathlib.LieQuotient
public import Ado.ForMathlib.LieHom
public import Ado.LieAbelian
public import Ado.UniversalEnvelopingAlgebraTrick

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set Module LieAlgebra LieModule LieSubmodule LieIdeal LieHom

variable {K 𝔫 : Type*}
variable [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

@[simps toSubmodule]
def Submodule.toLieSubalgebraOfDimOne (𝔥 : Submodule K 𝔫) (h𝔥 : finrank K 𝔥 = 1) :
    LieSubalgebra K 𝔫 where
  toSubmodule := 𝔥
  lie_mem' {x y} hx hy := by
    -- これ戦術化できないかな
    obtain ⟨x', rfl, rfl⟩ : ∃ x' : 𝔥, x = x'.1 ∧ hx ≍ x'.2 := ⟨⟨x, hx⟩, rfl, HEq.rfl⟩
    obtain ⟨y', rfl, rfl⟩ : ∃ y' : 𝔥, y = y'.1 ∧ hy ≍ y'.2 := ⟨⟨y, hy⟩, rfl, HEq.rfl⟩
    rw [finrank_eq_one_iff'] at h𝔥
    obtain ⟨v, hv, h𝔥⟩ := h𝔥
    obtain ⟨c₁, rfl⟩ := h𝔥 x'
    obtain ⟨c₂, rfl⟩ := h𝔥 y'
    simp

lemma LieAlgebra.IsAdo.of_isNilpotent_of_isFaithful_center
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔫 V]
    [LieModule K 𝔫 V] [IsFaithful K (center K 𝔫) V] [LieModule.IsNilpotent 𝔫 V] :
    IsAdo K 𝔫 := by
  suffices IsFaithful K 𝔫 (𝔫 × V) from .intro (𝔫 × V)
  rename IsFaithful K (center K 𝔫) V => h
  rw [isFaithful_iff_ker_eq_bot] at h ⊢
  -- `lieIdealOf` の問題を解決しても `Disjoint` の可換性の問題で詰む
  simpa [← disjoint_iff, - comap_incl] using h

variable (K 𝔫) in
lemma LieIdeal.exists_for_nilStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔫r : finrank K 𝔫 = n + 1) (h𝔫a : ¬IsLieAbelian 𝔫) :
    ∃ 𝔞 : LieIdeal K 𝔫, finrank K 𝔞 = n ∧ center K 𝔫 ≤ 𝔞 := by
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K (𝔫 ⧸ center K 𝔫),
      finrank K 𝔞' + 1 = finrank K (𝔫 ⧸ center K 𝔫)
  · existsi comap (LieIdeal.Quotient.mk' (center K 𝔫)) 𝔞'
    constructor
    case right => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    simp_rw [
      ← (LieIdeal.Quotient.mk' (center K 𝔫)).lieIdealComap 𝔞'
        |>.finrank_idealRange_add_finrank_ker
          (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
          (LieIdeal.Quotient.surjective_mk' _))),
      idealRange_eq_top_of_surjective _
        (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
      LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker]
    conv =>
      enter [1, 2]
      apply finrank_lieIdealOf
      tactic => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    rw [finrank_quotient, eq_tsub_iff_add_eq_of_le (by simp)] at h𝔞'
    lia
  let 𝔫' := (𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K 𝔫', finrank K 𝔞' + 1 = finrank K 𝔫'
  · existsi comap (LieIdeal.Quotient.mk' (derivedSeries K (𝔫 ⧸ center K 𝔫) 1)) 𝔞'
    simp_rw [
      ← (LieIdeal.Quotient.mk' (derivedSeries K (𝔫 ⧸ center K 𝔫) 1)).lieIdealComap 𝔞'
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
    subst 𝔫'
    lia
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : Submodule K 𝔫', finrank K 𝔞' + 1 = finrank K 𝔫'
  · have : IsLieAbelian 𝔫' := by
      subst 𝔫'
      refine { trivial x y := ?_ }
      obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
      obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
      simp [← Quotient.mk_bracket, lie_mem_lie]
    existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
    simp_rw [← finrank_toSubmodule, h𝔞']
  suffices h𝔫' : 0 < finrank K 𝔫' by
    rw [← Order.one_le_iff_pos] at h𝔫'
    apply Nat.exists_eq_add_of_le' at h𝔫'
    obtain ⟨m, hm⟩ := h𝔫'
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (by lia : m ≤ finrank K 𝔫')
    existsi Submodule.span K (range f)
    simp [finrank_span_eq_card hf, hm]
  subst 𝔫'
  rw [isLieAbelian_iff_center_eq_top K, ← ne_eq, ← lt_top_iff_ne_top, ← finrank_lt_iff,
    ← Nat.sub_pos_iff_lt, ← finrank_quotient, finrank_pos_iff] at h𝔫a
  have h𝔫' := derivedSeries_lt_top_of_solvable K (𝔫 ⧸ center K 𝔫)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔫'
  exact h𝔫'

structure NilStepAdoData (K 𝔫 : Type*)
    [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫] [LieRing.IsNilpotent 𝔫] where
  protected 𝔞 : LieIdeal K 𝔫
  protected 𝔥 : LieSubalgebra K 𝔫
  center_le_𝔞 : center K 𝔫 ≤ 𝔞
  finrank_𝔥 : finrank K 𝔥 = 1
  isCompl_toSubmodule : IsCompl 𝔞.toSubmodule 𝔥.toSubmodule
  [instIsAdo𝔞 : IsAdo K 𝔞]

attribute [instance] NilStepAdoData.instIsAdo𝔞

lemma NilStepAdoData.isAdo (D : NilStepAdoData K 𝔫) : IsAdo K 𝔫 :=
  sorry

public lemma LieAlgebra.IsAdo.of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing 𝔫 with
  | zero => rw [finrank_zero_iff] at hn; exact .intro Unit
  | succ n hin =>
    by_cases h𝔫 : IsLieAbelian 𝔫
    case pos => exact .of_isLieAbelian
    rsuffices ⟨D⟩ : Nonempty (NilStepAdoData K 𝔫)
    · exact D.isAdo
    obtain ⟨𝔞, rfl, h𝔞⟩ := exists_for_nilStepAdoData_of_not_isLieAbelian K 𝔫 n hn h𝔫
    specialize hin rfl
    obtain ⟨𝔥, h𝔥₁, h𝔥₂⟩ : ∃ 𝔥 : LieSubalgebra K 𝔫,
        IsCompl 𝔞.toSubmodule 𝔥.toSubmodule ∧ finrank K 𝔥 = 1 := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      rw [← Submodule.finrank_add_eq_of_isCompl h𝔥', finrank_toSubmodule,
        Nat.add_left_cancel_iff] at hn
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact ⟨h𝔥', hn⟩
    exact ⟨{ 𝔞, 𝔥, center_le_𝔞 := h𝔞, finrank_𝔥 := h𝔥₂, isCompl_toSubmodule := h𝔥₁ }⟩
