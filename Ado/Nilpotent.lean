/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieCenter
public import Ado.ForMathlib.LieFinrank
public import Ado.ForMathlib.LieModuleKer
public import Ado.ForMathlib.LieModulePUnit
public import Ado.ForMathlib.LieModuleSubsingleton
public import Ado.ForMathlib.LieMono
public import Ado.LieAbelian
public import Ado.SemiDirectSumAction

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set Finset LieAlgebra LieModule LieSubmodule LieIdeal LieHom SemiDirectSum
open Module UniversalEnvelopingAlgebra
open TensorAlgebra hiding ι

variable {K 𝔫 : Type*}
variable [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

-- `expose` しないと `simps` でエラーになる
@[expose, simps toSubmodule]
public def Submodule.toLieSubalgebraOfDimOne (𝔥 : Submodule K 𝔫) (h𝔥 : finrank K 𝔥 = 1) :
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
    conv_lhs =>
      enter [2]
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

section Step

variable {𝔞 𝔥 : Type*}
variable [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)

namespace LieAlgebra.SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

section LengthSubmodule

-- TODO: `UniversalEnvelopingAlgebra` 名前空間に移動
variable (K 𝔞) in
def lengthSubmodule (m : ℕ) : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  Submodule.map (mkAlgHom K 𝔞).toLinearMap
    (⨆ k ≥ m, LinearMap.range (TensorPower.toTensorAlgebra (n := k)))

@[simp]
lemma mkAlgHom_tprod_mem_lengthSubmodule (m) {n} (f : Fin n → 𝔞) (hn : m ≤ n) :
    mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f) ∈ lengthSubmodule K 𝔞 m := by
  unfold lengthSubmodule
  apply Submodule.mem_map_of_mem
  apply Submodule.mem_iSup_of_mem n
  apply Submodule.mem_iSup_of_mem hn
  convert LinearMap.mem_range_self _ (PiTensorProduct.tprod K f)
  simp

lemma lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod (m) :
    lengthSubmodule K 𝔞 m =
      .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞), m ≤ n ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)} := by
  apply le_antisymm
  · simp_rw [lengthSubmodule, Submodule.map_le_iff_le_comap, iSup₂_le_iff,
      LinearMap.range_le_iff_comap, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top,
      Submodule.span_le, range_subset_iff]
    intro n hn f
    apply Submodule.mem_span_of_mem
    rw [mem_ofPred]
    existsi n, f, hn
    simp
  · rw [Submodule.span_le, ofPred_subset]
    rintro _ ⟨n, f, hn, rfl⟩
    simp [hn, - TensorAlgebra.tprod_apply]

@[simp]
lemma lengthSubmodule_zero : lengthSubmodule K 𝔞 0 = ⊤ := by
  have hι := DirectSum.Decomposition.isInternal
      (fun n : ℕ ↦ LinearMap.range (TensorAlgebra.ι K : 𝔞 →ₗ[K] TensorAlgebra K 𝔞) ^ n)
  simp_rw [TensorAlgebra.ι_range_pow_eq] at hι
  apply DirectSum.IsInternal.submodule_iSup_eq_top at hι
  simp [lengthSubmodule, hι,
    LinearMap.range_eq_top_of_surjective (mkAlgHom K 𝔞).toLinearMap (mkAlgHom_surjective K 𝔞),
    - Submodule.map_iSup]

@[gcongr]
lemma lengthSubmodule_mono ⦃m n⦄ (h : m ≤ n) : lengthSubmodule K 𝔞 n ≤ lengthSubmodule K 𝔞 m := by
  simp_rw [lengthSubmodule]
  gcongr 1
  apply biSup_mono
  rwa [forall_ge_iff_le]

lemma antitone_lengthSubmodule : Antitone (lengthSubmodule K 𝔞) :=
  lengthSubmodule_mono

lemma ι_mul_mem_lengthSubmodule_succ_of_mem (m) (x : 𝔞) (a) (ha : a ∈ lengthSubmodule K 𝔞 m) :
    UniversalEnvelopingAlgebra.ι K x * a ∈ lengthSubmodule K 𝔞 (m + 1) := by
  revert a
  suffices h :
      Submodule.map (LinearMap.mul K _ (UniversalEnvelopingAlgebra.ι K x)) (lengthSubmodule K 𝔞 m)
        ≤ lengthSubmodule K 𝔞 (m + 1) by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage,
    LinearMap.mul_apply_apply]
  rintro _ ⟨n, f, hn, rfl⟩
  conv => equals
      mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 (n + 1) (Fin.cons x f))
        ∈ lengthSubmodule K 𝔞 (m + 1) =>
    simp
  exact mkAlgHom_tprod_mem_lengthSubmodule _ _ (by lia)

lemma bracket_𝔞_mem_lengthSubmodule_succ_of_mem (m) (x : 𝔞) (a) (ha : a ∈ lengthSubmodule K 𝔞 m) :
    ⁅x, a⁆ ∈ lengthSubmodule K 𝔞 (m + 1) := by
  rw [bracket_eq]
  exact ι_mul_mem_lengthSubmodule_succ_of_mem m x a ha

end LengthSubmodule

section NilSubmodule

variable [IsAdo K 𝔞]

variable (K 𝔞) in
noncomputable def nilSubmodule : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  lengthSubmodule K 𝔞 (nilpotencyLength 𝔞 (AdoSpace K 𝔞))

lemma nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod :
    nilSubmodule K 𝔞 =
      .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞), nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ n ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)} :=
  lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod (nilpotencyLength 𝔞 (AdoSpace K 𝔞))

lemma lengthSubmodule_nilpotenctLength :
    lengthSubmodule K 𝔞 (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) = nilSubmodule K 𝔞 :=
  rfl

@[simp]
lemma mkAlgHom_tprod_mem_nilSubmodule {n} (f : Fin n → 𝔞)
    (hn : nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ n) :
    mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f) ∈ nilSubmodule K 𝔞 :=
  mkAlgHom_tprod_mem_lengthSubmodule (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) f hn

@[simp]
lemma ι_mul_mem_nilSubmodule_of_mem (x : 𝔞) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    UniversalEnvelopingAlgebra.ι K x * a ∈ nilSubmodule K 𝔞 := by
  rw [← lengthSubmodule_nilpotenctLength] at ha ⊢
  grw [(by lia : nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ nilpotencyLength 𝔞 (AdoSpace K 𝔞) + 1)]
  apply ι_mul_mem_lengthSubmodule_succ_of_mem
  exact ha

lemma bracket_mem_nilSubmodule_of_mem (x : 𝔞) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    ⁅x, a⁆ ∈ nilSubmodule K 𝔞 := by
  rw [bracket_eq]
  exact ι_mul_mem_nilSubmodule_of_mem x a ha

@[simp]
lemma leftLieUE_mem_nilSubmodule_of_mem (x : 𝔥) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    leftLieUE ψ x a ∈ nilSubmodule K 𝔞 := by
  revert a
  suffices h :
      Submodule.map (leftLieUE ψ x) (nilSubmodule K 𝔞) ≤ nilSubmodule K 𝔞 by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage]
  rintro _ ⟨n, f, hn, rfl⟩
  conv => equals ∑ i : Fin n,
      mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (f i)))) ∈ nilSubmodule K 𝔞 =>
    simp [leftLieUE_mkAlgHom, - TensorAlgebra.tprod_apply]
  apply Submodule.sum_mem
  rintro i -
  exact mkAlgHom_tprod_mem_nilSubmodule _ hn

end NilSubmodule

section DepthSubmodule

def depthSubmodule (m : ℕ) : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞) (x : Fin n → ℕ),
      ∑ k, x k = m ∧
      (∀ k, (f k) ∈ (lowerCentralSeries K (inr ψ).range (inl ψ).idealRange (x k)).toSubmodule.comap
          (equivIdealRangeInl ψ).toLinearMap) ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)}

@[simp]
lemma depththSubmodule_zero : depthSubmodule ψ 0 = ⊤ := by
  simp_rw [eq_top_iff, ← lengthSubmodule_zero, lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod,
    zero_le, true_and, Submodule.span_le, ofPred_subset, SetLike.mem_coe]
  rintro _ ⟨n, f, rfl⟩
  unfold depthSubmodule
  apply Submodule.mem_span_of_mem
  rw [mem_ofPred]
  existsi n, f, 0
  simp

@[gcongr]
lemma depthSubmodule_mono ⦃m n⦄ (h : m ≤ n) : depthSubmodule ψ n ≤ depthSubmodule ψ m := by
  simp_rw [depthSubmodule]
  gcongr 4 with _ n f
  rintro ⟨x, rfl, hf, rfl⟩
  rsuffices ⟨x', hx', rfl⟩ : ∃ x' : Fin n → ℕ, x' ≤ x ∧ ∑ k, x' k = m
  · existsi x'
    refine ⟨rfl, ?_, rfl⟩
    intro k
    grw [hx' k]
    exact hf k
  induction h using Nat.decreasingInduction with
  | self => exists x
  | of_succ k h hi =>
    obtain ⟨x', hx', hi⟩ := hi
    have hx'₂ : 0 < ∑ k, x' k := by lia
    simp_rw [Finset.sum_pos_iff, Finset.mem_univ, true_and] at hx'₂
    obtain ⟨j, hj⟩ := hx'₂
    existsi x' - Pi.single j 1
    constructor
    · grw [tsub_le_self, hx']
    · have hx'₂ : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          Pi.single (M := fun _ ↦ ℕ) j 1 i ≤ x' i
      · rintro i -
        obtain (rfl | hj) := eq_or_ne i j
        · simp [hj, Nat.succ_le_iff]
        · simp [hj]
      simp_rw [Pi.sub_apply, Finset.sum_tsub_distrib _ hx'₂]
      simp [hi]

lemma leftLieUE_mem_depthSubmodule_succ_of_mem (m) (x : 𝔥) (a) (ha : a ∈ depthSubmodule ψ m) :
    leftLieUE ψ x a ∈ depthSubmodule ψ (m + 1) := by
  revert a
  suffices h :
      Submodule.map (leftLieUE ψ x) (depthSubmodule ψ m) ≤ depthSubmodule ψ (m + 1) by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [depthSubmodule, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage]
  rintro _ ⟨n, f, y, hy, hf, rfl⟩
  simp_rw [leftLieUE_mkAlgHom, leftLieUEAux_tprod, map_sum, SetLike.mem_coe]
  apply sum_mem; rintro k -
  simp_rw [depthSubmodule]; apply Submodule.mem_span_of_mem; simp_rw [mem_ofPred_eq]
  existsi n, update f k (ψ x (f k)), y + Pi.single k 1
  split_ands
  on_goal 3 => rfl
  · simp [Finset.sum_add_distrib, hy]
  · intro j
    obtain (rfl | hj) := eq_or_ne j k
    · specialize hf j
      conv at hf => equals
        equivIdealRangeInl ψ (f j) ∈ lowerCentralSeries K (inr ψ).range (inl ψ).idealRange (y j) =>
          simp
      replace hf := lie_mem_lie (by simp : ⟨inr ψ x, by simp⟩ ∈ (⊤ : LieIdeal K (inr ψ).range)) hf
      conv at hf => enter [2]; equals equivIdealRangeInl ψ (ψ x (f j)) => ext : 1; simp
      simpa using hf
    · simp [hj, hf]

variable [IsAdo K 𝔞]

noncomputable def depthLimit : ℕ :=
  Nat.pred (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) *
    Nat.pred (nilpotencyLength (inr ψ).range (inl ψ).idealRange) + 1

variable {ψ} in
lemma exists_nilpotencyLength_le_of_depthLimit_le_sum {n} [NeZero n] (x : Fin n → ℕ)
    (hn : n < nilpotencyLength 𝔞 (AdoSpace K 𝔞)) (hx : depthLimit ψ ≤ ∑ i, x i) :
    ∃ i, nilpotencyLength (inr ψ).range (inl ψ).idealRange ≤ x i := by
  apply Nat.le_pred_of_lt at hn
  grw [depthLimit, Nat.succ_le_iff, ← hn] at hx
  conv_lhs at hx =>
    equals ∑ _ : Fin n, Nat.pred (nilpotencyLength (inr ψ).range (inl ψ).idealRange) => simp
  apply Finset.exists_lt_of_sum_lt at hx
  simp_rw [Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi⟩ := hx
  apply Nat.le_of_pred_lt at hi
  exists i

lemma depthSubmodule_depthLimit_le_nilSubmodule [LieRing.IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥)] :
    depthSubmodule ψ (depthLimit ψ) ≤ nilSubmodule K 𝔞 := by
  simp_rw [depthSubmodule, Submodule.span_le, ofPred_subset, SetLike.mem_coe]
  rintro _ ⟨n, f, x, hx, hf, rfl⟩
  obtain (rfl | hn) := eq_or_ne n 0
  case inl => simp [depthLimit] at hx
  obtain (hn₂ | hn₂) := lt_or_ge n (nilpotencyLength 𝔞 (AdoSpace K 𝔞))
  case inr => apply mkAlgHom_tprod_mem_nilSubmodule _ hn₂
  apply NeZero.mk at hn
  replace hx := exists_nilpotencyLength_le_of_depthLimit_le_sum x hn₂ hx.ge
  obtain ⟨i, hi⟩ := hx
  specialize hf i
  grw [← hi, lowerCentralSeries_nilpotencyLength] at hf
  conv at hf => equals f i = 0 => simp
  simp [(TensorAlgebra.tprod K 𝔞 n).map_coord_zero i hf, - TensorAlgebra.tprod_apply]

end DepthSubmodule

instance [IsAdo K 𝔞] [FiniteDimensional K 𝔞] :
    FiniteDimensional K (UniversalEnvelopingAlgebra K 𝔞 ⧸ nilSubmodule K 𝔞) := by
  -- `Submodule` を後で `open` した方がいいかな
  suffices h : Submodule.map (nilSubmodule K 𝔞).mkQ
      (Submodule.map (mkAlgHom K 𝔞).toLinearMap
        (⨆ k < nilpotencyLength 𝔞 (AdoSpace K 𝔞),
          LinearMap.range (TensorPower.toTensorAlgebra (n := k)))) = ⊤ by
    simp_rw [Module.finite_def, ← h]
    apply Submodule.FG.map
    apply Submodule.FG.map
    simp_rw [← Finset.mem_Iio]
    apply Submodule.fg_biSup
    rintro n -
    apply Submodule.fg_range
  suffices h : Submodule.map (nilSubmodule K 𝔞).mkQ
      (Submodule.map (mkAlgHom K 𝔞).toLinearMap
        (⨆ k ≥ nilpotencyLength 𝔞 (AdoSpace K 𝔞),
          LinearMap.range (TensorPower.toTensorAlgebra (n := k)))) = ⊥ by
    have hι := DirectSum.Decomposition.isInternal
        (fun n : ℕ ↦ LinearMap.range (TensorAlgebra.ι K : 𝔞 →ₗ[K] TensorAlgebra K 𝔞) ^ n)
    simp_rw [TensorAlgebra.ι_range_pow_eq] at hι
    apply DirectSum.IsInternal.submodule_iSup_eq_top at hι
    simp_rw +singlePass [iSup_split _ (· < nilpotencyLength 𝔞 (AdoSpace K 𝔞)), not_lt] at hι
    apply_fun Submodule.map (mkAlgHom K 𝔞).toLinearMap at hι
    apply_fun Submodule.map (nilSubmodule K 𝔞).mkQ at hι
    simp_rw [Submodule.map_sup, h, sup_bot_eq, Submodule.map_top,
      (mkAlgHom K 𝔞).toLinearMap.range_eq_top_of_surjective (mkAlgHom_surjective _ _),
      Submodule.map_top, Submodule.range_mkQ] at hι
    exact hι
  simp_rw [← lengthSubmodule.eq_1, lengthSubmodule_nilpotenctLength,
    nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span, Submodule.span_eq_bot,
    forall_mem_image, mem_ofPred]
  rintro _ ⟨n, f, hn, rfl⟩
  simp_rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mkAlgHom_tprod_mem_nilSubmodule f hn]

lemma nilSubmodule_le_ker_lift_toEnd_adoSpace [IsAdo K 𝔞] [LieRing.IsNilpotent 𝔞] :
    nilSubmodule K 𝔞 ≤ LinearMap.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))).toLinearMap := by
  simp_rw [nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.span_le, ofPred_subset,
    SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rintro _ ⟨n, f, hn, rfl⟩
  simp_rw [nilpotencyLength_le_iff K, SetLike.ext_iff, LieSubmodule.mem_bot] at hn
  simp_rw [DFunLike.ext_iff, LinearMap.zero_apply, ← hn]
  intro x
  conv =>
    enter [2, 1, 2, 2]
    equals List.prod (List.map (TensorAlgebra.ι K) (List.ofFn f)) => simp [comp_def]
  simp_rw [map_list_prod, List.map_map, comp_def, lift_ι_apply']
  convert list_prod_map_toEnd_apply_mem_lowerCentralSeries K (List.ofFn f) x
  simp

variable (K 𝔞) in
lemma injective_quotient_mk_nilSubmodule [IsAdo K 𝔞] [LieRing.IsNilpotent 𝔞] :
    Injective (fun x ↦
      (Submodule.Quotient.mk (.ι K x) : UniversalEnvelopingAlgebra K 𝔞 ⧸ nilSubmodule K 𝔞)) := by
  apply Function.Injective.of_comp
      (f := (nilSubmodule K 𝔞).liftQ (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))).toLinearMap
        nilSubmodule_le_ker_lift_toEnd_adoSpace)
  simpa [comp_def] using IsFaithful.injective_toEnd

-- TODO: `UniversalEnvelopingAlgebra` 名前空間に移動
@[simps toSubmodule]
noncomputable def nilLieSubmodule [IsAdo K 𝔞] :
    LieSubmodule K (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  toSubmodule := nilSubmodule K 𝔞
  lie_mem {x a} ha := by
    obtain ⟨x₁, x₂⟩ := x
    conv at ha => equals a ∈ nilSubmodule K 𝔞 => simp
    conv => equals ι K x₁ * a + leftLieUE ψ x₂ a ∈ nilSubmodule K 𝔞 =>
      rw [Submodule.mem_carrier, SetLike.mem_coe]; simp [lieUE_def]
    simp [- ι_apply, add_mem, ha]

end LieAlgebra.SemiDirectSum

variable [IsAdo K 𝔞]

abbrev NilStepAdoSpace :=
  UniversalEnvelopingAlgebra K 𝔞 ⧸ nilLieSubmodule ψ

namespace NilStepAdoSpace

attribute [local instance 100] LieRing.ofAssociativeRing

instance [FiniteDimensional K 𝔞] : FiniteDimensional K (NilStepAdoSpace ψ) :=
  inferInstanceAs (FiniteDimensional K (UniversalEnvelopingAlgebra K 𝔞 ⧸ nilSubmodule K 𝔞))

lemma isFaithful_nilStepAdoSpace [LieRing.IsNilpotent 𝔞]
    (hc : center K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (inl ψ)) :
    IsFaithful K (center K (𝔞 ⋊⁅ψ⁆ 𝔥)) (NilStepAdoSpace ψ) := by
  suffices h : IsFaithful K (idealRange (inl ψ)) (NilStepAdoSpace ψ) by
    rw [isFaithful_iff] at h ⊢
    replace h := h.comp (LieSubmodule.inclusion_injective hc)
    convert h using 1
    ext x a
    simp
  simp_rw [isFaithful_iff', (equivIdealRangeInl ψ).surjective.forall, LieEquiv.coe_coe,
    EmbeddingLike.map_eq_zero_iff]
  intro x hx
  specialize hx (LieSubmodule.Quotient.mk 1)
  simp_rw [coe_bracket_of_module, Quotient.lie_bracket_mk, equivIdealRangeInl_apply_coe,
    inl_lieUE, bracket_eq, mul_one] at hx
  conv_rhs at hx => equals LieSubmodule.Quotient.mk (ι K 0) => simp
  exact injective_quotient_mk_nilSubmodule K 𝔞 hx

local instance : IsNilpotent (idealRange (inl ψ)) (NilStepAdoSpace ψ) := by
  suffices h : ∀ k,
      ((idealRange (inl ψ)).lcs (UniversalEnvelopingAlgebra K 𝔞) k).toSubmodule ≤
        lengthSubmodule K 𝔞 k by
    change IsNilpotent (idealRange (inl ψ)).toLieSubalgebra
      (_ ⧸ (nilLieSubmodule ψ).restr (idealRange (inl ψ)))
    simp_rw [isNilpotent_quotient_iff, ← toSubmodule_le_toSubmodule]
    conv =>
      enter [1, k, 1, 1]
      change lowerCentralSeries K (idealRange (inl ψ)) (UniversalEnvelopingAlgebra K 𝔞) k
    simp_rw [← coe_lcs_eq, restr_toSubmodule, toSubmodule_le_toSubmodule]
    existsi nilpotencyLength 𝔞 (AdoSpace K 𝔞)
    specialize h (nilpotencyLength 𝔞 (AdoSpace K 𝔞))
    simp_rw [lengthSubmodule_nilpotenctLength, ← nilLieSubmodule_toSubmodule ψ,
      toSubmodule_le_toSubmodule] at h
    exact h
  intro k
  induction k with
  | zero => simp
  | succ n hn =>
    simp_rw [LieIdeal.lcs_succ, lieIdeal_oper_eq_linear_span',
      ← exists_prop (a := _ ∈ idealRange (inl ψ)), Subtype.exists', Submodule.span_le,
      ofPred_subset, SetLike.mem_coe, (equivIdealRangeInl ψ).surjective.exists, LieEquiv.coe_coe]
    rintro _ ⟨x, a, ha, rfl⟩
    conv => equals ⁅x, a⁆ ∈ lengthSubmodule K 𝔞 (n + 1) =>
      rw [equivIdealRangeInl_apply_coe, inl_lieUE]
    simp_rw [IsConcreteLE.le_iff, mem_toSubmodule] at hn
    specialize hn ha
    exact bracket_𝔞_mem_lengthSubmodule_succ_of_mem n x a hn

local instance [LieRing.IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥)] :
    IsNilpotent (LieHom.range (inr ψ)) (NilStepAdoSpace ψ) := by
  suffices h : ∀ k,
      (lowerCentralSeries K (LieHom.range (inr ψ)) (UniversalEnvelopingAlgebra K 𝔞) k).toSubmodule ≤
        depthSubmodule ψ k by
    change IsNilpotent (LieHom.range (inr ψ)) (_ ⧸ (nilLieSubmodule ψ).restr (LieHom.range (inr ψ)))
    simp_rw [isNilpotent_quotient_iff, ← toSubmodule_le_toSubmodule, restr_toSubmodule]
    existsi depthLimit ψ
    specialize h (depthLimit ψ)
    grw [depthSubmodule_depthLimit_le_nilSubmodule, ← nilLieSubmodule_toSubmodule ψ] at h
    exact h
  intro k
  induction k with
  | zero => simp
  | succ n hn =>
    simp_rw [lowerCentralSeries_succ, lieIdeal_oper_eq_linear_span', mem_top, true_and,
      Submodule.span_le, ofPred_subset, SetLike.mem_coe,
      (equivRangeInr ψ).surjective.exists, LieEquiv.coe_coe]
    rintro _ ⟨x, a, ha, rfl⟩
    conv => equals leftLieUE ψ x a ∈ depthSubmodule ψ (n + 1) =>
      rw [LieSubalgebra.coe_bracket_of_module, equivRangeInr_apply_coe, inr_lieUE]
    simp_rw [IsConcreteLE.le_iff, mem_toSubmodule] at hn
    specialize hn ha
    exact leftLieUE_mem_depthSubmodule_succ_of_mem ψ n x a hn

instance [LieRing.IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥)] : IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥) (NilStepAdoSpace ψ) := by
  conv =>
    equals IsNilpotent ↥((inr ψ).range ⊔ (idealRange (inl ψ)).toLieSubalgebra)
      (NilStepAdoSpace ψ) =>
    have h : (inr ψ).range ⊔ (idealRange (inl ψ)).toLieSubalgebra = ⊤
    · simp [← LieSubalgebra.toSubmodule_inj, (isInnerSemiDirectSum_self ψ).codisjoint.symm.eq_top,
        - range_toSubmodule]
    simp [h]
  infer_instance

end NilStepAdoSpace

end Step

lemma LieAlgebra.IsAdo.semiDirectSum_of_isNilpotent {𝔞 𝔥 : Type*}
    [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
    [FiniteDimensional K 𝔞] [FiniteDimensional K 𝔥] [IsAdo K 𝔞]
    (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞) [LieRing.IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥)]
    (hc : center K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (inl ψ).idealRange) :
    IsAdo K (𝔞 ⋊⁅ψ⁆ 𝔥) := by
  have := (inl_injective ψ).lieAlgebra_isNilpotent
  have := NilStepAdoSpace.isFaithful_nilStepAdoSpace ψ hc
  exact .of_isNilpotent_of_isFaithful_center (NilStepAdoSpace ψ)

lemma LieAlgebra.IsAdo.of_isInnerSemiDirectSum_of_isNilpotent
    (𝔞 : LieIdeal K 𝔫) (𝔥 : LieSubalgebra K 𝔫)
    (hi : IsInnerSemiDirectSum 𝔞 𝔥) (hc : center K 𝔫 ≤ 𝔞) [IsAdo K 𝔞] : IsAdo K 𝔫 := by
  rw [(lieEquivLieSubalgebra hi).symm.isAdo_iff]
  have := (lieEquivLieSubalgebra hi).injective.lieAlgebra_isNilpotent
  apply (LieIdeal.map_mono (f := (lieEquivLieSubalgebra hi).symm.toLieHom)).imp at hc
  rw [map_equiv_center] at hc
  conv_rhs at hc => equals idealRange (inl ((LieDerivation.adoIdeal 𝔞).comp 𝔥.incl)) =>
    ext ⟨x, y⟩
    have h : y.1 ∈ 𝔞 ↔ y = 0 :=
      Submodule.mem_left_iff_eq_zero_of_disjoint hi.disjoint
    simp [add_mem_cancel_left, eq_comm (a := 0) (b := y), h]
  exact .semiDirectSum_of_isNilpotent _ hc

public instance LieAlgebra.IsAdo.of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing 𝔫 with
  | zero => rw [finrank_zero_iff] at hn; exact .intro Unit
  | succ n hin =>
    by_cases h𝔫 : IsLieAbelian 𝔫
    case pos => exact .of_isLieAbelian
    rsuffices ⟨𝔞, 𝔥, hi, hc, _⟩ : ∃ (𝔞 : LieIdeal K 𝔫) (𝔥 : LieSubalgebra K 𝔫),
        IsInnerSemiDirectSum 𝔞 𝔥 ∧ center K 𝔫 ≤ 𝔞 ∧ IsAdo K 𝔞
    · exact .of_isInnerSemiDirectSum_of_isNilpotent 𝔞 𝔥 hi hc
    obtain ⟨𝔞, rfl, h𝔞⟩ := exists_for_nilStepAdoData_of_not_isLieAbelian K 𝔫 n hn h𝔫
    specialize hin rfl
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔫, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      rw [← Submodule.finrank_add_eq_of_isCompl h𝔥', finrank_toSubmodule,
        Nat.add_left_cancel_iff] at hn
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨𝔞, 𝔥, h𝔥₁.isInnerSemidirectSum, h𝔞, hin⟩
