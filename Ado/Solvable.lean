/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Nilpotent
public import Ado.ForMathlib.UniversalEnvelopingAlgebraIdeal
public import Ado.ForMathlib.MatrixTriangular

/-!
## 可解 Lie 代数に対する Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section LieTheoremCorollary

open Module LieAlgebra LieSubmodule LieModule LinearMap Matrix

lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K 𝔯 V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing 𝔯] [LieAlgebra K 𝔯] [IsSolvable 𝔯]
    [AddCommGroup V] [Module K V] [LieRingModule 𝔯 V] [LieModule K 𝔯 V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : 𝔯, IsUpperTriangular (toMatrix b b (toEnd K 𝔯 V x)) := by
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    rw [finrank_eq_zero_iff_of_free] at hn
    simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
  | succ n hin =>
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K 𝔯 V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    let V₀ : LieSubmodule K 𝔯 V :=
      { toSubmodule := K ∙ v
        lie_mem {x w} hw := by
          conv at hw => equals ∃ k : K, k • v = w => simp [Submodule.mem_span_singleton]
          obtain ⟨k, rfl⟩ := hw
          simp [hvw, smul_smul, SMulMemClass.smul_mem] }
    have hV₀ : finrank K V₀ = 1 := by
      simp [← finrank_toSubmodule, V₀, finrank_span_singleton hvz]
    replace hV₀ : finrank K (V ⧸ V₀) = n := by simp [hn, hV₀]
    have hvq : (LieSubmodule.Quotient.mk v : V ⧸ V₀) = 0 := by simp [V₀]
    specialize hin (V ⧸ V₀) hV₀
    obtain ⟨b₀, hb₀⟩ := hin
    let bᵥ : Basis Unit K V₀ :=
      Module.Basis.ofRepr
        ((LinearEquiv.coord K V v hvz).trans (Finsupp.uniqueLinearEquiv K K ()).symm)
    have hbv : (bᵥ () : V) = v := by simp [bᵥ, LinearEquiv.toSpanNonzeroSingleton]
    let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
    let b := Basis.reindex (Basis.sumLieQuot bᵥ b₀) e
    existsi b
    intro x
    simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
    simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
    simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]

instance LieModule.isNilpotent_derivedSeries_one_of_isAlgClosed {K 𝔯}
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing 𝔯] [LieAlgebra K 𝔯] [IsSolvable 𝔯]
    [FiniteDimensional K 𝔯] : IsNilpotent (derivedSeries K 𝔯 1) 𝔯 := by
  obtain ⟨b, hb⟩ := exists_basis_isUpperTriangular_of_isAlgClosed K 𝔯 𝔯
  simp_rw [LieModule.isNilpotent_iff_forall (R := K), SetLike.forall, LieIdeal.toEnd_mk,
    ← LinearMap.isNilpotent_toMatrix_iff b]
  intro x hx
  replace hx : ∀ i j, j ≤ i → toMatrix b b (toEnd K 𝔯 𝔯 x) i j = 0
  · conv at hx =>
      conv => equals x ∈ (derivedSeries K 𝔯 1 : Submodule K 𝔯) => simp
      equals x ∈ Submodule.span K {x : 𝔯 | ∃ (x₁ x₂ : 𝔯), ⁅x₁, x₂⁆ = x} =>
        simp [LieSubmodule.lieIdeal_oper_eq_linear_span']
    induction hx using Submodule.span_induction with
    | mem x h =>
      rw [Set.mem_ofPred_eq] at h
      obtain ⟨x₁, x₂, rfl⟩ := h
      intro i j hij
      rw [le_iff_eq_or_lt] at hij
      obtain (rfl | hij) := hij
      case inr =>
        replace hb x₁ x₂ := (hb x₁).mul (hb x₂)
        simp_rw [Matrix.BlockTriangular, id_eq] at hb
        simp [LieRing.of_associative_ring_bracket, LinearMap.toMatrix_mul, hb, hij]
      replace hb x₁ x₂ i := mul_apply_diag_eq_mul_of_isUpperTriangular _ _ (hb x₁) (hb x₂) i
      simp [LieRing.of_associative_ring_bracket, LinearMap.toMatrix_mul, hb, sub_eq_zero,
        iff_true_intro (mul_comm _ _)]
    | zero => simp
    | add x y hx hy hix hiy => simp +contextual [*]
    | smul a x hx hix => simp +contextual [*]
  generalize toMatrix b b (toEnd K 𝔯 𝔯 x) = A at hx ⊢
  clear * - x A hx
  suffices h : ∀ (i j : Fin (finrank K 𝔯)) (n : ℕ), j < i + n → (A ^ n) i j = 0
  · existsi finrank K 𝔯; ext i j; apply h; lia
  intro i j n hij
  induction n generalizing i j with
  | zero => simp [show i ≠ j by lia]
  | succ n hn =>
    simp_rw +singlePass [pow_succ, Matrix.mul_apply,
      ← Finset.sum_filter_add_sum_filter_not _ (fun k ↦ j ≤ k)]
    conv_lhs =>
      enter [1]
      apply_congr
      next => rfl
      next k hk => rw [hx _ _ (by simpa using hk)]
    conv_lhs => equals ∑ k with k < j, (A ^ n) i k * A k j => simp
    conv_lhs =>
      apply_congr
      next => rfl
      next k hk => rw [hn _ _ (by grind)]
    simp

@[instance]
public axiom LieDerivation.isNilpotent_lieSpan_range {K 𝔯} [Field K] [CharZero K] [LieRing 𝔯]
    [LieAlgebra K 𝔯] [FiniteDimensional K 𝔯] [IsSolvable 𝔯] (D : LieDerivation K 𝔯 𝔯) :
    LieRing.IsNilpotent (lieSpan K 𝔯 (Set.range D))

end LieTheoremCorollary

open Set Module LieAlgebra LieModule LieHom LieSubmodule SemiDirectSum UniversalEnvelopingAlgebra
open scoped Pointwise

variable {K 𝔯 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔯] [LieAlgebra K 𝔯] [FiniteDimensional K 𝔯]

-- 可解性の仮定は恐らく外せるが、根基が特性的である事を示すのに手こずったから後回し
-- 注意: 正標数では成り立たない。別ファイルの反例を参照。
lemma LieIdeal.lieIdealOf_nilradical_eq_of_le
    (I : LieIdeal K 𝔯) (hN : nilradical K 𝔯 ≤ I) [IsSolvable I] :
    nilradical K I = lieIdealOf (nilradical K 𝔯) I := by
  apply le_antisymm
  on_goal 2 =>
    simp_rw [← LieIdeal.isNilpotent_iff_le_nilradical,
      (LieIdeal.lieIdealOfEquivOfLe hN).injective.lieAlgebra_isNilpotent]
  rsuffices ⟨J, hJ⟩ : ∃ J : LieIdeal K 𝔯,
      J.toLieSubalgebra = LieSubalgebra.map I.incl (nilradical K I).toLieSubalgebra
  · simp_rw [lieIdealOf, ← toLieSubalgebra_le_toLieSubalgebra, toLieSubalgebra_comap,
      ← LieSubalgebra.map_le_iff_le_comap, ← hJ, toLieSubalgebra_le_toLieSubalgebra,
      ← LieIdeal.isNilpotent_iff_le_nilradical]
    change LieRing.IsNilpotent J.toLieSubalgebra
    simp_rw [hJ]
    apply (LieSubalgebra.equivMapOfInjective
        _ (nilradical K I) I.incl_injective).surjective.lieAlgebra_isNilpotent
  simp_rw [LieSubalgebra.exists_lieIdeal_coe_eq_iff, LieSubalgebra.mem_map, mem_toLieSubalgebra,
    incl_apply]
  rintro x _ ⟨y, hy, rfl⟩
  have hy₂ := (LieDerivation.adIdeal I x).isNilpotent_lieSpan_range
  simp_rw [LieIdeal.isNilpotent_iff_le_nilradical, lieSpan_le, range_subset_iff,
    LieDerivation.adIdeal_apply_apply, SetLike.mem_coe] at hy₂
  existsi ⁅x, y⁆, hy₂ y
  simp

variable [IsSolvable 𝔯]

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
  have : Nontrivial (𝔯 ⧸ nilradical K 𝔯)
  · simp [← finrank_pos_iff (R := K), h𝔯r]
  have h𝔯' := derivedSeries_lt_top_of_solvable K (𝔯 ⧸ nilradical K 𝔯)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔯'
  exact h𝔯'

section Step

variable {𝔞 𝔥 : Type*}
variable [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥] [IsAdo K 𝔞]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)
variable (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (SemiDirectSum.inl ψ))

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K 𝔞) in
noncomputable def annihilatingIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) ⊔ Ideal.span (ι K '' nilradical K 𝔞)
deriving Ideal.IsTwoSided

variable (K 𝔞) in
noncomputable def nilIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  annihilatingIdeal K 𝔞 ^ nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)
deriving Ideal.IsTwoSided

omit [CharZero K] in
lemma nilIdeal_le {I} : nilIdeal K 𝔞 ≤ I ↔
    ∀ l : List (UniversalEnvelopingAlgebra K 𝔞),
      List.length l = nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) →
      (∀ x ∈ l, lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) x = 0 ∨ x ∈ Ideal.span (ι K '' nilradical K 𝔞)) →
          List.prod l ∈ I := by
  have : (Ideal.span (RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) ∪
      Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) :
        Set (UniversalEnvelopingAlgebra K 𝔞))).IsTwoSided := by
    rw [← Ideal.sup_eq_span]; infer_instance
  simp_rw [nilIdeal, annihilatingIdeal, Ideal.sup_eq_span, Ideal.span_pow, Ideal.span_le,
    Set.pow_subset]
  simp

omit [CharZero K] in
variable (K 𝔞) in
lemma nilIdeal_le_ker_lift_toEnd :
    nilIdeal K 𝔞 ≤ RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) := by
  simp_rw [nilIdeal_le, RingHom.mem_ker]
  intro l hll hl
  by_cases! hf₂ : ∃ x ∈ l, lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) x = 0
  case pos =>
    obtain ⟨x, hxl, hx⟩ := hf₂
    rw [map_list_prod]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exists x
  case neg =>
    replace hl x hx := (hl x hx).resolve_left (hf₂ x hx)
    clear hf₂
    revert l hll hl
    conv =>
      equals (Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) : Set (UniversalEnvelopingAlgebra K 𝔞)) ^
          nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) ⊆
            lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) ⁻¹' {0} =>
        simp [Set.pow_subset]
    have : (Ideal.span
        (Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) :
          Set (UniversalEnvelopingAlgebra K 𝔞))).IsTwoSided := by
      rw [Ideal.span_eq]; infer_instance
    simp_rw [← RingHom.ker_eq, ← Ideal.span_le, ← Ideal.span_pow, Ideal.span_eq, Ideal.span_pow,
      Ideal.span_le, RingHom.ker_eq, Set.pow_subset]
    intro l hll hl
    replace hl : l ∈ range (List.map (ι K ∘ ((↑) : nilradical K 𝔞 → 𝔞)))
    · simp_rw [Set.range_list_map, Set.range_comp, Subtype.range_coe_subtype,
        SetLike.setOfPred_mem_eq, Set.mem_ofPred]
      exact hl
    rw [Set.mem_range] at hl
    obtain ⟨l, rfl⟩ := hl
    rw [List.length_map] at hll
    conv =>
      equals ∀ x,
         (List.map (toEnd K (nilradical K 𝔞) (AdoSpace K 𝔞)) l).prod x ∈
            lowerCentralSeries K (nilradical K 𝔞) (AdoSpace K 𝔞)
              (nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)) =>
        simp [← List.prod_hom, Function.comp_def, DFunLike.ext_iff,
          - List.map_subtype, ← LieIdeal.toEnd_eq]
    intro x
    refine list_prod_map_toEnd_apply_mem_lowerCentralSeries K l x
        (nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)) ?_
    simp [hll]

omit [IsAdo K 𝔞] in
lemma range_ψ_le_nilradical
    [FiniteDimensional K 𝔞] [IsSolvable 𝔞] (x : 𝔥) :
    LinearMap.range (ψ x).toLinearMap ≤
      Submodule.restrictScalars K (nilradical K 𝔞).toSubmodule := by
  simp_rw [← SetLike.coe_subset_coe, Submodule.restrictScalars_self, coe_toSubmodule,
    ← LieSubmodule.lieSpan_le, LinearMap.coe_range, LieDerivation.coeFn_coe,
    ← LieIdeal.isNilpotent_iff_le_nilradical]
  infer_instance

variable [FiniteDimensional K 𝔞] [IsSolvable 𝔞]

lemma range_leftLieUE_le_annihilatingIdeal (x : 𝔥) :
    LinearMap.range (leftLieUE ψ x) ≤ Submodule.restrictScalars K (annihilatingIdeal K 𝔞) := by
  simp_rw [← Submodule.map_top,
    ← (mkAlgHom K 𝔞).toLinearMap.range_eq_top_of_surjective (mkAlgHom_surjective K 𝔞),
    ← Submodule.map_top, ← TensorAlgebra.span_tprod_eq_top, Submodule.map_span, Submodule.span_le,
    Set.subset_def, Set.forall_mem_image, Set.mem_ofPred, Submodule.coe_restrictScalars,
    AlgHom.toLinearMap_apply, SetLike.mem_coe]
  rintro _ ⟨n, f, rfl⟩
  simp_rw [leftLieUE_mkAlgHom, leftLieUEAux_tprod, map_sum]
  apply sum_mem
  rintro ⟨i, hi⟩ -
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = i + (m + 1) := by existsi n - (i + 1); lia
  cases f using Fin.appendCases with | append f g
  cases g using Fin.consCases with | cons y g
  simp_rw [show Fin.mk i hi = Fin.natAdd i ⟨0, by lia⟩ by ext; simp, Fin.update_append_natAdd,
    Fin.append_right, Fin.mk_zero, Fin.update_cons_zero, Fin.cons_zero,
    ← TensorAlgebra.tprod_mul_tprod, ← TensorAlgebra.ι_mul_tprod, map_mul, ← ι_apply]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_right
  simp_rw [annihilatingIdeal, Ideal.sup_eq_span, ← SetLike.mem_coe]
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_union_right
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_image_of_mem
  simp_rw +singlePass [SetLike.mem_coe, ← mem_toSubmodule, ← Submodule.restrictScalars_mem K]
  apply mem_of_le_of_mem (range_ψ_le_nilradical ψ x)
  simp

lemma leftLieUE_mem_annihilatingIdeal (x : 𝔥) {a : UniversalEnvelopingAlgebra K 𝔞} :
    leftLieUE ψ x a ∈ annihilatingIdeal K 𝔞 := by
  have h := range_leftLieUE_le_annihilatingIdeal ψ x
  rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff'] at h
  simp_all

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

variable [FiniteDimensional K 𝔞] [IsSolvable 𝔞]

abbrev SolStepAdoSpace :=
  UniversalEnvelopingAlgebra K 𝔞 ⧸ nilLieSubmodule ψ

namespace SolStepAdoSpace

attribute [local instance 100]
  LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

instance isFaithful_idealRange_solStepAdoSpace :
    IsFaithful K (idealRange (inl ψ)) (SolStepAdoSpace ψ) := by
  simp_rw [isFaithful_iff', (equivIdealRangeInl ψ).surjective.forall, LieEquiv.coe_coe,
    LieIdeal.coe_bracket_of_module, equivIdealRangeInl_apply_coe,
    (LieSubmodule.Quotient.surjective_mk' _).forall, ← LieModuleHom.map_lie, inl_lieUE,
    LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero',
    EmbeddingLike.map_eq_zero_iff]
  intro x hx
  suffices h : ∀ y : AdoSpace K 𝔞, ⁅x, y⁆ = 0
  · apply LieModule.ext_of_isFaithful (R := K) (M := AdoSpace K 𝔞)
    simpa using h
  intro y
  specialize hx 1
  grw [bracket_eq, ι_apply, mul_one] at hx
  apply mem_of_le_of_mem (nilIdeal_le_ker_lift_toEnd K 𝔞) at hx
  simp_rw [RingHom.mem_ker, lift_ι_apply', toEnd_eq_zero_iff] at hx
  subst hx
  simp

lemma isFaithful_center_solStepAdoSpace
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (inl ψ)) :
    IsFaithful K (center K (𝔞 ⋊⁅ψ⁆ 𝔥)) (SolStepAdoSpace ψ) where
  injective_toEnd := by
    convert
      (isFaithful_idealRange_solStepAdoSpace ψ).injective_toEnd.comp
        (LieIdeal.inclusion_injective (center_le_nilradical.trans hn))
    ext
    simp

lemma isNilpotent_nilradical_solStepAdoSpace [FiniteDimensional K 𝔥]
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (inl ψ)) :
    IsNilpotent (nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥)) (SolStepAdoSpace ψ) := by
  have : IsSolvable (idealRange (SemiDirectSum.inl ψ)) :=
    (equivIdealRangeInl ψ).surjective.lieAlgebra_isSolvable
  simp_rw [LieModule.isNilpotent_iff_forall (R := K),
    LieIdeal.lieIdealOfEquivOfLe hn |>.surjective.forall, LieEquiv.coe_coe, LieIdeal.toEnd_eq,
    LieIdeal.lieIdealOfEquivOfLe_toFun_coe,
    SetLike.forall (p := LieIdeal.lieIdealOf (nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥))
      (idealRange (SemiDirectSum.inl ψ))),
    ← LieIdeal.lieIdealOf_nilradical_eq_of_le _ hn, ← map_equiv_nilradical (equivIdealRangeInl ψ),
    (equivIdealRangeInl ψ).surjective.forall, LieEquiv.coe_coe, LieEquiv.mem_map_equiv,
    LieEquiv.symm_apply_apply, equivIdealRangeInl_apply_coe]
  intro x hx
  exists nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)
  simp_rw [DFunLike.ext_iff, (LieSubmodule.Quotient.surjective_mk' _).forall, toEnd_pow_apply_map,
    LinearMap.zero_apply, LieSubmodule.Quotient.mk_eq_zero, toEndUE_inl, toEnd_eq,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
  intro a
  apply Ideal.mul_mem_right
  simp_rw [nilIdeal, annihilatingIdeal, Ideal.pow_eq_span_pow_set, ← SetLike.mem_coe,
    Ideal.sup_eq_span]
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.pow_mem_pow
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_union_right
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_image_of_mem
  simp [hx]

@[instance]
public axiom finiteDimensional_solStepAdoSpace [FiniteDimensional K 𝔥] :
    FiniteDimensional K (SolStepAdoSpace ψ)

end SolStepAdoSpace

end Step

-- 一般の場合でも使うので公開
public lemma LieAlgebra.IsAdo.semiDirectSum_of_isSolvable {𝔞 𝔥 : Type*}
    [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
    [FiniteDimensional K 𝔞] [FiniteDimensional K 𝔥] [IsAdo K 𝔞]
    (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞) [IsSolvable 𝔞]
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (inl ψ).idealRange) :
    IsAdo K (𝔞 ⋊⁅ψ⁆ 𝔥) := by
  have := SolStepAdoSpace.isFaithful_center_solStepAdoSpace ψ hn
  have := SolStepAdoSpace.isNilpotent_nilradical_solStepAdoSpace ψ hn
  exact .of_isNilpotent_of_isFaithful_center (SolStepAdoSpace ψ)

lemma LieAlgebra.IsAdo.of_isInnerSemiDirectSum_of_isSolvable
    (𝔞 : LieIdeal K 𝔯) (𝔥 : LieSubalgebra K 𝔯)
    (hi : IsInnerSemiDirectSum 𝔞 𝔥) (hn : nilradical K 𝔯 ≤ 𝔞) [IsAdo K 𝔞] : IsAdo K 𝔯 := by
  rw [(lieEquivLieSubalgebra hi).symm.isAdo_iff]
  have := (lieEquivLieSubalgebra hi).injective.lieAlgebra_isSolvable
  apply (LieIdeal.map_mono (f := (lieEquivLieSubalgebra hi).symm.toLieHom)).imp at hn
  rw [map_equiv_nilradical] at hn
  conv_rhs at hn => equals idealRange (inl ((LieDerivation.adIdeal 𝔞).comp 𝔥.incl)) =>
    ext ⟨x, y⟩
    have h : y.1 ∈ 𝔞 ↔ y = 0 :=
      Submodule.mem_left_iff_eq_zero_of_disjoint hi.disjoint
    simp [add_mem_cancel_left, eq_comm (a := 0) (b := y), h]
  exact .semiDirectSum_of_isSolvable _ hn

public local instance LieAlgebra.IsAdo.of_isSolvable : IsAdo K 𝔯 := by
  generalize hn : finrank K (𝔯 ⧸ nilradical K 𝔯) = n
  induction n generalizing 𝔯 with
  | zero =>
    rw [finrank_quotient, Nat.sub_eq_zero_iff_le, ← not_lt, LieIdeal.finrank_lt_iff,
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
      simp_rw [← hn𝔞, finrank_quotient, 𝔞.lieIdealOf_nilradical_eq_of_le h𝔞,
        LieIdeal.finrank_lieIdealOf _ _ h𝔞, ← Submodule.finrank_add_eq_of_isCompl h𝔥',
        finrank_toSubmodule] at hn
      conv at hn => equals finrank K 𝔥' = 1 => grind only [LieIdeal.finrank_mono h𝔞]
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨𝔞, 𝔥, h𝔥₁.isInnerSemidirectSum, h𝔞, hin⟩
