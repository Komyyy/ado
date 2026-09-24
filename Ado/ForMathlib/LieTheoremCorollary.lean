/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieBaseChange
public import Ado.ForMathlib.MatrixTriangular

/-!
## Lie の定理の重要な系
-/

section LieTheoremCorollary

open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    rw [finrank_eq_zero_iff_of_free] at hn
    simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
  | succ n hin =>
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    let V₀ : LieSubmodule K L V :=
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

instance LieModule.isNilpotent_derivedSeries_one_of_isAlgClosed (K L)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [FiniteDimensional K L] : IsNilpotent (derivedSeries K L 1) L := by
  obtain ⟨b, hb⟩ := exists_basis_isUpperTriangular_of_isAlgClosed K L L
  simp_rw [LieModule.isNilpotent_iff_forall (R := K), SetLike.forall, LieIdeal.toEnd_mk,
    ← LinearMap.isNilpotent_toMatrix_iff b]
  intro x hx
  replace hx : ∀ i j, j ≤ i → toMatrix b b (toEnd K L L x) i j = 0
  · conv at hx =>
      conv => equals x ∈ (derivedSeries K L 1 : Submodule K L) => simp
      equals x ∈ Submodule.span K {x : L | ∃ (x₁ x₂ : L), ⁅x₁, x₂⁆ = x} =>
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
  generalize toMatrix b b (toEnd K L L x) = A at hx ⊢
  clear * - x A hx
  suffices h : ∀ (i j : Fin (finrank K L)) (n : ℕ), j < i + n → (A ^ n) i j = 0
  · existsi finrank K L; ext i j; apply h; lia
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

public instance LieModule.isNilpotent_derivedSeries_one (K L)
    [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [IsSolvable L] [FiniteDimensional K L] :
    IsNilpotent (derivedSeries K L 1) L := by
  have h :=
    isNilpotent_derivedSeries_one_of_isAlgClosed (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] L)
  simp_rw [isNilpotent_iff (AlgebraicClosure K), ← toSubmodule_eq_bot, ← LieIdeal.coe_lcs_eq,
    toSubmodule_eq_bot, LieAlgebra.derivedSeries_baseChange, LieIdeal.lcs_baseChange,
    ← baseChange_bot, baseChange_inj] at h
  simp_rw [isNilpotent_iff K, ← toSubmodule_eq_bot, ← LieIdeal.coe_lcs_eq, toSubmodule_eq_bot, h]

public instance LieDerivation.isNilpotent_lieSpan_range {K L} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [FiniteDimensional K L] [IsSolvable L] (D : LieDerivation K L L) :
    LieRing.IsNilpotent (lieSpan K L (Set.range D)) := by
  let ψ : K →ₗ⁅K⁆ LieDerivation K L L :=
    LieHom.toSpanSingleton K _ D
  suffices : IsSolvable (L ⋊⁅ψ⁆ K)
  · have hi := isNilpotent_derivedSeries_one K (L ⋊⁅ψ⁆ K)
    replace hi : LieRing.IsNilpotent (derivedSeries K (L ⋊⁅ψ⁆ K) 1) := inferInstance
    refine LieHom.lieIdealMap_injective_of_injective (inl ψ) _ (inl_injective ψ)
      |>.lieAlgebra_isNilpotent (h₁ := ?_)
    apply LieRing.isNilpotent_of_lieIdeal_le _ (derivedSeries K (L ⋊⁅ψ⁆ K) 1)
    conv =>
      equals ∀ (x : L), ⁅inr ψ 1, inl ψ x⁆ ∈
          ⁅(⊤ : LieIdeal K (L ⋊⁅ψ⁆ K)), (⊤ : LieIdeal K (L ⋊⁅ψ⁆ K))⁆ =>
        simp [LieIdeal.map_le_iff_le_comap, Set.range_subset_iff, ψ]
    intro x
    apply lie_mem_lie <;> simp
  suffices h : IsSolvable (derivedSeries K (L ⋊⁅ψ⁆ K) 1)
  · simp only [isSolvable_iff K, LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap,
      LieIdeal.comap_incl_eq_bot, disjoint_iff, ← derivedSeriesOfIdeal_add,
      inf_eq_right.mpr, derivedSeriesOfIdeal_le, le_refl, le_add_self] at h ⊢
    exact h.imp' (· + 1) (fun _ h ↦ h)
  suffices h : derivedSeries K (L ⋊⁅ψ⁆ K) 1 ≤ LieHom.idealRange (inl ψ)
  · apply le_solvable_ideal_solvable h
    rwa [← solvable_iff_equiv_solvable (equivIdealRangeInl ψ)]
  simp [lie_le_iff, trivial_lie_zero]

end LieTheoremCorollary
