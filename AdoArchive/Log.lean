/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Batteries.Data.List.Scan
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Banach 空間上の連続自己線形同型の対数

大学の Lie 群の講義で、行列の対数を使う場面があり、まだ行列の指数は知らなかったので、ついでに無限次元に拡張して
対数の存在を示した。
-/

public section

section ListProd

variable {M N : Type*} [Monoid M] [MulOneClass N] [MulAction M N]
variable [IsScalarTower M N N] [SMulCommClass M N N]

namespace List

@[to_fun prod_ofFn_fun_smul]
lemma prod_ofFn_smul {n} (f : Fin n → M) (g : Fin n → N) :
    prod (ofFn (f • g)) = prod (ofFn f) • prod (ofFn g) := by
  simp_rw [Pi.smul_def']
  induction f using Fin.consInduction with
  | elim0 => simp
  | cons x f h =>
    cases g using Fin.consCases with | cons y g
    simp [h, mul_smul_mul_comm]

end List

end ListProd

section PowerSeries

open Function Set FormalMultilinearSeries PowerSeries Finset

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalRing E]

namespace PowerSeries

noncomputable def toFMS (P : 𝕜⟦X⟧) : FormalMultilinearSeries 𝕜 E E :=
  ofScalars E (coeff · P)

variable (P : 𝕜⟦X⟧)

variable {E} in
@[simp]
lemma toFMS_apply (n : ℕ) (v : Fin n → E) :
    toFMS E P n v = coeff n P • List.prod (List.ofFn v) := by
  simp [toFMS, ofScalars]

@[simp]
lemma toFMS_add (P Q : 𝕜⟦X⟧) : toFMS E (P + Q) = toFMS E P + toFMS E Q := by
  ext; simp [add_smul]

@[simp]
lemma toFMS_sub (P Q : 𝕜⟦X⟧) : toFMS E (P - Q) = toFMS E P - toFMS E Q := by
  ext; simp [sub_smul]

@[simp]
lemma toFMS_X (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedRing E] [NormedAlgebra 𝕜 E] : toFMS E (X : 𝕜⟦X⟧) = .id 𝕜 E 0 := by
  ext n v; match n with | 0 | 1 | n + 2 => simp [coeff_X]

@[simp]
lemma toFMS_one (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedRing E] [NormedAlgebra 𝕜 E] :
    toFMS E (1 : 𝕜⟦X⟧) = constFormalMultilinearSeries 𝕜 E 1 := by
  ext n v; cases n <;> simp

lemma removeZero_toFMS (P : 𝕜⟦X⟧) : removeZero (toFMS E P) = toFMS E (P - C (constantCoeff P)) := by
  ext n v; cases n <;> simp

lemma toFMS_subst (P Q : 𝕜⟦X⟧) (hP : HasSubst P) :
    toFMS E (subst P Q) = FormalMultilinearSeries.comp (toFMS E Q) (toFMS E P) := by
  ext n v
  conv_lhs =>
    calc
      _ = ∑ᶠ k : ℕ, ∑ i ∈ finsuppAntidiag (range k) n,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        simp [coeff_subst' hP, coeff_pow, mul_sum, finsum_smul, sum_smul]
      _ = ∑ᶠ k : ℕ, ∑ i ∈ finsuppAntidiag (range k) n with ∀ j ∈ range k, 0 < i j,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        congr! 2 with k
        symm
        apply sum_eq_of_subset (filter_subset _ _)
        intro i hi₁ hi₂
        rw [mem_filter] at hi₂
        push Not at hi₂
        apply hi₂ at hi₁
        obtain ⟨j, hj, hj₂⟩ := hi₁
        rw [nonpos_iff_eq_zero] at hj₂
        suffices h : coeff (i j) P = 0 by rw [prod_eq_zero hj (by simp [h])]; simp
        simp_rw [hj₂, coeff_zero_eq_constantCoeff_apply, ← isNilpotent_iff_eq_zero, constantCoeff,
          hP]
      _ = ∑ k ≤ n, ∑ i ∈ finsuppAntidiag (range k) n with ∀ j ∈ range k, 0 < i j,
          (coeff k Q * ∏ j ∈ range k, coeff (i j) P) • (List.prod (List.ofFn v)) := by
        apply finsum_eq_finsetSum_of_support_subset
        simp_rw +singlePass [← Set.compl_subset_compl, compl_support, coe_Iic, compl_Iic,
          Finset.mem_range, ← Set.Ioi_def, Set.ofPred_subset_ofPred]
        intro m hm
        convert Finset.sum_empty
        simp_rw [Finset.eq_empty_iff_forall_notMem, mem_filter, and_comm (a := _ ∈ _), not_and,
          mem_finsuppAntidiag, Nat.lt_iff_add_one_le (m := 0), zero_add]
        intro i hi
        simp_rw [← Finset.mem_range] at hi
        apply Finset.sum_le_sum at hi
        grw [sum_const, card_range, smul_eq_mul, mul_one, ← hm] at hi
        simp_rw [Classical.not_and_iff_not_or_not, hi.ne', not_false_iff, true_or]
      _ =
          let (k : ℕ) : Fintype ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} :=
            Fintype.ofEquiv _ (finsuppAntidiagEquivSubtype (range k) n)
          ∑ k ≤ n,
            ∑ b ∈ {b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n}.toFinset with
                ∀ j, 0 < b j, (coeff k Q * ∏ j, coeff (b j) P) • (List.prod (List.ofFn v)) := by
        extract_lets
        simp_rw +singlePass [Finset.sum_filter, ← Finset.sum_coe_sort (finsuppAntidiag (range _) n),
          ← Finset.sum_set_coe, ← Finset.sum_filter]
        congr! 1 with k hk
        apply sum_equiv (finsuppAntidiagEquivSubtype (range k) n)
        · simp
        · simp_rw [Finset.finsuppAntidiagEquivSubtype_apply_coe, Finsupp.subtypeDomain_apply,
            ← Finset.prod_coe_sort (range k), forall_true_iff]
      _ =
          let (k : ℕ) : Fintype ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} :=
            Fintype.ofEquiv _ (finsuppAntidiagEquivSubtype (range k) n)
          let e (k : ℕ) : ↥{b : ↥(range k) →₀ ℕ | Finsupp.sum b (fun _ ↦ id) = n} ≃
              ↥{b : Fin k → ℕ | ∑ i, b i = n} :=
            { toFun x :=
                ⟨fun i ↦ x.1 ⟨i.1, by simp⟩, by
                  simpa [Finsupp.sum_fintype, ← sum_attach (range k),
                    sum_fin_eq_sum_range, - Subtype.coe_prop,
                    show ∀ x : range k, x.1 < k by simp] using x.2⟩
              invFun x :=
                ⟨Finsupp.equivFunOnFinite.symm
                    (fun i ↦ x.1 ⟨i.1, by simpa [- SetLike.coe_mem] using i.2⟩), by
                  simpa [Finsupp.sum_fintype, ← sum_attach (range k),
                    sum_fin_eq_sum_range, - Subtype.coe_prop,
                    show ∀ x : range k, x.1 < k by simp] using x.2⟩ }
          let (k : ℕ) : Fintype ↥{b : Fin k → ℕ | ∑ i, b i = n} :=
            Fintype.ofEquiv _ (e k)
          ∑ k ≤ n,
            ∑ b ∈ {b : Fin k → ℕ | ∑ i, b i = n}.toFinset with
                ∀ j, 0 < b j, (coeff k Q * ∏ j, coeff (b j) P) • (List.prod (List.ofFn v)) := by
        extract_lets _ _ e _
        congr! 1 with k hk
        simp_rw [Finset.sum_filter, ← Finset.sum_set_coe, ← Finset.sum_filter]
        have he i j : (e k i).1 j = i.1 ⟨j.1, by simp⟩ := rfl
        apply sum_equiv (e k)
        · simp [he, Fin.forall_iff]
        · simp [he, prod_fin_eq_prod_range, ← prod_attach (range k),
            show ∀ x : range k, x.1 < k by simp]
      _ = ∑ c : Composition n,
          (coeff c.length Q * ∏ j, coeff (c.blocksFun j) P) • (List.prod (List.ofFn v)) := by
        extract_lets
        symm
        rw [sum_sigma']
        let e : Composition n ≃
            Finset.sigma (Finset.Iic n) (fun k ↦ filter (fun b ↦ ∀ j, 0 < b j)
              {b : Fin k → ℕ | ∑ i, b i = n}.toFinset) :=
          { toFun c := ⟨⟨c.length, c.blocksFun⟩, by simp [Nat.lt_iff_add_one_le]⟩
            invFun x :=
              { blocks := List.ofFn x.1.2
                blocks_pos {j} hj := by
                  have h := x.2
                  rw [mem_sigma, mem_filter] at h
                  rw [List.mem_ofFn] at hj
                  obtain ⟨j, rfl⟩ := hj
                  simp [h]
                blocks_sum := by
                  have h := x.2
                  rw [mem_sigma, mem_filter, mem_toFinset, Set.mem_ofPred] at h
                  simp [List.sum_ofFn, h] }
            left_inv c := by ext : 1; simp
            right_inv x := by
              ext <;> simp [Composition.length, Composition.blocksFun, Fin.heq_fun_iff] }
        simp_rw [← sum_attach (Finset.sigma _ _)]
        apply sum_equiv e
        · simp
        · simp [e]
  conv_rhs =>
    tactic =>
      simp_rw [FormalMultilinearSeries.comp, _root_.sum_apply, compAlongComposition_apply,
        toFMS_apply]
      unfold applyComposition
      simp_rw [toFMS_apply, List.prod_ofFn_fun_smul, smul_smul, Fin.prod_ofFn,
        List.ofFn_comp' (g := List.prod), ← List.prod_flatten, ← List.map_ofFn,
        List.ofFn_comp' (g := List.map v), ← List.map_flatten]
  rw [List.ofFn_eq_map]
  congr! with c -
  apply List.ext_getElem
  · simp [List.sum_ofFn]
  · intro j hj₁ hj₂
    ext
    simp_rw [List.getElem_finRange, Fin.val_cast]
    symm
    simp_rw -zeta [List.getElem_flatten]
    extract_lets k₁ hk₁ k₂ hk₂
    subst hk₁ hk₂
    simp_rw [List.getElem_ofFn]
    have hk₁ : k₁ = c.index ⟨j, by simpa using hj₁⟩ := by
      simp_rw [k₁, List.map_ofFn, comp_def, List.length_ofFn]
      rw [Nat.sub_eq_iff_eq_add (by simp [Nat.add_one_le_iff]), List.findIdx_eq (by simp)]
      constructor
      · rw [decide_eq_true_iff, List.getElem_partialSums, Composition.ofFn_blocksFun,
          ← Composition.sizeUpTo]
        apply c.lt_sizeUpTo_index_succ ⟨j, by simpa using hj₁⟩
      · intro j₂ hj₂
        rw [Nat.lt_add_one_iff] at hj₂
        grw [decide_eq_false_iff_not, gt_iff_lt, not_lt, List.getElem_partialSums,
          Composition.ofFn_blocksFun, ← Composition.sizeUpTo, c.monotone_sizeUpTo.imp hj₂]
        apply c.sizeUpTo_index_le ⟨j, by simpa using hj₁⟩
    have hk₂ : k₂ = c.invEmbedding ⟨j, by simpa using hj₁⟩ := by
      simp_rw [k₂, List.length_flatten, List.map_take, List.map_ofFn, comp_def, List.length_ofFn,
        Composition.ofFn_blocksFun]
      rw [← Composition.sizeUpTo]
      simp_rw [Composition.coe_invEmbedding, hk₁]
    simp_rw [c.coe_embedding]
    rw [hk₁, hk₂, ← c.coe_embedding, c.embedding_comp_inv]

end PowerSeries

end PowerSeries

section Log

open FormalMultilinearSeries PowerSeries Filter
open scoped NNReal Topology

namespace NormedSpace

section Radius

variable (𝕜 𝔸 : Type*)
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
variable [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜]

lemma radius_logSeries_ge_one : 1 ≤ radius (logSeries 𝕜 𝔸) := by
  rw [logSeries_eq_ofScalars]
  convert inv_le_ofScalars_radius_of_tendsto 𝔸 _ (r := 1) (by positivity) ?_
  · simp
  convert_to Tendsto (fun n : ℕ ↦ ‖((↑n / (↑n + 1)) : 𝕜)‖) atTop (𝓝 ‖(1 : 𝕜)‖)
  · simp [inv_mul_eq_div]
  · simp
  apply Tendsto.norm
  exact_mod_cast tendsto_natCast_div_add_atTop (1 : 𝕜)

@[simp]
lemma radius_logSeries_eq_one [NormOneClass 𝔸] : radius (logSeries 𝕜 𝔸) = 1 := by
  rw [logSeries_eq_ofScalars]
  convert ofScalars_radius_eq_inv_of_tendsto 𝔸 _ (r := 1) (by positivity) ?_
  · simp
  convert_to Tendsto (fun n : ℕ ↦ ‖((↑n / (↑n + 1)) : 𝕜)‖) atTop (𝓝 ‖(1 : 𝕜)‖)
  · simp [inv_mul_eq_div]
  · simp
  apply Tendsto.norm
  exact_mod_cast tendsto_natCast_div_add_atTop (1 : 𝕜)

end Radius

section PowerSeries

variable (𝕜 𝔸 : Type*)
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
variable [CharZero 𝕜]

@[simp]
lemma _root_.PowerSeries.toFMS_exp : toFMS 𝔸 (.exp 𝕜) = expSeries 𝕜 𝔸 := by
  simp [expSeries_eq_ofScalars, toFMS]

@[simp]
lemma _root_.PowerSeries.toFMS_log : toFMS 𝔸 (.log 𝕜) = logSeries 𝕜 𝔸 := by
  convert_to ofScalars 𝔸 (fun n ↦ if n = 0 then (0 : 𝕜) else (-1) ^ (n + 1) / (n : 𝕜)) =
      ofScalars 𝔸 (fun n ↦ (-1) ^ (n + 1) / (n : 𝕜))
  · simp [toFMS]
  · simp [logSeries_eq_ofScalars]
  congr! 2 with n
  split_ifs <;> simp [*]

end PowerSeries

section Comp

variable (𝕜 𝔸 : Type*)
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
variable [CharZero 𝕜]

@[simp]
lemma comp_expSeries_logSeries :
    FormalMultilinearSeries.comp (expSeries 𝕜 𝔸) (logSeries 𝕜 𝔸) = .id 𝕜 𝔸 1 := by
  convert_to toFMS 𝔸 (subst (PowerSeries.log 𝕜) (PowerSeries.exp 𝕜)) = _
  · simp [toFMS_subst _ _ _ HasSubst.log]
  convert_to constFormalMultilinearSeries 𝕜 𝔸 1 + FormalMultilinearSeries.id 𝕜 𝔸 0 = _
  · simp [subst_exp_log]
  ext n v
  match n with | 0 | 1 | n + 2 => simp

@[simp]
lemma comp_logSeries_expSeries :
    FormalMultilinearSeries.comp (logSeries 𝕜 𝔸) (expSeries 𝕜 𝔸) = .id 𝕜 𝔸 0 := by
  convert_to FormalMultilinearSeries.comp (logSeries 𝕜 𝔸) (removeZero (expSeries 𝕜 𝔸)) = _
  · simp
  convert_to FormalMultilinearSeries.comp
      (logSeries 𝕜 𝔸) (expSeries 𝕜 𝔸 - constFormalMultilinearSeries 𝕜 𝔸 1) = _
  · congr! 1; ext n v; cases n <;> simp [expSeries_eq_ofScalars, ofScalars]
  convert_to toFMS 𝔸 (subst (PowerSeries.exp 𝕜 - 1) (PowerSeries.log 𝕜)) = _
  · simp [toFMS_subst _ _ _ HasSubst.exp_sub_one, - comp_removeZero]
  simp [subst_log_exp_sub_one]

end Comp

section FPowerSeries

variable (𝕜 𝔸 : Type*)
variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
variable [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜] [CompleteSpace 𝔸]

lemma hasFPowerSeriesOnBall_log : HasFPowerSeriesOnBall (log (𝔸 := 𝔸)) (logSeries 𝕜 𝔸) 1 1 := by
  rw [log_eq_logSeries_sum 𝕜]
  rw (config := { occs := [2] }) [← zero_add (1 : 𝔸)]
  apply HasFPowerSeriesOnBall.comp_sub
  refine HasFPowerSeriesOnBall.mono ?_ (by positivity) (radius_logSeries_ge_one 𝕜 𝔸)
  apply FormalMultilinearSeries.hasFPowerSeriesOnBall
  grw [← radius_logSeries_ge_one]
  positivity

@[simp]
lemma hasFPowerSeriesAt_log_one : HasFPowerSeriesAt (log (𝔸 := 𝔸)) (logSeries 𝕜 𝔸) 1 :=
  hasFPowerSeriesOnBall_log 𝕜 𝔸 |>.hasFPowerSeriesAt

end FPowerSeries

section Inv

variable (𝔸 : Type*)
variable [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

lemma eventually_exp_log_eq : ∀ᶠ x in 𝓝 (1 : 𝔸), exp (log x) = x := by
  suffices h : HasFPowerSeriesAt (exp (𝔸 := 𝔸) ∘ log (𝔸 := 𝔸)) (.id ℚ 𝔸 1) 1 by
    filter_upwards [h.eventually_hasSum_sub] with x hx
    apply hx.unique
    have hs :
        Function.support (fun n ↦ FormalMultilinearSeries.id ℚ 𝔸 1 n (fun _ ↦ x - 1))
          ⊆ Set.Iic 1 := by
      rw [← Set.compl_subset_compl, Set.compl_Iic, Function.compl_support, ← Set.Ioi_def,
        Set.ofPred_subset_ofPred]
      intro n hn
      simp [id_apply_of_one_lt, hn]
    rw [← hasSum_subtype_iff_of_support_subset hs]
    convert hasSum_fintype (β := Set.Iic 1) _
    simp [Finset.sum_set_coe
      (f := fun n  ↦ FormalMultilinearSeries.id ℚ 𝔸 1 n (fun _ ↦ x - 1)),
      show Finset.Iic 1 = {0, 1} by decide]
  rw [← comp_expSeries_logSeries]
  refine HasFPowerSeriesAt.comp ?_ (hasFPowerSeriesAt_log_one ℚ 𝔸)
  convert exp_hasFPowerSeriesAt_zero (𝕂 := ℚ) (𝔸 := 𝔸)
  simp

lemma eventually_log_exp_eq : ∀ᶠ x in 𝓝 (0 : 𝔸), log (exp x) = x := by
  suffices h : HasFPowerSeriesAt (log (𝔸 := 𝔸) ∘ exp (𝔸 := 𝔸)) (.id ℚ 𝔸 0) 0 by
    filter_upwards [h.eventually_hasSum] with x hx
    rw [zero_add] at hx
    apply hx.unique
    have hs :
        Function.support (fun n ↦ FormalMultilinearSeries.id ℚ 𝔸 0 n (fun _ ↦ x))
          ⊆ Set.Iic 1 := by
      rw [← Set.compl_subset_compl, Set.compl_Iic, Function.compl_support, ← Set.Ioi_def,
        Set.ofPred_subset_ofPred]
      intro n hn
      simp [id_apply_of_one_lt, hn]
    rw [← hasSum_subtype_iff_of_support_subset hs]
    convert hasSum_fintype (β := Set.Iic 1) _
    simp [Finset.sum_set_coe
      (f := fun n  ↦ FormalMultilinearSeries.id ℚ 𝔸 0 n (fun _ ↦ x)),
      show Finset.Iic 1 = {0, 1} by decide]
  rw [← comp_logSeries_expSeries]
  refine HasFPowerSeriesAt.comp ?_ (exp_hasFPowerSeriesAt_zero (𝕂 := ℚ) (𝔸 := 𝔸))
  convert hasFPowerSeriesAt_log_one ℚ 𝔸
  simp

end Inv

example {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    ∀ᶠ x in 𝓝 (0 : E →L[ℝ] E), log (exp x) = x :=
  have := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  eventually_log_exp_eq _

example {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    ∀ᶠ x in 𝓝 (1 : E →L[ℝ] E), exp (log x) = x :=
  have := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  eventually_exp_log_eq _

end NormedSpace

end Log
