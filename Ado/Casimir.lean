/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.BilinFormDualBasis
public import Ado.ForMathlib.HasNondegenerateTraceForm
public import Ado.ForMathlib.LieCochain
public import Ado.ForMathlib.LieSemisimple
public import Ado.ForMathlib.UniversalEnvelopingAlgebra

/-!
## Casimir 元
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

public section Casimir

open Module LinearMap.BilinForm LieIdeal LieModule UniversalEnvelopingAlgebra LieDerivation
open LieModule.Cohomology
open LieAlgebra hiding Basis
open LieHom hiding ker
open LieModule renaming ker → mker
open UniversalEnvelopingAlgebra renaming map → mapᵤ

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L V : Type*}
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K V] [HasTrivialRadical K L]

namespace UniversalEnvelopingAlgebra

section Faithful

variable [IsFaithful K L V]

variable (V) in
private noncomputable def casimirOfBasis {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K L) : UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (B i) * ι K (dualBasis (traceForm K L V) (by simp) B i)

variable (V) in
-- `dualBasis B hB (Basis.map b f)` という式が簡単に表せないため証明がこのように複雑になっている。
private lemma casimirOfBasis_eq_of_same_index {n : Type*} [Fintype n] [DecidableEq n]
    (B B' : Basis n K L) : casimirOfBasis V B = casimirOfBasis V B' := by
  unfold casimirOfBasis
  set DB := dualBasis (ι := n) (traceForm K L V) (by simp)
  have h i : Basis.equivFun (DB B) (DB B' i) = fun j ↦ Basis.repr B' (B j) i
  · ext j : 1
    convert_to
        traceForm K L V (DB B' i) (∑ i, Basis.repr B' (B j) i • B' i) =
          Basis.repr B' (B j) i
    · simp [DB]
    simp_rw [map_sum]
    simp [DB, apply_dualBasis_left]
  simp_rw [← LinearEquiv.eq_symm_apply, Basis.equivFun_symm_apply] at h
  simp_rw [h]
  convert_to _ = ∑ j, (∑ i, Basis.repr B' (B j) i • ι K (B' i)) * ι K (DB B j)
  · simp [Finset.mul_sum, Finset.sum_mul, iff_true_intro Finset.sum_comm, - ι_apply]
  simp_rw [← map_smul, ← map_sum, Basis.sum_repr]

variable (V) in
private lemma casimirOfBasis_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Basis m K L) (B' : Basis n K L) :
    casimirOfBasis V B = casimirOfBasis V B' := by
  convert_to _ = casimirOfBasis V (Basis.reindex B' (Basis.indexEquiv B' B))
  · simp [casimirOfBasis, ← Basis.indexEquiv B' B |>.sum_comp, - ι_apply]
  apply casimirOfBasis_eq_of_same_index

variable [FiniteDimensional K L]

variable (K L V) in
/-- TODO: `casimir` が忠実ならこれと等しい事に示して統一 -/
noncomputable def casimirOfFaithful : UniversalEnvelopingAlgebra K L :=
  casimirOfBasis V (finBasis K L)

omit [FiniteDimensional K L] in
variable (V) in
lemma casimirOfFaithful_eq {_ : FiniteDimensional K L} {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K L) :
    casimirOfFaithful K L V =
      ∑ i, ι K (B i) * ι K (dualBasis (traceForm K L V) (by simp) B i) :=
  casimirOfBasis_eq ..

variable (K L V) in
lemma trace_lift_casimirOfFaithful :
    LinearMap.trace _ _ (lift K (toEnd K L V) (casimirOfFaithful K L V)) = finrank K L := by
  let B := traceForm K L V
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι),
      Nonempty (Basis ι K L) :=
    ⟨_, inferInstance, inferInstance, ⟨finBasis K L⟩⟩
  let b' := dualBasis B (by simp [B]) b
  conv_lhs =>
    equals ∑ i, B (b i) (b' i) =>
      simp +zetaDelta [casimirOfFaithful_eq V b, traceForm_apply_apply, End.mul_eq_comp]
  simp +zetaDelta [apply_dualBasis_right,
    LinearMap.BilinForm.isSymm_iff.mpr <| traceForm_isSymm _ _ _, Module.finrank_eq_card_basis b]

variable (K) in
lemma lift_casimirOfFaithful_comm (x : L) (v : V) :
    lift K (toEnd K L V) (casimirOfFaithful K L V) ⁅x, v⁆ =
      ⁅x, lift K (toEnd K L V) (casimirOfFaithful K L V) v⁆ := by
  let B := traceForm K L V
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι),
      Nonempty (Basis ι K L) :=
    ⟨_, inferInstance, inferInstance, ⟨finBasis K L⟩⟩
  let b' := dualBasis B (by simp [B]) b
  conv => equals ∑ i, ⁅b i, ⁅b' i, ⁅x, v⁆⁆⁆ = ⁅x, ∑ i, ⁅b i, ⁅b' i, v⁆⁆⁆ =>
    simp +zetaDelta [casimirOfFaithful_eq V b]
  simp_rw [lie_sum]
  conv_rhs =>
    enter [2, i]
    rw [leibniz_lie x (b i)]
    enter [1, 1]
    equals ∑ j, B ⁅x, b i⁆ (b' j) • b j =>
      symm
      convert Basis.sum_repr (dualBasis B (by simp [B]) b') ⁅x, b i⁆ <;>
        [simp +zetaDelta;
          simp +zetaDelta [LinearMap.BilinForm.isSymm_iff.mpr <| traceForm_isSymm _ _ _]]
  conv_rhs =>
    enter [2, i, 2]
    rw [leibniz_lie x (b' i)]
    enter [2, 1, 1]
    equals ∑ j, B ⁅x, b' i⁆ (b j) • b' j =>
      symm
      convert Basis.sum_repr b' ⁅x, b' i⁆
      simp +zetaDelta
    skip
  simp only [sum_lie, lie_sum, lie_add, Finset.sum_add_distrib, smul_lie, lie_smul, ← add_assoc]
  symm
  simp_rw [add_eq_right, B, traceForm_apply_lie_apply' K L V x (b _) (b' _),
    traceForm_comm K L V (b _) ⁅x, b' _⁆, neg_smul, Finset.sum_neg_distrib, neg_add_eq_zero,
    iff_true_intro Finset.sum_comm]

end Faithful

variable [FiniteDimensional K L]

variable (K L V) in
noncomputable def casimir : UniversalEnvelopingAlgebra K L :=
  mapᵤ K (incl (mker K L V)ᶜ) (casimirOfFaithful K ↥(mker K L V)ᶜ V)

variable (K L V) in
lemma lift_casimir_eq_lift_casimirOfFaithful :
    lift K (toEnd K L V) (casimir K L V) =
      lift K (toEnd K ↥(mker K L V)ᶜ V) (casimirOfFaithful K ↥(mker K L V)ᶜ V) := by
  simp_rw [casimir, lift_map]
  congr!

variable (K L V) in
lemma trace_lift_casimir :
    LinearMap.trace _ _ (lift K (toEnd K L V) (casimir K L V)) =
      finrank K L - finrank K (mker K L V) := by
  simp [lift_casimir_eq_lift_casimirOfFaithful, trace_lift_casimirOfFaithful]

variable (K) in
lemma lift_casimir_comm (x : L) (v : V) :
    lift K (toEnd K L V) (casimir K L V) ⁅x, v⁆ =
      ⁅x, lift K (toEnd K L V) (casimir K L V) v⁆ := by
  simp_rw [← projectionOnto_lieModule_ker_compl_lie K x, lift_casimir_eq_lift_casimirOfFaithful,
    lift_casimirOfFaithful_comm]

/-- `IsComplemented W` は Wely の完全可約性から外せるが、そもそもそれを示すのにこの補題が必要。 -/
axiom restrict_lift_casimir (W : LieSubmodule K L V) (h : IsComplemented W)
    (hW : ∀ v ∈ W, lift K (toEnd K L V) (casimir K L V) v ∈ W) :
    LinearMap.restrict (lift K (toEnd K L V) (casimir K L V)) hW =
      lift K (toEnd K L W) (casimir K L W)

lemma _root_.LieDerivation.exists_lift_casimir_apply_eq_lie (D : LieDerivation K L V) :
    ∃ v : V, ∀ x, lift K (toEnd K L V) (casimir K L V) (D x) = ⁅x, v⁆ := by
  let B := traceForm K ↥(mker K L V)ᶜ V
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι),
      Nonempty (Basis ι K ↥(mker K L V)ᶜ) :=
    ⟨_, inferInstance, inferInstance, ⟨finBasis K ↥(mker K L V)ᶜ⟩⟩
  let b' := dualBasis B (by simp [B]) b
  let v := ∑ i, ⁅(b i : L), D (b' i)⁆
  existsi v
  intro x
  convert_to _ = (∑ i, ⁅(b i : L), ⁅x, D (b' i)⁆⁆) + (∑ i, ⁅⁅x, (b i : L)⁆, D (b' i)⁆)
  · simp_rw [v, lie_lie, Finset.sum_sub_distrib, lie_sum]; abel
  conv_rhs =>
    enter [2, 2, i, 1]
    equals ∑ j, B ⁅x, b i⁆ (b' j) • (b j : L) =>
      norm_cast
      symm
      convert Basis.sum_repr (dualBasis B (by simp [B]) b') ⁅x, b i⁆ <;>
        [simp +zetaDelta;
          simp +zetaDelta [LinearMap.BilinForm.isSymm_iff.mpr <| traceForm_isSymm _ _ _]]
  conv_rhs =>
    enter [2, 2, i, 1]
    equals -∑ j, B ⁅x, b' j⁆ (b i) • (b j : L) =>
      obtain ⟨⟨x₁, x₂⟩, rfl⟩ :=
        LieSubmodule.existsUnique_add_of_isCompl_prod
          (isCompl_compl (x := LieModule.ker K L V)).symm x |>.exists
      suffices h : ∀ (y z : ↥(mker K L V)ᶜ), B ⁅(x₂ : L), y⁆ z = 0
      · simp_rw [add_lie, LinearMap.map_add₂, h, add_zero, ← LieIdeal.coe_bracket_of_module,
          B, traceForm_apply_lie_apply, ← lie_skew (b _)]
        simp
      simp_rw [B, traceForm_apply_apply]
      conv =>
        enter [y, z, 1, 2, 1]
        equals 0 => ext; simp [LieModule.mem_ker _ _ _ _ |>.mp x₂.2]
      simp
  simp_rw [neg_lie, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  have h j : ⁅x, b' j⁆ = ∑ k, B ⁅x, b' j⁆ (b k) • b' k
  · symm
    convert Basis.sum_repr b' ⁅x, b' j⁆
    simp +zetaDelta
  simp_rw +singlePass [h, LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left]
  conv_rhs =>
    enter [2, 2, i, 1, 2, j, 1]
    equals B ⁅x, b' j⁆ (b i) =>
      simp_rw +zetaDelta [apply_dualBasis_left, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ _)]
  conv_rhs =>
    enter [2]
    equals ∑ i, ⁅(b i : L), D ⁅x, (b' i : L)⁆⁆ =>
      norm_cast
      conv_rhs => tactic =>
        simp_rw +singlePass [h, AddSubmonoidClass.coe_finsetSum, map_sum, lie_sum, SetLike.val_smul,
          map_smul, lie_smul]
      conv_lhs => tactic =>
        simp_rw +singlePass
          [AddSubmonoidClass.coe_finsetSum, sum_lie, SetLike.val_smul, smul_lie, Finset.sum_comm]
  conv_rhs => equals ∑ i, ⁅(b i : L), ⁅(b' i : L), D x⁆⁆ =>simp
  simp +zetaDelta [casimir, casimirOfFaithful_eq V b]

lemma _root_.LieModule.Cohomology.exists_lift_casimir_twoCocycle_apply_eq_d₁₂
    (f : twoCochain K L V) (hf : f ∈ twoCocycle K L V) :
    ∃ g : oneCochain K L V, ∀ x y,
      lift K (toEnd K L V) (casimir K L V) (f x y) = d₁₂ K L V g x y := by
  let B := traceForm K ↥(mker K L V)ᶜ V
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι),
      Nonempty (Basis ι K ↥(mker K L V)ᶜ) :=
    ⟨_, inferInstance, inferInstance, ⟨finBasis K ↥(mker K L V)ᶜ⟩⟩
  let b' := dualBasis B (by simp [B]) b
  let g : oneCochain K L V :=
    { toFun y := ∑ i, ⁅(b i : L), f (b' i) y⁆
      map_add' := by simp [Finset.sum_add_distrib]
      map_smul' := by simp [Finset.smul_sum] }
  existsi g
  intro x y
  convert_to _ = (∑ i, ⁅x, ⁅(b i : L), f (b' i) y⁆⁆) - (∑ i, ⁅y, ⁅(b i : L), f (b' i) x⁆⁆)
      - (∑ i, ⁅(b i : L), f (b' i) ⁅x, y⁆⁆) using 1
  · simp [g, lie_sum]
  simp_rw +singlePass [leibniz_lie, Finset.sum_add_distrib, sub_add_eq_sub_sub]
  have h (x y : L) : ∑ i, ⁅⁅x, (b i : L)⁆, f (b' i) y⁆ = -∑ i, ⁅(b i : L), f ⁅x, (b' i : L)⁆ y⁆
  · conv_lhs =>
    enter [2, i, 1]
    -- 前の定理とのコピペ。要改善。
    equals ∑ j, B ⁅x, b i⁆ (b' j) • (b j : L) =>
      norm_cast
      symm
      convert Basis.sum_repr (dualBasis B (by simp [B]) b') ⁅x, b i⁆ <;>
        [simp +zetaDelta;
          simp +zetaDelta [LinearMap.BilinForm.isSymm_iff.mpr <| traceForm_isSymm _ _ _]]
    conv_lhs =>
      enter [2, i, 1]
      equals -∑ j, B ⁅x, b' j⁆ (b i) • (b j : L) =>
      obtain ⟨⟨x₁, x₂⟩, rfl⟩ :=
        LieSubmodule.existsUnique_add_of_isCompl_prod
          (isCompl_compl (x := LieModule.ker K L V)).symm x |>.exists
      suffices h : ∀ (y z : ↥(mker K L V)ᶜ), B ⁅(x₂ : L), y⁆ z = 0
      · simp_rw [add_lie, LinearMap.map_add₂, h, add_zero, ← LieIdeal.coe_bracket_of_module,
          B, traceForm_apply_lie_apply, ← lie_skew (b _)]
        simp
      simp_rw [B, traceForm_apply_apply]
      conv =>
        enter [y, z, 1, 2, 1]
        equals 0 => ext; simp [LieModule.mem_ker _ _ _ _ |>.mp x₂.2]
      simp
    simp_rw [neg_lie, Finset.sum_neg_distrib]
    have h j : ⁅x, b' j⁆ = ∑ k, B ⁅x, b' j⁆ (b k) • b' k
    · symm
      convert Basis.sum_repr b' ⁅x, b' j⁆
      simp +zetaDelta
    simp_rw +singlePass [h, LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left]
    conv_lhs =>
      enter [1, 2, i, 1, 2, j, 1]
      equals B ⁅x, b' j⁆ (b i) =>
      simp_rw +zetaDelta [apply_dualBasis_left, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ _)]
    conv_lhs =>
      enter [1]
      equals ∑ i, ⁅(b i : L), f ⁅x, (b' i : L)⁆ y⁆ =>
        norm_cast
        conv_rhs => tactic =>
          simp_rw +singlePass [h, AddSubmonoidClass.coe_finsetSum, map_sum, LinearMap.sum_apply,
            lie_sum, SetLike.val_smul, map_smul, LinearMap.smul_apply, lie_smul]
        conv_lhs => tactic =>
          simp_rw +singlePass
            [AddSubmonoidClass.coe_finsetSum, sum_lie, SetLike.val_smul, smul_lie, Finset.sum_comm]
  simp_rw [h]
  conv_rhs => enter [1, 1, 1, 1, 1, 2, i, 2]; rw [← lie_skew, map_neg, LinearMap.neg_apply]
  conv_rhs => enter [2, 2, i, 2]; rw [← Cohomology.twoCochain_skew]
  simp_rw [lie_neg, Finset.sum_neg_distrib]
  convert_to _ = (∑ i, ⁅(b i : L), ⁅x, f (b' i) y⁆⁆) - (∑ i, ⁅(b i : L), ⁅y, f (b' i) x⁆⁆)
      + (∑ i, ⁅(b i : L), (f ⁅x, y⁆ (b' i) + f ⁅y, (b' i : L)⁆ x + f ⁅(b' i : L), x⁆ y)⁆)
  · simp_rw [lie_add, Finset.sum_add_distrib]; abel
  simp_rw [Cohomology.twoCocycle_lie_jacobi_eq_lie_apply f hf, lie_add, Finset.sum_add_distrib]
  conv_rhs => enter [1, 1, 2, i, 2, 2]; rw [← Cohomology.twoCochain_skew]
  simp_rw [lie_neg, Finset.sum_neg_distrib]
  convert_to _ = ∑ i, ⁅(b i : L), ⁅(b' i : L), f x y⁆⁆
  · abel
  simp +zetaDelta [casimir, casimirOfFaithful_eq _ b]

end UniversalEnvelopingAlgebra

end Casimir
