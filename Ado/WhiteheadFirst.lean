/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Solvable
public import Ado.ForMathlib.HasNondegenerateTraceForm
public import Ado.ForMathlib.LieSemisimple
public import Ado.ForMathlib.LieFitting
public import Ado.ForMathlib.BilinFormDualBasis
public import Ado.ForMathlib.Complemented

/-!
## Whitehead の第一補題
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

public section Casimir

open Module LinearMap.BilinForm LieIdeal LieModule UniversalEnvelopingAlgebra LieDerivation
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

end UniversalEnvelopingAlgebra

end Casimir

section WhiteheadFirst

open Function Filter LieAlgebra LieModule LieSubmodule LieModuleHom
open UniversalEnvelopingAlgebra
open LinearMap hiding restrict

variable (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace LieDerivation

lemma surjective_inner_of_hasTrivialRadical_of_isNilpotent_casimir
    (h : _root_.IsNilpotent (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V) := by
  apply isNilpotent_trace_of_isNilpotent at h
  simp_rw [isNilpotent_iff_eq_zero, trace_lift_casimir, sub_eq_zero, Nat.cast_inj,
    eq_comm (a := Module.finrank K L), ← eq_top_iff_finrank_eq, ← isTrivial_iff_ker] at h
  intro D
  existsi 0
  suffices h : Submodule.map D.toLinearMap (derivedSeries K L 1) = ⊥
  · simp_all [↓derivedSeries_one_eq_top_of_isSemisimple, LinearMap.range_eq_bot, DFunLike.ext_iff]
  simp_rw [_root_.eq_bot_iff, coe_derivedSeries_one_eq, Submodule.map_span, Submodule.span_le,
    Submodule.bot_coe, Set.subset_singleton_iff, Set.forall_mem_image, Set.mem_ofPred]
  rintro _ ⟨x, y, rfl⟩
  simp [trivial_lie_zero]

lemma surjective_inner_of_hasTrivialRadical_of_bijective_casimir
    (h : Bijective (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V) := by
  intro D
  obtain ⟨v, hv⟩ := exists_lift_casimir_apply_eq_lie D
  let e := LinearEquiv.ofBijective _ h
  have he : ∀ (x : L) (v : V), e.symm ⁅x, v⁆ = ⁅x, e.symm v⁆
  · simp_rw +zetaDelta +singlePass [e.surjective.forall, LinearEquiv.ofBijective_apply,
      ← lift_casimir_comm, LinearEquiv.ofBijective_symm_apply_apply, implies_true]
  existsi e.symm v
  ext x
  simp +zetaDelta [← he, LinearEquiv.symm_apply_eq, hv]

public theorem surjective_inner_of_hasTrivialRadical :
    Surjective (inner K L V) := by
  let πc : V →ₗ⁅K,L⁆ V :=
    { __ := lift K (toEnd K L V) (casimir K L V)
      map_lie' := by simp [lift_casimir_comm] }
  obtain ⟨W₀, W₁, hWc, ⟨hWm, hWn⟩, hWb⟩ := πc.fitting
  simp_rw +zetaDelta [← isNilpotent_toLinearMap, restrict_toLinearMap,
    restrict_lift_casimir _ hWc.isComplemented] at hWn
  intro D
  obtain ⟨v₀, hv₀⟩ :=
    surjective_inner_of_hasTrivialRadical_of_isNilpotent_casimir K L W₀ hWn
      (compCodomain D (projectionOnto W₀ W₁ hWc))
  have hWb₂ : Bijective (LinearMap.restrict πc.toLinearMap hWb.mapsTo.imp) := hWb.bijective
  rw [restrict_lift_casimir _ hWc.isComplemented_right] at hWb₂
  obtain ⟨v₁, hv₁⟩ :=
    surjective_inner_of_hasTrivialRadical_of_bijective_casimir K L W₁ hWb₂
      (compCodomain D (projectionOnto W₁ W₀ hWc.symm))
  existsi v₀ + v₁
  convert_to ∀ x : L, ⁅x, (v₀ : V)⁆ = projection W₀ W₁ hWc (D x) at hv₀
  · simp [DFunLike.ext_iff, Subtype.ext_iff]
  convert_to ∀ x : L, ⁅x, (v₁ : V)⁆ = projection W₁ W₀ hWc.symm (D x) at hv₁
  · simp [DFunLike.ext_iff, Subtype.ext_iff]
  ext x
  simp [hv₀, hv₁, projection_add_projection_eq_self]

end LieDerivation

end WhiteheadFirst
