/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Solvable
public import Ado.ForMathlib.LieModuleCartanCriterion

/-!
## Whitehead の第一補題
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

public section HasNondegenerateTraceForm

open LinearMap.BilinForm LieAlgebra LieModule LieIdeal
open LinearMap hiding Nondegenerate

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {I : LieIdeal R L}

attribute [mk_iff LieAlgebra.isKilling_iff_killingCompl_top_eq_bot] IsKilling

namespace LieModule

variable (R L M) in
/-- `IsKilling` の Lie 加群バージョン -/
@[mk_iff hasNondegenerateTraceForm_def]
class HasNondegenerateTraceForm where
  nondegenerate_traceForm : Nondegenerate (traceForm R L M)

attribute [simp] HasNondegenerateTraceForm.nondegenerate_traceForm

end LieModule

namespace LieIdeal

variable (R L M I) in
/-- `killingCompl` の Lie 加群バージョン -/
noncomputable def traceCompl : LieIdeal R L :=
  InvariantForm.orthogonal (traceForm R L M) (traceForm_lieInvariant R L M) I

@[simp]
lemma mem_traceCompl {x} : x ∈ traceCompl R L M I ↔ ∀ y ∈ I, traceForm R L M y x = 0 := by
  simp [traceCompl, InvariantForm.mem_orthogonal]

variable (I) in
@[simp]
lemma traceCompl_eq_killingCompl : traceCompl R L L I = killingCompl R L I := by
  ext; simp

end LieIdeal

namespace LieModule

lemma hasNondegenerateTraceForm_iff_traceCompl_top_eq_bot :
    HasNondegenerateTraceForm R L M ↔ traceCompl R L M ⊤ = ⊥ := by
  simp_rw [hasNondegenerateTraceForm_def,
    traceForm_isSymm R L M |>.isRefl.nondegenerate_iff_separatingRight,
    SeparatingRight, eq_bot_iff, IsConcreteLE.le_iff]
  simp

@[simp]
lemma hasNondegenerateTraceForm_iff_isKilling :
    HasNondegenerateTraceForm R L L ↔ IsKilling R L := by
  simp_rw [hasNondegenerateTraceForm_iff_traceCompl_top_eq_bot,
    isKilling_iff_killingCompl_top_eq_bot, traceCompl_eq_killingCompl]

instance [IsKilling R L] : HasNondegenerateTraceForm R L L :=
  hasNondegenerateTraceForm_iff_isKilling.mpr inferInstance

instance [CharZero R] [IsDomain R] [IsNoetherian R M] [Module.Free R M] [HasTrivialRadical R L]
    [IsFaithful R L M] : HasNondegenerateTraceForm R L M := by
  suffices h : IsSolvable (traceCompl R L M ⊤)
  · replace h := HasTrivialRadical.eq_bot_of_isSolvable _ (hI := h)
    rwa [hasNondegenerateTraceForm_iff_traceCompl_top_eq_bot]
  apply LieIdeal.isSolvable_of_traceFrom_apply_lie_eq_zero_of_isFaithful M
  convert_to
    ⁅traceCompl R L M ⊤, traceCompl R L M ⊤⁆ ≤ traceCompl R L M ⊤
  · simp only [IsConcreteLE.le_iff, mem_traceCompl, LieSubmodule.mem_top]
    grind only
  simp_rw +contextual [LieSubmodule.lie_le_iff, mem_traceCompl, LieSubmodule.mem_top,
    true_implies, ← traceForm_apply_lie_apply, implies_true]

end LieModule

namespace LieAlgebra

instance [HasNondegenerateTraceForm R L L] : IsKilling R L :=
  hasNondegenerateTraceForm_iff_isKilling.mp inferInstance

end LieAlgebra

end HasNondegenerateTraceForm

public section BilinFormDualBasis

open Module

namespace LinearMap.BilinForm

@[simp]
lemma dualBasis_reindex {K V} [Field K] [AddCommGroup V] [Module K V]
    {ι ι'} [DecidableEq ι] [DecidableEq ι'] [Finite ι] [Finite ι']
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (e : ι ≃ ι') :
    dualBasis B hB (Basis.reindex b e) = Basis.reindex (dualBasis B hB b) e := by
  ext; simp [dualBasis, LinearMap.ext_iff]

end LinearMap.BilinForm

end BilinFormDualBasis

public section LieIdealBoolean

open LieAlgebra LieHom LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsSemisimple R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieIdeal

instance : IsFaithful R ↥(LieModule.ker R L M)ᶜ M := by
  simp_rw [isFaithful_iff_ker_eq_bot, LieIdeal.ker_eq, LieIdeal.comap_incl_eq_bot,
    disjoint_compl_left]

end LieIdeal

end LieIdealBoolean

public section Casimir

open Module LinearMap.BilinForm LieModule
open LieAlgebra hiding Basis
open LieHom hiding ker
open LieModule renaming ker → mker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L V : Type*}
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] [IsFaithful K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace UniversalEnvelopingAlgebra

variable (V) in
private noncomputable def casimirOfBasis {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K L) : UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (B i : L) * ι K (dualBasis (traceForm K L V) (by simp) B i : L)

omit [FiniteDimensional K L] in
variable (V) in
-- `dualBasis B hB (Basis.map b f)` という式が簡単に表せないため証明がこのように複雑になっている。
private lemma casimirOfBasis_eq_of_same_index {n : Type*} [Fintype n] [DecidableEq n]
    (B B' : Basis n K L) : casimirOfBasis V B = casimirOfBasis V B' := by
  unfold casimirOfBasis
  set DB := dualBasis (ι := n) (traceForm K L V) (by simp)
  have h i : Basis.equivFun (DB B) (DB B' i) = fun j ↦ Basis.repr B' (B j) i
  · ext j : 1
    convert_to
        traceForm K L V (DB B' i) (∑ i, Basis.repr B' (B j) i • B' i) = Basis.repr B' (B j) i
    · simp [DB]
    simp_rw [map_sum]
    simp [DB, apply_dualBasis_left]
  simp_rw [← LinearEquiv.eq_symm_apply, Basis.equivFun_symm_apply] at h
  simp_rw [h]
  convert_to _ = ∑ j, (∑ i, Basis.repr B' (B j) i • ι K (B' i)) * ι K (DB B j)
  · simp [Finset.mul_sum, Finset.sum_mul, iff_true_intro Finset.sum_comm, - ι_apply]
  simp_rw [← map_smul, ← map_sum, Basis.sum_repr]

omit [FiniteDimensional K L] in
variable (V) in
private lemma casimirOfBasis_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Basis m K L) (B' : Basis n K L) : casimirOfBasis V B = casimirOfBasis V B' := by
  convert_to _ = casimirOfBasis V (Basis.reindex B' (Basis.indexEquiv B' B))
  · simp [casimirOfBasis, ← Basis.indexEquiv B' B |>.sum_comp, - ι_apply]
  apply casimirOfBasis_eq_of_same_index

variable (K L V) in
noncomputable def casimir : UniversalEnvelopingAlgebra K L :=
  casimirOfBasis V (finBasis K L)

omit [FiniteDimensional K L] in
variable (V) in
lemma casimir_eq {_ : FiniteDimensional K L} {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K L) :
    casimir K L V = ∑ i, ι K (B i) * ι K (dualBasis (traceForm K L V) (by simp) B i) :=
  casimirOfBasis_eq ..

end UniversalEnvelopingAlgebra

end Casimir

section WhiteheadFirst

open Function LieAlgebra LieModule

variable {K L V} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V]

namespace LieDerivation

public axiom surjective_inner_of_hasTrivialRadical [CharZero K]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] :
  Surjective (inner K L V)

end LieDerivation

end WhiteheadFirst
