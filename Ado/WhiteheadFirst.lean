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

public section Killing

open LinearMap.BilinForm Submodule LieAlgebra LieModule LieIdeal
open LinearMap hiding Nondegenerate

section CommRing

variable {R L : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieAlgebra

attribute [mk_iff isKilling_iff_killingCompl_top_eq_bot] IsKilling

lemma isKilling_iff_nondegenerate_killingForm :
    IsKilling R L ↔ Nondegenerate (killingForm R L) := by
  simp_rw [isKilling_iff_killingCompl_top_eq_bot,
    traceForm_isSymm R L L |>.isRefl.nondegenerate_iff_separatingRight,
    SeparatingRight, eq_bot_iff, IsConcreteLE.le_iff]
  simp

end LieAlgebra

namespace LieIdeal

/-- `BilinForm.orthogonal` と `Submodule.orthogonalBilin` で重複があってややこしい。統合したい。 -/
lemma toSubmodule_killingCompl_eq_orthogonalBilin (I : LieIdeal R L) :
    (killingCompl R L I).toSubmodule = orthogonalBilin (killingForm R L) I.toSubmodule := by
  ext; simp

lemma killingCompl_sup (I J : LieIdeal R L) :
    killingCompl R L (I ⊔ J) = killingCompl R L I ⊓ killingCompl R L J := by
  simp only [← LieSubmodule.toSubmodule_inj, toSubmodule_killingCompl_eq_orthogonalBilin,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule, orthogonalBilin_sup]

end LieIdeal

end CommRing

section Field

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

namespace LieIdeal

set_option allowUnsafeReducibility true in
attribute [local reducible] LieIdeal.toLieSubalgebra in
lemma isKilling_iff_isCompl_killingForm {I : LieIdeal K L} :
    IsKilling K I ↔ IsCompl I (killingCompl K L I) := by
  simp_rw [isKilling_iff_nondegenerate_killingForm, killingForm_eq,
    restrict_nondegenerate_iff_isCompl_orthogonal <| traceForm_isSymm K L L |>.isRefl,
    ← toSubmodule_killingCompl, LieSubmodule.isCompl_toSubmodule]

lemma isKilling_iff_disjoint_killingForm {I : LieIdeal K L} :
    IsKilling K I ↔ Disjoint I (killingCompl K L I) := by
  simp_rw [isKilling_iff_isCompl_killingForm, ← LieSubmodule.isCompl_toSubmodule,
    ← LieSubmodule.disjoint_toSubmodule, toSubmodule_killingCompl,
    isCompl_orthogonal_iff_disjoint <| traceForm_isSymm K L L |>.isRefl]

instance (I : LieIdeal K L) [IsKilling K L] : IsKilling K I := by
  simp [isKilling_iff_isCompl_killingForm, LieIdeal.isCompl_killingCompl]

-- `LieIdeal K L` が分配束であれば解けるが、モジュラー束なので、良い示し方が分からない
theorem_wanted isKilling_iff_of_isCompl (I J : LieIdeal K L) (h : IsCompl I J) :
    IsKilling K L ↔ IsKilling K I ∧ IsKilling K J

end LieIdeal

end Field

end Killing

public section HasNondegenerateTraceForm

open LinearMap.BilinForm LieAlgebra LieModule LieIdeal
open LinearMap hiding Nondegenerate

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {I : LieIdeal R L}

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

@[expose] public section LieIdealCompl

open LieModule LieSubmodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieIdeal

lemma isTrivial_of_disjoint {I J : LieIdeal R L} (h : Disjoint I J) : IsTrivial I J := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  suffices h₂ : ⁅x, y⁆ ∈ I ⊓ J
  · simpa [h.eq_bot, Subtype.ext_iff] using h₂
  rw [mem_inf, show ⁅x, y⁆ ∈ I ↔ -⁅y, x⁆ ∈ I by rw [lie_skew], neg_mem_iff]
  exact ⟨I.lie_mem hx, J.lie_mem hy⟩

@[simps !]
noncomputable def prodEquivOfIsCompl (I J : LieIdeal R L) (h : IsCompl I J) : (I × J) ≃ₗ⁅R⁆ L where
  __ := Submodule.prodEquivOfIsCompl I.toSubmodule J.toSubmodule (by simp [h])
  map_lie' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    have := isTrivial_of_disjoint h.disjoint
    have := isTrivial_of_disjoint h.disjoint.symm
    convert_to (↑⁅x₁, y₁⁆ : L) + ↑⁅x₂, y₂⁆ = ↑⁅x₁, y₁⁆ + ↑⁅x₂, y₁⁆ + (↑⁅x₁, y₂⁆ + ↑⁅x₂, y₂⁆) using 0
    · simp
    simp_rw [trivial_lie_zero]
    simp

end LieIdeal

end LieIdealCompl

public section LieProd

open LieAlgebra

variable {R L₁ L₂ : Type*}
variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]

namespace Prod

variable (R L₁ L₂) in
lemma ad_apply_eq (x : L₁ × L₂) :
    ad R (L₁ × L₂) x = LinearMap.prodMap (ad R L₁ x.1) (ad R L₂ x.2) := by
  simp [DFunLike.ext_iff]

end Prod

end LieProd

public section Casimir

open Module LinearMap.BilinForm LieModule UniversalEnvelopingAlgebra
open LieAlgebra hiding Basis
open LieHom hiding ker
open LieModule renaming ker → mker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L V : Type*}
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace UniversalEnvelopingAlgebra

variable (V) in
private noncomputable def casimirOfBasis {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K ↥(mker K L V)ᶜ) : UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (B i : L) * ι K (dualBasis (traceForm K ↥(mker K L V)ᶜ V) (by simp) B i : L)

variable (V) in
-- `dualBasis B hB (Basis.map b f)` という式が簡単に表せないため証明がこのように複雑になっている。
private lemma casimirOfBasis_eq_of_same_index {n : Type*} [Fintype n] [DecidableEq n]
    (B B' : Basis n K ↥(mker K L V)ᶜ) : casimirOfBasis V B = casimirOfBasis V B' := by
  unfold casimirOfBasis
  set DB := dualBasis (ι := n) (traceForm K ↥(mker K L V)ᶜ V) (by simp)
  have h i : Basis.equivFun (DB B) (DB B' i) = fun j ↦ Basis.repr B' (B j) i
  · ext j : 1
    convert_to
        traceForm K ↥(mker K L V)ᶜ V (DB B' i) (∑ i, Basis.repr B' (B j) i • B' i) =
          Basis.repr B' (B j) i
    · simp [DB]
    simp_rw [map_sum]
    simp [DB, apply_dualBasis_left]
  simp_rw [← LinearEquiv.eq_symm_apply, Basis.equivFun_symm_apply] at h
  simp_rw [h]
  convert_to _ = ∑ j, (∑ i, Basis.repr B' (B j) i • ι K (B' i : L)) * ι K (DB B j : L)
  · simp [Finset.mul_sum, Finset.sum_mul, iff_true_intro Finset.sum_comm, - ι_apply]
  simp_rw [← map_smul, ← map_sum, ← LieSubmodule.coe_smul, ← AddSubmonoidClass.coe_finsetSum,
    Basis.sum_repr]

variable (V) in
private lemma casimirOfBasis_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Basis m K ↥(mker K L V)ᶜ) (B' : Basis n K ↥(mker K L V)ᶜ) :
    casimirOfBasis V B = casimirOfBasis V B' := by
  convert_to _ = casimirOfBasis V (Basis.reindex B' (Basis.indexEquiv B' B))
  · simp [casimirOfBasis, ← Basis.indexEquiv B' B |>.sum_comp, - ι_apply]
  apply casimirOfBasis_eq_of_same_index

variable (K L V) in
noncomputable def casimir : UniversalEnvelopingAlgebra K L :=
  casimirOfBasis V (finBasis K ↥(mker K L V)ᶜ)

omit [FiniteDimensional K L] in
variable (V) in
lemma casimir_eq {_ : FiniteDimensional K L} {n : Type*} [Fintype n] [DecidableEq n]
    (B : Basis n K ↥(mker K L V)ᶜ) :
    casimir K L V =
      ∑ i, ι K (B i : L) * ι K (dualBasis (traceForm K ↥(mker K L V)ᶜ V) (by simp) B i : L) :=
  casimirOfBasis_eq ..

variable (K L V) in
axiom trace_lift_casimir :
    LinearMap.trace _ _ (lift K (toEnd K L V) (casimir K L V)) =
      finrank K L - finrank K (mker K L V)

variable (K) in
axiom lift_casimir_comm (x : L) (v : V) :
    lift K (toEnd K L V) (casimir K L V) ⁅x, v⁆ =
      ⁅x, lift K (toEnd K L V) (casimir K L V) v⁆

axiom casimir_eq_add_of_isCompl (W₁ W₂ : LieSubmodule K L V) (h : IsCompl W₁ W₂) :
  casimir K L V = casimir K L W₁ + casimir K L W₂

end UniversalEnvelopingAlgebra

namespace LieDerivation

axiom exists_eq_lift_casimir_lie (D : LieDerivation K L V) : ∃ v : V, ∀ x,
    D x = lift K (toEnd K L V) (casimir K L V) ⁅x, v⁆

end LieDerivation

end Casimir

public section LieModuleFitting

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

namespace LieModuleHom

lemma isCompl_iSup_ker_pow_iInf_range_pow [IsArtinian R M] [IsNoetherian R M] (f : M →ₗ⁅R,L⁆ M) :
    IsCompl (⨆ n : ℕ, ker (f ^ n)) (⨅ n : ℕ, range (f ^ n)) := by
  simpa [← toLinearMap_pow, ← ker_toSubmodule, ← toSubmodule_range, ← LieSubmodule.iSup_toSubmodule,
    ← LieSubmodule.iInf_toSubmodule] using f.toLinearMap.isCompl_iSup_ker_pow_iInf_range_pow

end LieModuleHom

end LieModuleFitting

section WhiteheadFirst

open Function Filter LinearMap LieAlgebra LieModule LieSubmodule LieModuleHom
open UniversalEnvelopingAlgebra

variable {K L V} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace LieDerivation

public axiom surjective_inner_of_hasTrivialRadical_of_isNilpotent_casimir [CharZero K]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]
    (h : _root_.IsNilpotent (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V)

public axiom surjective_inner_of_hasTrivialRadical_of_bijective_casimir [CharZero K]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]
    (h : Bijective (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V)

public axiom surjective_inner_of_hasTrivialRadical :
    Surjective (inner K L V) -- := by
  -- let πc : V →ₗ⁅K,L⁆ V :=
  --   { __ := lift K (toEnd K L V) (casimir K L V)
  --     map_lie' := by simp [lift_casimir_comm] }
  -- suffices h : ∀ᶠ n in (atTop : Filter ℕ),
  --     ∃ (V₀ V₁ : LieSubmodule K L V), IsCompl V₀ V₁ ∧ sorry
  -- · sorry
  -- sorry

end LieDerivation

end WhiteheadFirst
