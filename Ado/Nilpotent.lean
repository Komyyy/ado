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

section ForMathlib

public section DirectSum

namespace DirectSum

@[to_fun (attr := simp) lmap_fun_add]
lemma lmap_add
    {R : Type*} [Semiring R]
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    (f g : (i : ι) → M i →ₗ[R] N i) : lmap (f + g) = lmap f + lmap g := by
  ext; simp

@[to_fun (attr := simp) lmap_fun_smul]
lemma lmap_smul
    {R : Type*} [CommSemiring R]
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    (c : R) (f : (i : ι) → M i →ₗ[R] N i) : lmap (c • f) = c • lmap f := by
  ext; simp [smul_apply]

end DirectSum

end DirectSum

public section TensorAlgebra

open TensorPower

namespace TensorAlgebra

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]

@[ext high]
lemma hom_ext_tprod
    (f g : TensorAlgebra R M →ₗ[R] N)
    (h : ∀ n x, f (TensorAlgebra.tprod R M n x) = g (TensorAlgebra.tprod R M n x)) :
    f = g := by
  suffices h₂ :
      f ∘ₗ TensorAlgebra.ofDirectSum.toLinearMap = g ∘ₗ TensorAlgebra.ofDirectSum.toLinearMap by
    ext x
    replace h₂ := DFunLike.congr_fun h₂
    specialize h₂ x.toDirectSum
    simpa using h₂
  ext n x
  simp [DirectSum.lof_eq_of, - TensorAlgebra.tprod_apply, h]

@[simp]
lemma tprod_mul_tprod {m n} (x : Fin m → M) (y : Fin n → M) :
    TensorAlgebra.tprod R M m x * TensorAlgebra.tprod R M n y =
      TensorAlgebra.tprod R M (m + n) (Fin.append x y) := by
  conv_lhs => tactic =>
    simp_rw [← toTensorAlgebra_tprod, ← toTensorAlgebra_gMul, TensorPower.tprod_mul_tprod,
      toTensorAlgebra_tprod]

end TensorAlgebra

end TensorAlgebra

public section FinAdd

namespace Fin

@[simp]
lemma castAdd_ne_natAdd {m n} (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j := by
  apply_fun addCases (fun _ ↦ false) (fun _ ↦ true); simp

@[simp]
lemma natAdd_ne_castAdd {m n} (i : Fin n) (j : Fin m) : natAdd m i ≠ castAdd n j :=
  castAdd_ne_natAdd j i |>.symm

end Fin

end FinAdd

end ForMathlib

open Function Set Module LieAlgebra LieModule LieSubmodule LieIdeal LieHom
open UniversalEnvelopingAlgebra

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

namespace NilStepAdoData

variable (D : NilStepAdoData K 𝔫)

attribute [local instance 100] LieRing.ofAssociativeRing

def bracketAux (x : D.𝔥) : TensorAlgebra K D.𝔞 →ₗ[K] UniversalEnvelopingAlgebra K D.𝔞 :=
  mkAlgHom K D.𝔞 ∘ₗ LinearEquiv.conj TensorAlgebra.equivDirectSum.toLinearEquiv.symm
    (DirectSum.lmap (fun n ↦
      ∑ i : Fin n, PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i (toEnd K D.𝔥 D.𝔞 x))))

@[simp]
lemma bracketAux_ι (x : D.𝔥) (y : D.𝔞) : D.bracketAux x (TensorAlgebra.ι K y) = ι K ⁅x, y⁆ := by
  simp [bracketAux]

@[simp]
lemma bracketAux_tprod (x : D.𝔥) {n} (f : Fin n → D.𝔞) :
    D.bracketAux x (TensorAlgebra.tprod K D.𝔞 n f) =
      ∑ i : Fin n, mkAlgHom K D.𝔞 (TensorAlgebra.tprod K D.𝔞 n (update f i ⁅x, f i⁆)) := by
  simp [bracketAux, - TensorAlgebra.tprod_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
    apply_update (f := fun (i : Fin n) (F : D.𝔞 →ₗ[K] D.𝔞) ↦ F (f i))]

lemma bracketAux_add_left (x y : D.𝔥) (a) :
    D.bracketAux (x + y) a = D.bracketAux x a + D.bracketAux y a := by
  simp [bracketAux, PiTensorProduct.map_update_add, Finset.sum_add_distrib]

lemma bracketAux_smul_left (t : K) (x : D.𝔥) (a) :
    D.bracketAux (t • x) a = t • D.bracketAux x a := by
  simp [bracketAux, PiTensorProduct.map_update_smul, ← Finset.smul_sum]

lemma bracketAux_mul (x : D.𝔥) (a b) : D.bracketAux x (a * b) =
    mkAlgHom K D.𝔞 a * D.bracketAux x b + D.bracketAux x a * mkAlgHom K D.𝔞 b := by
  revert a b
  suffices h :
      (LinearMap.mul K (TensorAlgebra K D.𝔞)).compr₂ (D.bracketAux x) =
        (LinearMap.mul K (UniversalEnvelopingAlgebra K D.𝔞)).compl₁₂
            (mkAlgHom K D.𝔞) (D.bracketAux x) +
          (LinearMap.mul K (UniversalEnvelopingAlgebra K D.𝔞)).compl₁₂
            (D.bracketAux x) (mkAlgHom K D.𝔞) by
    simpa [DFunLike.ext_iff] using h
  conv_rhs => apply add_comm
  ext m y n z
  simp only [LinearMap.compr₂_apply, LinearMap.mul_apply_apply, TensorAlgebra.tprod_mul_tprod,
    bracketAux_tprod, LieSubalgebra.coe_bracket_of_module, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, LinearMap.add_apply, LinearMap.compl₁₂_apply, coe_toLinearMap,
    AlgHom.coe_toLieHom, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  conv => enter [2, 1, 2, x]; rw [← map_mul, TensorAlgebra.tprod_mul_tprod]
  conv => enter [2, 2, 2, x]; rw [← map_mul, TensorAlgebra.tprod_mul_tprod]
  congr! with i _ i _ <;> ext j <;> cases j using Fin.addCases <;> simp [update_apply]

lemma bracketAux_eq_of_ringCon (x : D.𝔥) (a b) (h : ringCon K D.𝔞 a b) :
    D.bracketAux x a = D.bracketAux x b := by
  induction h using ringCon_induction with
  | refl | symm | trans | add => grind only [= map_add]
  | mul a b c d h₁ h₂ hi₁ hi₂ =>
    rw [← mkAlgHom_eq_mkAlgHom] at h₁ h₂; simp only [bracketAux_mul, *]
  | lie_compat a b =>
    rw [map_add, ← eq_sub_iff_add_eq]
    conv_rhs => simp only [bracketAux_mul, bracketAux_ι, ← ι_apply]
    conv_lhs =>
      rw [bracketAux_ι, D.𝔥.coe_bracket_of_module, leibniz_lie, ← D.𝔥.coe_bracket_of_module,
        ← D.𝔥.coe_bracket_of_module, map_add, map_lie, map_lie,
        LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket]
    noncomm_ring

instance : LieRingModule D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞) where
  bracket x := tensorLift (D.bracketAux x) (D.bracketAux_eq_of_ringCon x)
  add_lie x y a := by
    cases a with | mkAlgHom a
    simp_rw [tensorLift_mkAlgHom, bracketAux_add_left]
  lie_add x a b := by
    cases a with | mkAlgHom a
    cases b with | mkAlgHom b
    conv_lhs => rw [← map_add, tensorLift_mkAlgHom, map_add]
    conv_rhs => rw [tensorLift_mkAlgHom, tensorLift_mkAlgHom]
  leibniz_lie := sorry

lemma bracket_𝔥_def (x : D.𝔥) (a : UniversalEnvelopingAlgebra K D.𝔞) :
    ⁅x, a⁆ = tensorLift (D.bracketAux x) (D.bracketAux_eq_of_ringCon x) a :=
  rfl

instance : LieModule K D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞) where
  smul_lie t x a := by
    cases a with | mkAlgHom a
    simp_rw [bracket_𝔥_def, tensorLift_mkAlgHom, bracketAux_smul_left]
  lie_smul t x a := by
    cases a with | mkAlgHom a
    conv_lhs => rw [bracket_𝔥_def, ← map_smul, tensorLift_mkAlgHom, map_smul]
    conv_rhs => rw [bracket_𝔥_def, tensorLift_mkAlgHom]

end NilStepAdoData

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
