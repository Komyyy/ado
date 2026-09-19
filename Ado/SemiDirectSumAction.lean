/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.DirectSum
public import Ado.ForMathlib.FinAdd
public import Ado.ForMathlib.LieSemiDirectSum
public import Ado.ForMathlib.TensorAlgebra
public import Ado.ForMathlib.UniversalEnvelopingAlgebra

/-!
## 半直和から普遍被覆代数への作用
-/

public section

open Function Module Finset LieAlgebra LieModule LieSubmodule LieIdeal LieHom SemiDirectSum
open TensorAlgebra hiding ringCon ι
open UniversalEnvelopingAlgebra hiding ι

variable {K : Type*} [Field K]
variable {𝔞 𝔥 : Type*} [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)

namespace LieAlgebra.SemiDirectSum

open TensorAlgebra (ι)

attribute [local instance 100] LieRing.ofAssociativeRing

section ActionOnTensorAlgebra

open TensorAlgebra (ι)

@[expose]
def leftLieUEAux : 𝔥 →ₗ[K] End K (TensorAlgebra K 𝔞) where
  toFun x :=
    LinearEquiv.conj TensorAlgebra.equivDirectSum.toLinearEquiv.symm
      (DirectSum.lmap (fun n ↦
        ∑ i : Fin n, PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i (ψ x))))
  map_add' x y := by simp [PiTensorProduct.map_update_add, Finset.sum_add_distrib]
  map_smul' t x := by simp [PiTensorProduct.map_update_smul, ← Finset.smul_sum]

@[simp]
lemma leftLieUEAux_ι (x : 𝔥) (y : 𝔞) : leftLieUEAux ψ x (ι K y) = ι K (ψ x y) := by
  simp [leftLieUEAux]

@[simp]
lemma leftLieUEAux_tprod (x : 𝔥) {n} (f : Fin n → 𝔞) :
    leftLieUEAux ψ x (TensorAlgebra.tprod K 𝔞 n f) =
      ∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (f i))) := by
  simp [leftLieUEAux, - TensorAlgebra.tprod_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
    apply_update (f := fun (i : Fin n) (F : 𝔞 →ₗ[K] 𝔞) ↦ F (f i))]

lemma leftLieUEAux_leftLieUEAux_tprod (x y : 𝔥) {n} (f : Fin n → 𝔞) :
    leftLieUEAux ψ x (leftLieUEAux ψ y (TensorAlgebra.tprod K 𝔞 n f)) =
      (∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (ψ y (f i))))) +
        (∑ p ∈ offDiag (univ : Finset (Fin n)),
          TensorAlgebra.tprod K 𝔞 n (update (update f p.1 (ψ y (f p.1))) p.2 (ψ x (f p.2)))) :=
  calc _
    _ = ∑ i : Fin n, leftLieUEAux ψ x (TensorAlgebra.tprod K 𝔞 n (update f i (ψ y (f i)))) := by
      conv_lhs => rw [leftLieUEAux_tprod, map_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        TensorAlgebra.tprod K 𝔞 n
          (update (update f i (ψ y (f i))) j (ψ x (update f i (ψ y (f i)) j))) := by
      simp only [leftLieUEAux_tprod]
    _ = (∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (ψ y (f i))))) +
          (∑ i : Fin n, ∑ j ∈ ({i}ᶜ : Finset (Fin n)),
            TensorAlgebra.tprod K 𝔞 n (update (update f i (ψ y (f i))) j (ψ x (f j)))) := by
      conv_lhs =>
        conv => enter [2, i]; rw [Fintype.sum_eq_add_sum_compl i]
        rw [sum_add_distrib]
      congr! 3 with i _ i _ j hj <;> [simp; (congr! 3; apply update_of_ne; simpa using hj)]
    _ = _ := by
      congr! 1
      symm
      apply sum_finset_product
      simp [not_iff_not, iff_true_intro eq_comm]

lemma leftLieUEAux_lie_left (x y : 𝔥) (a) : leftLieUEAux ψ ⁅x, y⁆ a =
    leftLieUEAux ψ x (leftLieUEAux ψ y a) - leftLieUEAux ψ y (leftLieUEAux ψ x a) := by
  revert a
  suffices h : leftLieUEAux ψ ⁅x, y⁆ =
      leftLieUEAux ψ x * leftLieUEAux ψ y - leftLieUEAux ψ y * leftLieUEAux ψ x by
    simpa [DFunLike.ext_iff] using h
  ext n f
  conv_lhs => tactic =>
    simp_rw [leftLieUEAux_tprod, map_lie, LieDerivation.lie_apply, MultilinearMap.map_update_sub,
      sum_sub_distrib]
  conv_rhs =>
    simp only [LinearMap.sub_apply, End.mul_apply, leftLieUEAux_leftLieUEAux_tprod]
    enter [2, 2]
    conv =>
      apply_congr
      next => rfl
      tactic => rename_i p hp; rw [update_comm (by simpa using hp)]
    tactic =>
      symm
      apply sum_equiv (s := offDiag (univ : Finset (Fin n))) (Equiv.prodComm (Fin n) (Fin n))
      · simp [not_iff_not, iff_true_intro eq_comm]
      · intro i hi; simp only [Equiv.prodComm_apply, Prod.snd_swap, Prod.fst_swap]; rfl
  noncomm_ring

lemma leftLieUEAux_mul (x : 𝔥) (a b) : leftLieUEAux ψ x (a * b) =
    a * leftLieUEAux ψ x b + leftLieUEAux ψ x a * b := by
  revert a b
  suffices h :
      (LinearMap.mul K (TensorAlgebra K 𝔞)).compr₂ (leftLieUEAux ψ x) =
        (LinearMap.mul K (TensorAlgebra K 𝔞)).compl₁₂ LinearMap.id (leftLieUEAux ψ x) +
          (LinearMap.mul K (TensorAlgebra K 𝔞)).compl₁₂ (leftLieUEAux ψ x) LinearMap.id by
    simpa [DFunLike.ext_iff] using h
  conv_rhs => apply add_comm
  ext m y n z
  simp [Fin.sum_univ_add, - LieSubalgebra.coe_bracket_of_module, - TensorAlgebra.tprod_apply]

lemma mkAlgHom_leftLieUEAux_eq_of_ringCon (x : 𝔥) (a b) (h : ringCon K 𝔞 a b) :
    mkAlgHom K 𝔞 (leftLieUEAux ψ x a) = mkAlgHom K 𝔞 (leftLieUEAux ψ x b) := by
  induction h using ringCon_induction with
  | refl | symm | trans | add => grind only [= map_add]
  | mul a b c d h₁ h₂ hi₁ hi₂ =>
    rw [← mkAlgHom_eq_mkAlgHom] at h₁ h₂; simp [leftLieUEAux_mul, *]
  | lie_compat a b =>
    simp_rw [map_add, ← eq_sub_iff_add_eq]
    conv_rhs => simp only [leftLieUEAux_mul, map_add, map_mul, leftLieUEAux_ι, ← ι_apply]
    conv_lhs =>
      rw [leftLieUEAux_ι, ← ι_apply, LieDerivation.apply_lie_eq_add, map_add, map_lie, map_lie,
        LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket]
    noncomm_ring

lemma ringCon_leftLieUEAux_of_ringCon (x : 𝔥) (a b) (h : ringCon K 𝔞 a b) :
    ringCon K 𝔞 (leftLieUEAux ψ x a) (leftLieUEAux ψ x b) :=
  mkAlgHom_eq_mkAlgHom.mp (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x a b h)

end ActionOnTensorAlgebra

section ActionOnUniversalEnvelopingAlgebra

open UniversalEnvelopingAlgebra (ι)

@[expose]
def leftLieUE : 𝔥 →ₗ[K] End K (UniversalEnvelopingAlgebra K 𝔞) where
  toFun x :=
    { toFun :=
        tensorLift (mkAlgHom K 𝔞 ∘ leftLieUEAux ψ x) (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x)
      map_add' a b := by
        cases a with | mkAlgHom a
        cases b with | mkAlgHom b
        simp_rw [← map_add, tensorLift_mkAlgHom, Function.comp_apply, map_add]
      map_smul' t a := by
        cases a with | mkAlgHom a
        simp_rw [RingHom.id_apply, ← map_smul, tensorLift_mkAlgHom, Function.comp_apply, map_smul] }
  map_add' x y := by ext a; cases a with | mkAlgHom a; simp
  map_smul' t x := by ext a; cases a with | mkAlgHom a; simp

lemma leftLieUE_def (x : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ x a =
      tensorLift (mkAlgHom K 𝔞 ∘ leftLieUEAux ψ x) (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x) a :=
  rfl

lemma leftLieUE_mkAlgHom (x : 𝔥) (a : TensorAlgebra K 𝔞) :
    leftLieUE ψ x (mkAlgHom K 𝔞 a) = mkAlgHom K 𝔞 (leftLieUEAux ψ x a) := by
  simp [leftLieUE_def]

lemma leftLieUE_lie_left (x y : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ ⁅x, y⁆ a = leftLieUE ψ x (leftLieUE ψ y a) - leftLieUE ψ y (leftLieUE ψ x a) := by
  cases a with | mkAlgHom a; simp [leftLieUE_mkAlgHom, leftLieUEAux_lie_left]

@[simp]
lemma leftLieUE_mul (x : 𝔥) (a b : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ x (a * b) = a * leftLieUE ψ x b + leftLieUE ψ x a * b := by
  cases a with | mkAlgHom a
  cases b with | mkAlgHom b
  simp_rw [← map_mul, leftLieUE_mkAlgHom, leftLieUEAux_mul]
  simp

@[simp]
lemma leftLieUE_ι (x : 𝔥) (y : 𝔞) :
    leftLieUE ψ x (UniversalEnvelopingAlgebra.ι K y) = UniversalEnvelopingAlgebra.ι K (ψ x y) := by
  simp [leftLieUE_mkAlgHom]

instance : Bracket (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  bracket x a := ⁅x.left, a⁆ + leftLieUE ψ x.right a

variable {ψ} in
lemma lieUE_def (x : 𝔞 ⋊⁅ψ⁆ 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    ⁅x, a⁆ = ⁅x.left, a⁆ + leftLieUE ψ x.right a :=
  rfl

@[simp]
lemma inl_lieUE (x : 𝔞) (a : UniversalEnvelopingAlgebra K 𝔞) : ⁅inl ψ x, a⁆ = ⁅x, a⁆ := by
  simp [lieUE_def]

@[simp]
lemma inr_lieUE (x : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) : ⁅inr ψ x, a⁆ = leftLieUE ψ x a := by
  simp [lieUE_def]

variable {ψ} in
lemma add_lieUE (x y : 𝔞 ⋊⁅ψ⁆ 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    ⁅x + y, a⁆ = ⁅x, a⁆ + ⁅y, a⁆ := by
  simp only [add_eq_mk, lieUE_def, add_lie, bracket_eq, ι_apply, map_add, LinearMap.add_apply]
  abel

variable {ψ} in
lemma smul_lieUE (t : K) (x : 𝔞 ⋊⁅ψ⁆ 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    ⁅t • x, a⁆ = t • ⁅x, a⁆ := by
  simp [lieUE_def]

variable {ψ} in
lemma neg_lieUE (x : 𝔞 ⋊⁅ψ⁆ 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    ⁅-x, a⁆ = -⁅x, a⁆ := by
  simpa using smul_lieUE (-1 : K) x a

instance : LieRingModule (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  add_lie := add_lieUE
  lie_add x a b := by
    simp only [lieUE_def, lie_add, bracket_eq, ι_apply, map_add]; abel
  leibniz_lie x y a := by
    conv => equals ⁅⁅x, y⁆, a⁆ = ⁅x, ⁅y, a⁆⁆ - ⁅y, ⁅x, a⁆⁆ => grind only
    obtain ⟨x₁, x₂⟩ := x; obtain ⟨y₁, y₂⟩ := y
    conv => equals
        ⁅⁅inl ψ x₁, inl ψ y₁⁆, a⁆ + ⁅⁅inr ψ x₂, inl ψ y₁⁆, a⁆ +
          ⁅⁅inl ψ x₁, inr ψ y₂⁆, a⁆ + ⁅⁅inr ψ x₂, inr ψ y₂⁆, a⁆ =
          ⁅x₁, ⁅y₁, a⁆⁆ + ⁅x₁, leftLieUE ψ y₂ a⁆ +
            leftLieUE ψ x₂ ⁅y₁, a⁆ + leftLieUE ψ x₂ (leftLieUE ψ y₂ a) -
          (⁅y₁, ⁅x₁, a⁆⁆ + ⁅y₁, leftLieUE ψ x₂ a⁆ +
            leftLieUE ψ y₂ ⁅x₁, a⁆ + (leftLieUE ψ y₂ (leftLieUE ψ x₂ a))) =>
      simp [lieUE_def, - ι_apply, - bracket_eq, ← add_assoc, ← sub_eq_add_neg]
    conv_lhs =>
      conv =>
        enter [1, 1, 1]
        equals ⁅x₁, ⁅y₁, a⁆⁆ - ⁅y₁, ⁅x₁, a⁆⁆ => simp_rw [← LieHom.map_lie, inl_lieUE, lie_lie]
      conv =>
        enter [2]
        equals leftLieUE ψ x₂ (leftLieUE ψ y₂ a) - leftLieUE ψ y₂ (leftLieUE ψ x₂ a) =>
          simp_rw [← LieHom.map_lie, inr_lieUE, leftLieUE_lie_left]
    conv => equals
        ⁅⁅inr ψ x₂, inl ψ y₁⁆, a⁆ + ⁅⁅inl ψ x₁, inr ψ y₂⁆, a⁆ =
          ⁅x₁, leftLieUE ψ y₂ a⁆ + leftLieUE ψ x₂ ⁅y₁, a⁆ -
            (⁅y₁, leftLieUE ψ x₂ a⁆ + leftLieUE ψ y₂ ⁅x₁, a⁆) =>
      grind only
    conv_lhs =>
      conv =>
        enter [1]
        rw [inr_lie_inl, inl_lieUE, bracket_eq]
      conv =>
        enter [2]
        rw [inl_lie_inr, neg_lieUE, inl_lieUE, bracket_eq]
    conv_rhs =>
      simp only [bracket_eq]
      conv =>
        enter [1, 2]
        rw [leftLieUE_mul, leftLieUE_ι]
      conv =>
        enter [2, 2]
        rw [leftLieUE_mul, leftLieUE_ι]
    noncomm_ring

instance : LieModule K (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  smul_lie := smul_lieUE
  lie_smul t x a := by simp [lieUE_def]

@[simp]
lemma toEndUE_inl (x : 𝔞) :
    toEnd K (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) (inl ψ x) =
      toEnd K 𝔞 (UniversalEnvelopingAlgebra K 𝔞) x := by
  ext; simp [- inl_eq_mk]

end ActionOnUniversalEnvelopingAlgebra

end LieAlgebra.SemiDirectSum
