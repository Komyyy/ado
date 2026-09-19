/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Ado.ForMathlib.SubmodulePow

public section

open Submodule LinearMap TensorPower
open scoped Pointwise

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

lemma ι_mul_tprod {n} (m : M) (x : Fin n → M) :
    ι R m * TensorAlgebra.tprod R M n x =
      TensorAlgebra.tprod R M (n + 1) (Fin.cons m x) := by
  simp

variable (R M) in
lemma ι_range_pow_eq (n : ℕ) :
    range (ι R : M →ₗ[R] TensorAlgebra R M) ^ n = range (TensorPower.toTensorAlgebra (n := n)) := by
  apply le_antisymm
  · conv => equals ∀ (f : Fin n → TensorAlgebra R M),
        (∀ i, ∃ x, ι R x = f i) → ∃ a : TensorPower R n M, toTensorAlgebra a = (List.ofFn f).prod =>
      simp_rw [Submodule.pow_eq_span_pow_set, Submodule.span_le, Set.subset_def,
        Set.mem_pow, forall_exists_index, Equiv.subtypePiEquivPi.surjective.forall]
      simp [Equiv.subtypePiEquivPi]
    intro f hf
    choose g hg using hf
    rw [← funext_iff] at hg
    subst hg
    existsi PiTensorProduct.tprod R g
    simp
  · simp_rw [LinearMap.range_le_iff_comap, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top,
      Submodule.span_le, Set.range_subset_iff, SetLike.mem_coe, Submodule.mem_comap,
      toTensorAlgebra_tprod]
    intro f
    simp [Submodule.list_prod_mem_pow]

variable (R M) in
lemma span_tprod_eq_top : span R {x | ∃ᵉ (n) (f : Fin n → M), x = tprod R M n f} = ⊤ := by
  have hι := DirectSum.Decomposition.isInternal
      (fun n : ℕ ↦ LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n)
  simp_rw [TensorAlgebra.ι_range_pow_eq] at hι
  apply DirectSum.IsInternal.submodule_iSup_eq_top at hι
  simp_rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span,
    iSup_span] at hι
  convert hι
  simp only [Set.ext_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Set.mem_range]
  grind only [_=_ toTensorAlgebra_tprod]

end TensorAlgebra
