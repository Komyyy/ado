/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

public section

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
