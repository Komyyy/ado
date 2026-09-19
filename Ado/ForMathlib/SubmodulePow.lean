/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Algebra.Operations
public import Ado.ForMathlib.SetPow

public section

open scoped Pointwise

namespace Submodule

variable {R : Type*} [Semiring R] {A : Type*} [Semiring A] [Module R A] [IsScalarTower R A A]

lemma list_prod_mem_pow (M : Submodule R A) (n) (l : List A)
    (hl : l.length = n) (hlM : ∀ x ∈ l, x ∈ M) : l.prod ∈ M ^ n := by
  grw [← SetLike.mem_coe, ← pow_subset_pow, Set.mem_pow_iff_list_prod]
  exists l

-- `mul_def` は非可換の場合でも拡張可能
lemma mul_def_noncomm (M N : Submodule R A) : M * N = span R (M * N : Set A) := by
  apply eq_of_forall_ge_iff
  simp [span_le, mul_le, Set.mul_subset_iff]

lemma span_mul (T : Set A) (M : Submodule R A) : span R T * M = span R (T * (M : Set A)) := by
  apply le_antisymm
  on_goal 2 => grw [span_le, ← mul_subset_mul, ← Set.mul_subset_mul_right subset_span]
  rw [mul_le, forall₂_comm]
  intro x hx
  -- `LinearMap.mulRight` は積の可換性を要求しない！
  conv => equals span R T ≤ comap (LinearMap.mulRight R x) (span R (T * (M : Set A))) =>
    simp [IsConcreteLE.le_iff]
  rw [span_le]
  simp +contextual [Set.subset_def, Submodule.mem_span_of_mem, Set.mul_mem_mul, hx]

-- `pow_eq_span_pow_set` は非可換の場合でも拡張可能
lemma pow_eq_span_pow_set_noncomm (M : Submodule R A) (n : ℕ) : M ^ n = span R (M ^ n : Set A) := by
  induction n with
  | zero => simp [Submodule.pow_zero, one_eq_span_one_set]
  | succ n hn =>
    simp_rw [Submodule.pow_succ, hn, span_mul, pow_succ]

end Submodule
