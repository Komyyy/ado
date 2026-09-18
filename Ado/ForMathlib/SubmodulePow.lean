/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Algebra.Operations

public section

open scoped Pointwise

namespace Submodule

variable {R : Type*} [Semiring R] {A : Type*} [Semiring A] [Module R A] [IsScalarTower R A A]

lemma list_prod_mem_pow (M : Submodule R A) (n) (l : List A)
    (hl : l.length = n) (hlM : ∀ x ∈ l, x ∈ M) : l.prod ∈ M ^ n := by
  subst hl
  induction l using List.reverseRec with
  | nil => simp [Submodule.pow_zero, Submodule.one_eq_span_one_set, Submodule.mem_span]
  | append_singleton l x hil =>
    simp_rw [List.forall_mem_append, List.forall_mem_singleton] at hlM
    specialize hil hlM.1
    simp [Submodule.pow_succ, Submodule.mul_mem_mul, hil, hlM.2]

lemma fin_prod_mem_pow (M : Submodule R A) {n} (f : Fin n → A) (hf : ∀ i, f i ∈ M) :
    Fin.prod f ∈ M ^ n := by
  simp [Fin.prod_eq_prod_map_finRange, list_prod_mem_pow, hf]

-- `mul_def` は非可換の場合でも拡張可能 (`pow` はできないかも)
theorem mul_def_noncomm (M N : Submodule R A) : M * N = span R (M * N : Set A) := by
  apply eq_of_forall_ge_iff
  simp [span_le, mul_le, Set.mul_subset_iff]

section Algebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

lemma pow_le {M N : Submodule R A} {n : ℕ} :
    M ^ n ≤ N ↔ (∀ f : Fin n → A, (∀ i, f i ∈ M) → Fin.prod f ∈ N) := by
  simp_rw [pow_eq_span_pow_set, span_le, Set.subset_def, SetLike.mem_coe, Set.mem_pow,
    forall_exists_index, forall_apply_eq_imp_iff, SetLike.coe_sort_coe,
    Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map, Equiv.subtypePiEquivPi.surjective.forall,
    Subtype.forall]
  simp [Equiv.subtypePiEquivPi]

end Algebra

end Submodule
