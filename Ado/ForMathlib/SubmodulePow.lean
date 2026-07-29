/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Algebra.Operations

public section

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

end Submodule
