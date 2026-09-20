/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.SubmodulePow
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

public section

variable {R : Type*} [Semiring R]

open scoped Pointwise

namespace Ideal

instance (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] : (I ⊔ J).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    rw [Submodule.mem_sup] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ha
    rw [add_mul]
    solve_by_elim (transparency := .reducible) (maxDepth := 10)
      [add_mem, Ideal.mul_mem_right, Ideal.mem_sup_left, Ideal.mem_sup_right]

lemma mul_eq_span_mul (I J : Ideal R) : I * J = span (I * J : Set R) :=
  Submodule.mul_def_noncomm I J

lemma pow_eq_span_pow_set (I : Ideal R) (n : ℕ) : I ^ n = span (I ^ n : Set R) :=
  Submodule.pow_eq_span_pow_set_noncomm I n

lemma span_pow (S : Set R) (n : ℕ) [(span S).IsTwoSided] :
    span S ^ n = span (S ^ n : Set R) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : (span (S ^ n : Set R)).IsTwoSided := by rw [← hn]; infer_instance
    rw [Submodule.pow_succ, hn, span_mul_span, pow_succ]

lemma mul_subset_mul (I J : Ideal R) : (I * J : Set R) ⊆ ↑(I * J) :=
  Submodule.mul_subset_mul I J

lemma pow_subset_pow (I : Ideal R) (n : ℕ) : (I : Set R) ^ n ⊆ ↑(I ^ n) :=
  Submodule.pow_subset_pow I

-- 後で `Submodule` に拡張
lemma sup_eq_span (I J : Ideal R) : I ⊔ J = span (I ∪ J) := by
  simp

@[elab_as_elim]
theorem span_induction {s : Set R} {p : (x : R) → x ∈ span s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (zero : p 0 (Ideal.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Ideal.add_mem _ ‹_› ‹_›))
    (mul : ∀ (a : R) (x hx), p x hx → p (a * x) (Ideal.mul_mem_left _ _ ‹_›)) {x}
    (hx : x ∈ span s) : p x hx :=
  Submodule.span_induction mem zero add mul hx

end Ideal

namespace TwoSidedIdeal

@[simp]
lemma fromIdeal_span {R : Type*} [Ring R] (S : Set R) : fromIdeal (Ideal.span S) = span S := by
  apply eq_of_forall_ge_iff
  intro I
  rw [TwoSidedIdeal.gc.le_iff_le, span_le, Ideal.span_le, coe_asIdeal]

lemma _root_.Ideal.le_toTwoSidedIdeal {R : Type*} [Ring R] {I : TwoSidedIdeal R} {J : Ideal R}
    [J.IsTwoSided] : I ≤ J.toTwoSided ↔ asIdeal I ≤ J := by
  simp [IsConcreteLE.le_iff]

lemma _root_.Ideal.toTwoSidedIdeal_le {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
    {J : TwoSidedIdeal R} : I.toTwoSided ≤ J ↔ I ≤ asIdeal J := by
  simp [IsConcreteLE.le_iff]

end TwoSidedIdeal
