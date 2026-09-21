/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Nilpotent
public import Ado.ForMathlib.UniversalEnvelopingAlgebraIdeal

public section

namespace Matrix

lemma IsUpperTriangular.imp {n R} [Zero R] [LT n]
    {A : Matrix n n R} (hA : IsUpperTriangular A) ⦃i j : n⦄ (hij : j < i) : A i j = 0 :=
  hA hij


lemma mul_apply_diag_eq_mul_of_isUpperTriangular
    {n R} [NonUnitalNonAssocSemiring R] [LinearOrder n] [Fintype n]
    (A B : Matrix n n R) (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) (i : n) :
    (A * B) i i = A i i * B i i := by
  suffices h : ∑ j ∈ ({i}ᶜ : Finset n), A i j * B j i = 0
  · simp [Matrix.mul_apply, Fintype.sum_eq_add_sum_compl i, h]
  apply Finset.sum_eq_zero
  simp +contextual [Finset.mem_compl, Finset.mem_singleton, ← lt_or_lt_iff_ne, or_imp,
    hA.imp, hB.imp]

end Matrix
