/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.DirectSum.Module

public section

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
