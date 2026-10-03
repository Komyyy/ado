/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Tactic.LinearCombination

@[expose] public section

variable {R L M M₂} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

namespace LieModule.Cohomology

omit [LieRingModule L M] [LieModule R L M] in
@[simp]
lemma twoCochain_mk_apply (f hf x) : (⟨f, hf⟩ : twoCochain R L M) x = f x :=
  rfl

lemma twoCocycle_lie_jacobi_eq_lie_apply
    (f : twoCochain R L M) (hf : f ∈ twoCocycle R L M) (x y z : L) :
    f ⁅x, y⁆ z + f ⁅y, z⁆ x + f ⁅z, x⁆ y = ⁅x, f y z⁆ + ⁅y, f z x⁆ + ⁅z, f x y⁆ := by
  simp_rw [mem_twoCocycle_iff, DFunLike.ext_iff, d₂₃_apply, LinearMap.zero_apply] at hf
  specialize hf x y z
  conv_lhs at hf => enter [1, 1, 1, 1, 2]; rw [← twoCochain_skew, lie_neg]
  conv_lhs at hf => enter [1, 2]; rw [← lie_skew, map_neg, LinearMap.neg_apply]
  linear_combination (norm := abel) -hf

def twoCochain.compCodomain (f : twoCochain R L M) (g : M →ₗ⁅R,L⁆ M₂) : twoCochain R L M₂ :=
  ⟨LinearMap.compr₂ f.val g.toLinearMap, by simp⟩

omit [LieModule R L M] [LieModule R L M₂] in
@[simp]
lemma twoCochain.compCodomain_apply_apply (f : twoCochain R L M) (g : M →ₗ⁅R,L⁆ M₂) (x y) :
    twoCochain.compCodomain f g x y = g (f x y) :=
  rfl

@[simp]
lemma twoCochain.compCodomain_mem_twoCocycle (f : twoCochain R L M) (g : M →ₗ⁅R,L⁆ M₂)
    (hf : f ∈ twoCocycle R L M) : twoCochain.compCodomain f g ∈ twoCocycle R L M₂ := by
  simp_rw [mem_twoCocycle_iff, DFunLike.ext_iff, d₂₃_apply, twoCochain.compCodomain_apply_apply,
    LinearMap.zero_apply, ← LieModuleHom.map_lie, sub_eq_add_neg, ← map_neg, ← map_add] at hf ⊢
  simp_rw [hf, map_zero, implies_true]

end LieModule.Cohomology
