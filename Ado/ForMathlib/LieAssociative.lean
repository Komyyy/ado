/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent

public import Mathlib.Tactic.NoncommRing

public section

open List Function Module LieModule

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieRing

lemma mul_lie_of_associative (x y z : A) : ⁅x * y, z⁆ = ⁅x, z⁆ * y + x * ⁅y, z⁆ := by
  simp_rw [of_associative_ring_bracket]; noncomm_ring

lemma list_prod_ofFn_lie_of_associative {n} (f : Fin n → A) (x : A) :
    ⁅prod (ofFn f), x⁆ = ∑ i : Fin n, prod (ofFn (update f i ⁅f i, x⁆)) := by
  induction f using Fin.consInduction with
  | elim0 => simp [of_associative_ring_bracket]
  | cons y f hf =>
    simp_rw [ofFn_cons, prod_cons, mul_lie_of_associative, hf, Fin.sum_univ_succ,
      Fin.update_cons_zero, Fin.cons_zero, ← Fin.cons_update, ofFn_cons, prod_cons, Fin.cons_succ,
      Finset.mul_sum]

instance {A : Type*} [CommRing A] : IsLieAbelian A := by
  rw [← isMulCommutative_iff_isLieAbelian]; infer_instance

end LieRing

namespace LieAlgebra

lemma toSubmodule_lowerCentralSeries_lieSubalgebra_le_top_pow
    (L : LieSubalgebra R A) (k : ℕ) :
    (LieSubmodule.lcs k L.toLieSubmodule).toSubmodule ≤ L.toSubmodule ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k hk =>
    simp_rw [LieSubmodule.lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
      LieSubmodule.mem_top, true_and, SetLike.exists, LieSubalgebra.coe_bracket_of_module,
      Submodule.span_le,Set.ofPred_subset]
    rintro - ⟨x, hx, y, hy, rfl⟩
    replace hy := mem_of_le_of_mem hk (SetLike.mem_coe.mpr hy)
    simp_rw [SetLike.mem_coe, LieRing.of_associative_ring_bracket]
    apply sub_mem
    · rw [Submodule.pow_succ' _ (by simp)]
      simp [Submodule.mul_mem_mul, hx, hy]
    · rw [Submodule.pow_succ]
      simp [Submodule.mul_mem_mul, hx, hy]

lemma _root_.Module.End.toSubmodule_lowerCentralSeries_lieSubalgebra_eq
    (L : LieSubalgebra R (End R M)) (k : ℕ) :
    (lowerCentralSeries R L M k).toSubmodule =
      Submodule.map₂ LinearMap.applyₗ (⊤ : Submodule R M) (L.toSubmodule ^ k) := by
  induction k with
  | zero =>
    simp_rw [lowerCentralSeries_zero, LieSubmodule.top_toSubmodule, Submodule.pow_zero,
      Submodule.one_eq_span_one_set,← Set.singleton_one, Submodule.map₂_span_singleton_eq_map_flip,
      show LinearMap.applyₗ.flip 1 = LinearMap.id from rfl]
    simp
  | succ k hk =>
    -- 後でリファクタリング
    simp_rw +singlePass [lowerCentralSeries_succ]
    conv_lhs =>
      equals Submodule.map₂ LinearMap.applyₗ (lowerCentralSeries R L M k).toSubmodule
          L.toSubmodule =>
        rw [← Submodule.map₂_flip]
        simp [LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.map₂_eq_span_image2,
          Set.image2]
    obtain (rfl | hk₂) := eq_or_ne k 0
    · simp
    simp_rw [hk, Submodule.pow_succ' _ hk₂, Submodule.mul_eq_map₂]
    generalize L.toSubmodule ^ k = N
    simp_rw +singlePass [← N.span_eq, ← L.toSubmodule.span_eq, ← Submodule.span_univ,
      Submodule.map₂_span_span, Set.image2]
    simp only [Set.mem_univ, SetLike.mem_coe, LinearMap.applyₗ_apply_apply, true_and,
      Set.mem_ofPred_eq, LieSubalgebra.mem_toSubmodule, ↓existsAndEq, and_true,
      LinearMap.mul_apply_apply, exists_exists_and_exists_and_eq_and, End.mul_apply]
    grind only

end LieAlgebra
