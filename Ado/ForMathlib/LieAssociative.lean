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
