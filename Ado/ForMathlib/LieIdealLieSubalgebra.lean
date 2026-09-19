/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.OfAssociative

public import Mathlib.Tactic.Have

public section

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieIdeal LieSubalgebra

namespace LieSubalgebra

@[simp]
lemma toSubmodule_sup_lieIdeal (L' : LieSubalgebra R L) (I : LieIdeal R L) :
    (L' ⊔ I.toLieSubalgebra).toSubmodule = L'.toSubmodule ⊔ I.toSubmodule := by
  apply le_antisymm
  on_goal 2 => simp [← LieIdeal.toLieSubalgebra_toSubmodule]
  suffices h :
      ∀ᵉ (x ∈ L'.toSubmodule ⊔ I.toSubmodule) (y ∈ L'.toSubmodule ⊔ I.toSubmodule),
        ⁅x, y⁆ ∈ L'.toSubmodule ⊔ I.toSubmodule
  · conv_rhs => change
      { toSubmodule := L'.toSubmodule ⊔ I.toSubmodule
        lie_mem' {x y} hx hy := h x hx y hy : LieSubalgebra R L }.toSubmodule
    simp_rw -proj [LieSubalgebra.toSubmodule_le_toSubmodule, sup_le_iff,
      ← toSubmodule_le_toSubmodule]
    simp
  simp_rw [Submodule.forall_mem_sup, mem_toSubmodule, LieSubmodule.mem_toSubmodule]
  intro x hx y hy z hz w hw
  simp_rw [add_lie, lie_add, ← lie_skew y z]
  refine add_mem (add_mem ?_ ?_) (add_mem (neg_mem ?_) ?_)
  on_goal 1 => refine mem_of_le_of_mem le_sup_left (L'.lie_mem ?_ ?_) <;> assumption
  all_goals refine mem_of_le_of_mem le_sup_right (I.lie_mem ?_); assumption

end LieSubalgebra

namespace LieIdeal

@[simp]
lemma toLieSubalgebra_le_toLieSubalgebra (I I' : LieIdeal R L) :
    I.toLieSubalgebra ≤ I'.toLieSubalgebra ↔ I ≤ I' := by
  simp [← toSubmodule_le_toSubmodule]

@[simp]
lemma toLieSubalgebra_sup (I I' : LieIdeal R L) :
    (I ⊔ I').toLieSubalgebra = I.toLieSubalgebra ⊔ I'.toLieSubalgebra := by
  suffices (I ⊔ I').toLieSubalgebra ≤ I.toLieSubalgebra ⊔ I'.toLieSubalgebra by
    simpa [le_antisymm_iff]
  simp [← toSubmodule_le_toSubmodule]

theorem toEnd_eq (I : LieIdeal R L) {x : I} :
    LieModule.toEnd R I M x = LieModule.toEnd R L M x :=
  rfl

end LieIdeal
