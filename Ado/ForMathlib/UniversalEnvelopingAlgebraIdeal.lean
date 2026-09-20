/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.FinAdd
public import Ado.ForMathlib.IdealOperation
public import Ado.ForMathlib.TensorAlgebra
public import Ado.ForMathlib.UniversalEnvelopingAlgebra
public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.RingTheory.Ideal.BigOperators

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

open Ideal TensorAlgebra

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

instance (I : LieIdeal R L) : (span (ι R '' (I : Set L))).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    induction ha using span_induction with
    | mem a h =>
      simp only [Set.mem_image, SetLike.mem_coe] at h
      obtain ⟨x, hx, rfl⟩ := h
      induction b with | mkAlgHom b
      revert x hx b
      conv =>
        equals Submodule.map₂ (LinearMap.mul R (UniversalEnvelopingAlgebra R L))
            (Submodule.map (ι R).toLinearMap I.toSubmodule)
              (LinearMap.range (mkAlgHom R L).toLinearMap) ≤
                Submodule.restrictScalars R (span (ι R '' (I : Set L))) =>
        simp [Submodule.map₂_le]
      conv_lhs =>
        enter [2]; rw [← Submodule.span_eq (Submodule.map (ι R).toLinearMap I.toSubmodule)]
      simp_rw [← Submodule.map_top, ← span_tprod_eq_top, Submodule.map_span,
        Submodule.map₂_span_span, Submodule.span_le, Set.image2_subset_iff]
      conv =>
        equals ∀ᵉ (x ∈ I) (n) (f : Fin n → L),
            ι R x * mkAlgHom R L (tprod R L n f) ∈ span ((ι R) '' I) =>
          simp [- TensorAlgebra.tprod_apply, - ι_apply]; grind only
      intro x hx n f
      induction n using Nat.strong_induction_on generalizing x with
      | _ n hn =>
        conv_rhs =>
          equals mkAlgHom R L (tprod R L n f) * ι R x - ⁅mkAlgHom R L (tprod R L n f), ι R x⁆ =>
            simp_rw [LieRing.of_associative_ring_bracket]; noncomm_ring
        refine sub_mem (Ideal.mul_mem_left _ _ ?hx) ?_
        case hx => grw [← SetLike.mem_coe, ← Ideal.subset_span]; exact Set.mem_image_of_mem (ι R) hx
        simp_rw [mkAlgHom_tprod_lie_of_associative]
        apply Ideal.sum_mem
        rintro ⟨i, hi⟩ -
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = i + (m + 1) := by existsi n - (i + 1); lia
        cases f using Fin.appendCases with | append f g
        cases g using Fin.consCases with | cons y g
        simp_rw [show Fin.mk i hi = Fin.natAdd i ⟨0, by lia⟩ by ext; simp, Fin.update_append_natAdd,
          Fin.append_right, Fin.mk_zero, Fin.update_cons_zero, Fin.cons_zero,
          ← TensorAlgebra.tprod_mul_tprod, ← TensorAlgebra.ι_mul_tprod, map_mul, ← ι_apply]
        apply Ideal.mul_mem_left
        apply hn
        · lia
        exact LieSubmodule.lie_mem _ hx
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ hia₁ hia₂ => simp only [add_mul, add_mem, hia₁, hia₂]
    | mul x a ha hia => simp only [mul_assoc, Ideal.mul_mem_left, hia]

end UniversalEnvelopingAlgebra
