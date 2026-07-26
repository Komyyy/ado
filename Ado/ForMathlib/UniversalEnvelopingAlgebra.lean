/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.UniversalEnveloping
import all Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Tactic.NoncommRing

public section

open Function LieRing LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

namespace UniversalEnvelopingAlgebra

instance : LieRingModule L (UniversalEnvelopingAlgebra R L) where
  bracket x a := ι R x * a
  add_lie x y a := by simp [add_mul]
  lie_add x a b := by simp [mul_add]
  leibniz_lie x y a := by
    simp only [ι_apply, LieHom.map_lie, of_associative_ring_bracket]; noncomm_ring

@[simp]
lemma bracket_eq (x : L) (a : UniversalEnvelopingAlgebra R L) : ⁅x, a⁆ = ι R x * a :=
  rfl

instance : LieModule R L (UniversalEnvelopingAlgebra R L) where
  smul_lie t x a := by simp
  lie_smul t x a := by simp

lemma ringCon_lie_compat (x y : L) :
    ringCon R L
      (TensorAlgebra.ι R ⁅x, y⁆ + TensorAlgebra.ι R y * TensorAlgebra.ι R x)
      (TensorAlgebra.ι R x * TensorAlgebra.ι R y) :=
  RingConGen.Rel.of _ _ (UniversalEnvelopingAlgebra.Rel.lie_compat x y)

@[elab_as_elim, induction_eliminator]
lemma ringCon_induction {motive : ∀ x y, ringCon R L x y → Prop}
    (refl : ∀ a, motive a a ((ringCon R L).refl a))
    (symm : ∀ a b (h : ringCon R L a b), motive a b h → motive b a ((ringCon R L).symm h))
    (trans : ∀ a b c (h₁ : ringCon R L a b) (h₂ : ringCon R L b c),
      motive a b h₁ → motive b c h₂ → motive a c ((ringCon R L).trans h₁ h₂))
    (add : ∀ a b c d (h₁ : ringCon R L a b) (h₂ : ringCon R L c d),
      motive a b h₁ → motive c d h₂ → motive (a + c) (b + d) ((ringCon R L).add h₁ h₂))
    (mul : ∀ a b c d (h₁ : ringCon R L a b) (h₂ : ringCon R L c d),
      motive a b h₁ → motive c d h₂ → motive (a * c) (b * d) ((ringCon R L).mul h₁ h₂))
    (lie_compat : ∀ a b,
      motive
        (TensorAlgebra.ι R ⁅a, b⁆ + TensorAlgebra.ι R b * TensorAlgebra.ι R a)
        (TensorAlgebra.ι R a * TensorAlgebra.ι R b)
        (ringCon_lie_compat a b)) :
    ∀ {a b} (h : ringCon R L a b), motive a b h :=
  fun {_a _b} h ↦ RingConGen.Rel.rec (fun _a _b h ↦ h.rec lie_compat) refl @symm @trans @add @mul h

@[expose]
def tensorLift {α : Type*} (f : TensorAlgebra R L → α) (hf : ∀ a b, ringCon R L a b → f a = f b) :
    UniversalEnvelopingAlgebra R L → α :=
  Quotient.lift f hf

@[simp]
lemma tensorLift_mkAlgHom {α : Type*} (f : TensorAlgebra R L → α)
    (hf : ∀ a b, ringCon R L a b → f a = f b) (a : TensorAlgebra R L) :
    tensorLift f hf (mkAlgHom R L a) = f a :=
  rfl

lemma mkAlgHom_eq_mkAlgHom {a b} : mkAlgHom R L a = mkAlgHom R L b ↔ ringCon R L a b :=
  (ringCon R L).eq

variable (R L) in
lemma mkAlgHom_surjective : Surjective (mkAlgHom R L) :=
  (ringCon R L).mk'_surjective

@[elab_as_elim, induction_eliminator, cases_eliminator]
protected lemma ind {motive : UniversalEnvelopingAlgebra R L → Prop} :
    (mkAlgHom : ∀ a, motive (mkAlgHom R L a)) → ∀ a, motive a :=
  fun h ↦ (mkAlgHom_surjective R L).forall.mpr h

end UniversalEnvelopingAlgebra
