/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent

@[expose] public section

variable (R L : Type*) {M₁ M₂ : Type*}

@[instance_reducible]
protected def Function.Injective.lieRingModule
    [LieRing L] [Bracket L M₁] [AddCommGroup M₁] [AddCommGroup M₂] [LieRingModule L M₂]
    (f : M₁ →+ M₂) (hf : Function.Injective f) (bracket : ∀ (x : L) (m : M₁), f ⁅x, m⁆ = ⁅x, f m⁆) :
    LieRingModule L M₁ where
  add_lie x y m := hf <| by simp [*]
  lie_add x m n := hf <| by simp [*]
  leibniz_lie x y m := hf <| by simp [*]

protected lemma Function.Injective.lieModule
    [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂] [LieRingModule L M₁] [LieRingModule L M₂] [LieModule R L M₂]
    (f : M₁ →ₗ[R] M₂) (hf : Function.Injective f)
    (bracket : ∀ (x : L) (m : M₁), f ⁅x, m⁆ = ⁅x, f m⁆) : LieModule R L M₁ where
  smul_lie t x m := hf <| by simp [*]
  lie_smul t x m := hf <| by simp [*]

@[instance_reducible]
protected def Equiv.lieRingModule [LieRing L] [AddCommGroup M₂] [LieRingModule L M₂] (e : M₁ ≃ M₂) :
    letI := e.addCommGroup
    LieRingModule L M₁ :=
  letI := e.addCommGroup
  letI := { bracket x m := e.symm ⁅x, e m⁆ : Bracket L M₁ }
  e.injective.lieRingModule L e.addEquiv.toAddMonoidHom (by unfold_projs; simp)

@[simp]
lemma linearEquiv_coe {α β : Type*} [Semiring R] [AddCommMonoid β] [Module R β] (e : α ≃ β) :
    ⇑(e.linearEquiv R) = e :=
  rfl

protected lemma Equiv.lieModule
    [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
    [LieModule R L M₂] (e : M₁ ≃ M₂) :
    letI := e.addCommGroup
    letI := e.module R
    letI := e.lieRingModule L
    LieModule R L M₁ :=
  letI := e.addCommGroup
  letI := e.module R
  letI := e.lieRingModule L
  e.injective.lieModule R L (e.linearEquiv R).toLinearMap (by unfold_projs; simp)

def Equiv.lieModuleEquiv
    [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
    [LieModule R L M₂] (e : M₁ ≃ M₂) :
    letI := e.addCommGroup
    letI := e.module R
    letI := e.lieRingModule L
    letI := e.lieModule R L
    M₁ ≃ₗ⁅R,L⁆ M₂ :=
  letI := e.addCommGroup
  letI := e.module R
  letI := e.lieRingModule L
  letI := e.lieModule R L
  { e.linearEquiv R with
    map_lie' {x m} := by unfold_projs; simp }

open Function LieModule

variable {R L}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
variable [LieRingModule L M₁] [LieRingModule L M₂] [LieModule R L M₁] [LieModule R L M₂]

lemma Function.Injective.isFaithful [IsFaithful R L M₁] (f : M₁ →ₗ⁅R,L⁆ M₂) (hf : Injective f) :
    IsFaithful R L M₂ := by
  rw [LieModule.isFaithful_iff']
  intro x hx
  apply ext_of_isFaithful (R := R) (M := M₁)
  intro m
  rw [zero_lie, ← hf.eq_iff, f.map_lie, map_zero, hx]

lemma LieModuleEquiv.isFaithful_iff (e : M₁ ≃ₗ⁅R,L⁆ M₂) :
    IsFaithful R L M₁ ↔ IsFaithful R L M₂ where
  mp _ := e.toEquiv.injective.isFaithful e.toLieModuleHom
  mpr _ := e.symm.toEquiv.injective.isFaithful e.symm.toLieModuleHom

omit [LieAlgebra R L] [LieModule R L M₁] [LieModule R L M₂] in
@[simp]
lemma LieModuleEquiv.map_lie (e : M₁ ≃ₗ⁅R,L⁆ M₂) (x : L) (m : M₁) : e ⁅x, m⁆ = ⁅x, e m⁆ :=
  e.toLieModuleHom.map_lie x m

lemma LieModuleEquiv.isNilpotent_iff (e : M₁ ≃ₗ⁅R,L⁆ M₂) : IsNilpotent L M₁ ↔ IsNilpotent L M₂ :=
  Equiv.lieModule_isNilpotent_iff (f := .refl) (g := e.toLinearEquiv) (by simp)
