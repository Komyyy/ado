/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

section ForMathlib

@[expose] public section LieModuleTransferInstance

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

end LieModuleTransferInstance

public noncomputable section LieModuleShrink

open LieModule

universe u

variable (R L : Type*) {M : Type*} [Small.{u} M]

namespace Shrink

instance [LieRing L] [AddCommGroup M] [LieRingModule L M] : LieRingModule L (Shrink.{u} M) :=
  (equivShrink M).symm.lieRingModule L

instance [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] : LieModule R L (Shrink.{u} M) :=
  (equivShrink M).symm.lieModule R L

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]

def lieModuleEquiv : Shrink.{u} M ≃ₗ⁅R,L⁆ M :=
  (equivShrink M).symm.lieModuleEquiv R L

variable {R L}

@[simp]
lemma isFaithful_iff : IsFaithful R L (Shrink.{u} M) ↔ IsFaithful R L M :=
  (lieModuleEquiv R L).isFaithful_iff

instance [IsFaithful R L M] : IsFaithful R L (Shrink.{u} M) :=
  isFaithful_iff.mpr ‹IsFaithful R L M›

@[simp]
lemma isNilpotent_iff : IsNilpotent L (Shrink.{u} M) ↔ IsNilpotent L M :=
  (lieModuleEquiv ℤ L).isNilpotent_iff

instance [IsNilpotent L M] : IsNilpotent L (Shrink.{u} M) :=
  isNilpotent_iff.mpr ‹IsNilpotent L M›

end Shrink

end LieModuleShrink

end ForMathlib

public section Statement

universe u

open LieAlgebra LieModule

namespace LieAlgebra

structure BundledAdoSpace (K : Type u) (𝔤 : Type*)
    [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] where
  mk' ::
  (V : Type u)
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module K V]
  [instFiniteDimentional : FiniteDimensional K V]
  [instLieRingModule : LieRingModule 𝔤 V]
  [instLieModule : LieModule K 𝔤 V]
  [instIsFaithful : IsFaithful K 𝔤 V]
  [instIsNilpotentMaxNilpotentIdeal : IsNilpotent (maxNilpotentIdeal K 𝔤) V]

attribute [instance]
  BundledAdoSpace.instAddCommGroup
  BundledAdoSpace.instModule
  BundledAdoSpace.instFiniteDimentional
  BundledAdoSpace.instLieRingModule
  BundledAdoSpace.instLieModule
  BundledAdoSpace.instIsFaithful
  BundledAdoSpace.instIsNilpotentMaxNilpotentIdeal

@[expose]
noncomputable def BundledAdoSpace.mk {K : Type u} {𝔤 : Type*}
    [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (maxNilpotentIdeal K 𝔤) V] :
    BundledAdoSpace K 𝔤 :=
  haveI : Small.{u} V := Module.Finite.small K V
  { V := Shrink.{u} V }

class IsAdo (K : Type u) (𝔤 : Type*) [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    : Prop where
  intro ::
  nonempty_bundledAdoSpace : Nonempty (BundledAdoSpace K 𝔤)

end LieAlgebra

def AdoSpace (K : Type u) (𝔤 : Type*)
    [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤] : Type u :=
  ia.nonempty_bundledAdoSpace.some.V

variable (K : Type u) (𝔤 : Type*)
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤]

@[no_expose]
noncomputable instance : AddCommGroup (AdoSpace K 𝔤) :=
  inferInstanceAs (AddCommGroup ia.nonempty_bundledAdoSpace.some.V)

@[no_expose]
noncomputable instance : Module K (AdoSpace K 𝔤) :=
  inferInstanceAs (Module K ia.nonempty_bundledAdoSpace.some.V)

instance : FiniteDimensional K (AdoSpace K 𝔤) :=
  inferInstanceAs (FiniteDimensional K ia.nonempty_bundledAdoSpace.some.V)

@[no_expose]
noncomputable instance : LieRingModule 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (LieRingModule 𝔤 ia.nonempty_bundledAdoSpace.some.V)

instance : LieModule K 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (LieModule K 𝔤 ia.nonempty_bundledAdoSpace.some.V)

instance : IsFaithful K 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (IsFaithful K 𝔤 ia.nonempty_bundledAdoSpace.some.V)

end Statement

open Function Set Module LieAlgebra LieModule
open scoped Pointwise

namespace LieAlgebra

universe u

variable {K 𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]
variable [LieRing.IsNilpotent 𝔤]

-- TODO: 後でインスタンスにする
attribute [local instance 100] LieRing.ofAssociativeRing

public theorem ado_of_isNilpotent : IsAdo K 𝔤 := by
  sorry

end LieAlgebra
