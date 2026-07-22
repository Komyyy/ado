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

public section LieModuleTransferInstance

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

end LieModuleTransferInstance

public noncomputable section LieModuleShrink

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

end Shrink

end LieModuleShrink

end ForMathlib

open Function Set Module LieAlgebra LieModule
open scoped Pointwise

namespace LieAlgebra

universe u

variable {K : Type u} {𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]
variable [LieRing.IsNilpotent 𝔤]

-- TODO: 後でインスタンスにする
attribute [local instance 100] LieRing.ofAssociativeRing

public theorem ado_of_isNilpotent :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule K 𝔤 V),
      IsFaithful K 𝔤 V ∧ LieModule.IsNilpotent 𝔤 V := by
  sorry

end LieAlgebra
