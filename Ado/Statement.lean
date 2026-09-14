/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleShrink
public import Ado.ForMathlib.LieModuleNilpotent
public import Ado.ForMathlib.Nilradical

/-!
## Ado の定理の主張
-/

public section

universe u

open Function LieAlgebra LieModule LieIdeal

namespace LieAlgebra

structure BundledAdoSpace (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] where
  mk' ::
  protected V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module K V]
  [instFiniteDimentional : FiniteDimensional K V]
  [instLieRingModule : LieRingModule 𝔤 V]
  [instLieModule : LieModule K 𝔤 V]
  [instIsFaithful : IsFaithful K 𝔤 V]
  [instIsNilpotentNilradical : IsNilpotent (nilradical K 𝔤) V]

attribute [instance]
  BundledAdoSpace.instAddCommGroup
  BundledAdoSpace.instModule
  BundledAdoSpace.instFiniteDimentional
  BundledAdoSpace.instLieRingModule
  BundledAdoSpace.instLieModule
  BundledAdoSpace.instIsFaithful
  BundledAdoSpace.instIsNilpotentNilradical

@[expose]
noncomputable def BundledAdoSpace.mk {K : Type u} {𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (nilradical K 𝔤) V] :
    BundledAdoSpace K 𝔤 :=
  haveI : Small.{u} V := Module.Finite.small K V
  { V := Shrink.{u} V }

class IsAdo (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] :
    Prop where
  nonempty_bundledAdoSpace : Nonempty (BundledAdoSpace K 𝔤)

lemma IsAdo.intro {K 𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (nilradical K 𝔤) V] : IsAdo K 𝔤 :=
  ⟨⟨.mk V⟩⟩

end LieAlgebra

def AdoSpace (K : Type u) (𝔤 : Type*)
    [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤] : Type u :=
  ia.nonempty_bundledAdoSpace.some.V

variable {K : Type u} {𝔤 𝔤₁ 𝔤₂ : Type*}
variable [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤]
variable [LieRing 𝔤₁] [LieAlgebra K 𝔤₁] [LieRing 𝔤₂] [LieAlgebra K 𝔤₂]

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

instance : IsNilpotent (nilradical K 𝔤) (AdoSpace K 𝔤) :=
  inferInstanceAs (IsNilpotent (nilradical K 𝔤) ia.nonempty_bundledAdoSpace.some.V)

instance [LieRing.IsNilpotent 𝔤] : IsNilpotent 𝔤 (AdoSpace K 𝔤) := by
  simpa using (inferInstance : IsNilpotent (nilradical K 𝔤) (AdoSpace K 𝔤))

lemma LieEquiv.isAdo (e : 𝔤₁ ≃ₗ⁅K⁆ 𝔤₂) [IsAdo K 𝔤₁] : IsAdo K 𝔤₂ := by
  let : LieRingModule 𝔤₂ (AdoSpace K 𝔤₁) :=
    { bracket x m := ⁅e.symm x, m⁆
      add_lie := by simp
      lie_add := by simp
      -- これ `simp` に出来ない?
      leibniz_lie := by simp [LieEquiv.map_lie] }
  have hlie (x : 𝔤₂) (m : AdoSpace K 𝔤₁) : ⁅x, m⁆ = ⁅e.symm x, m⁆ := rfl
  have : LieModule K 𝔤₂ (AdoSpace K 𝔤₁) :=
    { smul_lie := by simp [hlie]
      lie_smul := by simp [hlie] }
  have : IsFaithful K 𝔤₂ (AdoSpace K 𝔤₁) :=
    { injective_toEnd := (IsFaithful.injective_toEnd (L := 𝔤₁)).comp e.symm.injective }
  have : IsNilpotent (nilradical K 𝔤₂) (AdoSpace K 𝔤₁)
  · suffices h : IsNilpotent (map e.toLieHom (nilradical K 𝔤₁)) (AdoSpace K 𝔤₁)
    · simpa using h
    rw [← Equiv.lieModule_isNilpotent_iff (lieIdealMap e (nilradical K 𝔤₁))
      (LinearEquiv.refl K (AdoSpace K 𝔤₁)) (by simp [hlie])]
    infer_instance
  exact .intro (AdoSpace K 𝔤₁)

lemma LieEquiv.isAdo_iff (e : 𝔤₁ ≃ₗ⁅K⁆ 𝔤₂) : IsAdo K 𝔤₁ ↔ IsAdo K 𝔤₂ where
  mp _ := e.isAdo
  mpr _ := e.symm.isAdo
