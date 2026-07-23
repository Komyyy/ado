/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleShrink

/-!
## Ado の定理の主張
-/

public section

universe u

open LieAlgebra LieModule

namespace LieAlgebra

structure BundledAdoSpace (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] where
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
noncomputable def BundledAdoSpace.mk {K : Type u} {𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (maxNilpotentIdeal K 𝔤) V] :
    BundledAdoSpace K 𝔤 :=
  haveI : Small.{u} V := Module.Finite.small K V
  { V := Shrink.{u} V }

class IsAdo (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] :
    Prop where
  nonempty_bundledAdoSpace : Nonempty (BundledAdoSpace K 𝔤)

lemma IsAdo.intro {K 𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (maxNilpotentIdeal K 𝔤) V] : IsAdo K 𝔤 :=
  ⟨⟨.mk V⟩⟩

end LieAlgebra

def AdoSpace (K : Type u) (𝔤 : Type*)
    [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤] : Type u :=
  ia.nonempty_bundledAdoSpace.some.V

variable (K : Type u) (𝔤 : Type*)
variable [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤]

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

instance : IsNilpotent (maxNilpotentIdeal K 𝔤) (AdoSpace K 𝔤) :=
  inferInstanceAs (IsNilpotent (maxNilpotentIdeal K 𝔤) ia.nonempty_bundledAdoSpace.some.V)
