/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleTransferInstance

public noncomputable section

open LieModule

universe u

variable (R L : Type*) {M : Type*} [Small.{u} M]

namespace Shrink

instance [LieRing L] [AddCommGroup M] [LieRingModule L M] : LieRingModule L (Shrink.{u} M) :=
  (equivShrink M).symm.lieRingModule L

instance [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] : LieModule R L (Shrink.{u} M) :=
  (equivShrink M).symm.lieModule R L

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

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
