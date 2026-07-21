/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Unused.LieTransferInstance
public import Mathlib.Logic.Small.Defs

public noncomputable section

namespace Shrink

universe u

variable (R L : Type*) [Small.{u} L]

instance [LieRing L] : LieRing (Shrink.{u} L) :=
  (equivShrink L).symm.lieRing

instance [CommRing R] [LieRing L] [LieAlgebra R L] :
    LieAlgebra R (Shrink.{u} L) :=
  (equivShrink L).symm.lieAlgebra R

def lieEquiv [CommRing R] [LieRing L] [LieAlgebra R L] : Shrink.{u} L ≃ₗ⁅R⁆ L :=
  (equivShrink L).symm.lieEquiv R

end Shrink
