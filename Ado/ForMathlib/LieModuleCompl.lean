/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleProd

@[expose] public section

open LieModule LieSubmodule LieModuleHom

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubmodule

noncomputable def prodEquivOfIsCompl (N N' : LieSubmodule R L M) (h : IsCompl N N') :
    (N × N') ≃ₗ⁅R,L⁆ M where
  __ := Submodule.prodEquivOfIsCompl N.toSubmodule N'.toSubmodule (by simp [h])
  map_lie' := by rintro x ⟨m₁, m₂⟩; simp

noncomputable def projectionOnto (N N' : LieSubmodule R L M) (h : IsCompl N N') : M →ₗ⁅R,L⁆ N :=
  comp (fst R L N N') (prodEquivOfIsCompl N N' h).symm

noncomputable def projection (N N' : LieSubmodule R L M) (h : IsCompl N N') : M →ₗ⁅R,L⁆ M :=
  comp (incl N) (projectionOnto N N' h)

variable {N N' : LieSubmodule R L M} (h : IsCompl N N')

omit [LieAlgebra R L] [LieModule R L M] in
@[simp]
lemma coe_projectionOnto_apply (x) :
    (projectionOnto N N' h x : M) = projection N N' h x :=
  rfl

omit [LieAlgebra R L] [LieModule R L M] in
lemma projection_add_projection_eq_self (x) :
    projection N N' h x + projection N' N h.symm x = x :=
  Submodule.projection_add_projection_eq_self (mod_cast h) x

end LieSubmodule
