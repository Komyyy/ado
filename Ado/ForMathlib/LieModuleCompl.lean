/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleProd

@[expose] public section

open LieModule LieSubmodule LieModuleHom

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

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

@[simp]
lemma coe_projectionOnto_apply (x) :
    (projectionOnto N N' h x : M) = projection N N' h x :=
  rfl

lemma projection_add_projection_eq_self (x) :
    projection N N' h x + projection N' N h.symm x = x :=
  Submodule.projection_add_projection_eq_self (mod_cast h) x

include h in
lemma existsUnique_add_of_isCompl_prod (x : M)
    : ∃! u : N × N', (u.1 : M) + u.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod (mod_cast h) x

@[simp]
theorem projection_apply_left (x : N) : projection N N' h x = x :=
  Submodule.projection_apply_left (mod_cast h) x

@[simp]
theorem projection_apply_right (x : N') : projection N N' h x = 0 :=
  Submodule.projection_apply_right (mod_cast h) x

end LieSubmodule
