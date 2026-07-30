/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Submodule

public section

open LieModuleHom LieSubmodule

variable {R L M M₂ M₃ : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable [LieRingModule L M] [LieRingModule L M₂] [LieRingModule L M₃]

namespace LieSubmodule

lemma comap_comp (f : M →ₗ⁅R,L⁆ M₂) (g : M₂ →ₗ⁅R,L⁆ M₃) (N : LieSubmodule R L M₃) :
    comap (g.comp f) N = comap f (comap g N) := by
  ext x; simp

lemma _root_.LieModuleHom.ker_comp (f : M →ₗ⁅R,L⁆ M₂) (g : M₂ →ₗ⁅R,L⁆ M₃) :
    ker (g.comp f) = comap f (ker g) := by
  ext x; simp

@[simp high]
lemma mem_map_equiv (e : M ≃ₗ⁅R,L⁆ M₂) (N : LieSubmodule R L M) (x) :
    x ∈ map e N ↔ e.symm x ∈ N := by
  simp [e.symm.surjective.exists]

lemma map_equiv_eq_comap_symm (e : M ≃ₗ⁅R,L⁆ M₂) (N : LieSubmodule R L M) :
    map e N = comap e.symm.toLieModuleHom N := by
  ext x; simp

lemma comap_equiv_eq_map_symm (e : M ≃ₗ⁅R,L⁆ M₂) (N : LieSubmodule R L M₂) :
    comap e N = map e.symm.toLieModuleHom N := by
  ext x; simp

end LieSubmodule

namespace LieModuleEquiv

lemma toLieModuleHom_trans (e : M ≃ₗ⁅R,L⁆ M₂) (e₂ : M₂ ≃ₗ⁅R,L⁆ M₃) :
    (e.trans e₂ : M →ₗ⁅R,L⁆ M₃) = LieModuleHom.comp (e₂ : M₂ →ₗ⁅R,L⁆ M₃) e :=
  rfl

@[simp]
lemma toLieModuleHom_refl :
    ((LieModuleEquiv.refl : M ≃ₗ⁅R,L⁆ M) : M →ₗ⁅R,L⁆ M) = LieModuleHom.id :=
  rfl

@[simp]
lemma comp_symm (e : M ≃ₗ⁅R,L⁆ M₂) : e.toLieModuleHom.comp e.symm = LieModuleHom.id := by
  ext; simp


@[simp]
lemma symm_comp (e : M ≃ₗ⁅R,L⁆ M₂) : e.symm.toLieModuleHom.comp e = LieModuleHom.id := by
  ext; simp

end LieModuleEquiv
