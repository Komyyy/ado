/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Submodule

@[expose] public section

open LieModuleHom LieSubmodule

variable {R L M M₂ M₃ : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable [LieRingModule L M] [LieRingModule L M₂] [LieRingModule L M₃]

namespace LieModuleHom

instance : Mul (M →ₗ⁅R,L⁆ M) where
  mul f g := LieModuleHom.comp f g

theorem mul_eq_comp (f g : M →ₗ⁅R,L⁆ M) : f * g = f.comp g := rfl

@[simp]
theorem mul_apply (f g : M →ₗ⁅R,L⁆ M) (x : M) : (f * g) x = f (g x) := rfl

variable (R L M) in
@[simp, norm_cast]
lemma toLinearMap_one : (1 : M →ₗ⁅R,L⁆ M).toLinearMap = 1 :=
  rfl

lemma one_eq_id : (1 : M →ₗ⁅R,L⁆ M) = LieModuleHom.id :=
  rfl

lemma range_id : range (LieModuleHom.id : M →ₗ⁅R,L⁆ M) = ⊤ := by
  ext; simp

lemma range_comp (f : M₂ →ₗ⁅R,L⁆ M₃) (g : M →ₗ⁅R,L⁆ M₂) : range (comp f g) = map f (range g) := by
  ext; simp

@[simp, norm_cast]
lemma toLinearMap_mul (f g : M →ₗ⁅R,L⁆ M) : (f * g).toLinearMap = f.toLinearMap * g.toLinearMap :=
  rfl

instance : Monoid (M →ₗ⁅R,L⁆ M) where
  mul_assoc _ _ _ := DFunLike.ext _ _ fun _ ↦ rfl
  mul_one _ := DFunLike.ext _ _ fun _ ↦ rfl
  one_mul _ := DFunLike.ext _ _ fun _ ↦ rfl

@[simp, norm_cast]
lemma toLinearMap_pow (f : M →ₗ⁅R,L⁆ M) (n : ℕ) : (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction n <;> simp [pow_succ, *]

end LieModuleHom

namespace LieSubmodule

lemma comap_comp (f : M →ₗ⁅R,L⁆ M₂) (g : M₂ →ₗ⁅R,L⁆ M₃) (N : LieSubmodule R L M₃) :
    comap (g.comp f) N = comap f (comap g N) := by
  ext x; simp

lemma _root_.LieModuleHom.ker_comp (f : M →ₗ⁅R,L⁆ M₂) (g : M₂ →ₗ⁅R,L⁆ M₃) :
    ker (g.comp f) = comap f (ker g) := by
  ext x; simp

@[simp high]
lemma mem_map_equiv {e : M ≃ₗ⁅R,L⁆ M₂} {N : LieSubmodule R L M} {x} :
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
