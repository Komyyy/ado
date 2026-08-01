/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Nilpotent
public import Ado.ForMathlib.LieModuleHom

@[expose] public section

open Function LieModuleHom

namespace LieIdeal.Quotient

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simps]
def mk' (s : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ s :=
  { s.toSubmodule.mkQ with
    toFun := LieSubmodule.Quotient.mk
    map_lie' {_ _} := rfl }

@[simp]
theorem surjective_mk' (s : LieIdeal R L) : Surjective (mk' s) :=
  Quot.mk_surjective

@[simp]
theorem mk'_ker (s : LieIdeal R L) : (mk' s).ker = s := by
  ext; simp

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing.IsNilpotent L] (s : LieIdeal R L) : LieRing.IsNilpotent (L ⧸ s) :=
  (LieIdeal.Quotient.surjective_mk' s).lieAlgebra_isNilpotent

end LieIdeal.Quotient

namespace LieSubmodule.Quotient

variable {R L M M₂ : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂] [LieRingModule L M] [LieRingModule L M₂]
variable [LieAlgebra R L] [LieModule R L M]

@[simp]
lemma lie_bracket_mk (N : LieSubmodule R L M) (x : L) (m : M) : ⁅x, (mk m : M ⧸ N)⁆ = mk ⁅x, m⁆ :=
  rfl

def lift (N : LieSubmodule R L M) (f : M →ₗ⁅R,L⁆ M₂) (h : N ≤ ker f) : M ⧸ N →ₗ⁅R,L⁆ M₂ where
  toLinearMap := N.toSubmodule.liftQ f.toLinearMap (by exact h)
  map_lie' {x m} := by
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N m
    simp_rw [← map_lie, LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    conv_lhs => apply Submodule.liftQ_apply
    conv_rhs => arg 2; apply Submodule.liftQ_apply
    simp

@[simp]
lemma lift_apply (N : LieSubmodule R L M) (f : M →ₗ⁅R,L⁆ M₂) {h : N ≤ ker f} (x) :
    lift N f h (mk x) = f x :=
  N.toSubmodule.liftQ_apply ..

@[simp]
lemma lift_mk' (N : LieSubmodule R L M) (f : M →ₗ⁅R,L⁆ M₂) (h : N ≤ ker f) :
    LieModuleHom.comp (lift N f h) (mk' N) = f := by
  ext x; simp

variable [LieModule R L M₂]

def map (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂) (f : M →ₗ⁅R,L⁆ M₂)
    (h : N ≤ comap f N₂) : (M ⧸ N) →ₗ⁅R,L⁆ (M₂ ⧸ N₂) :=
  lift N (LieModuleHom.comp (mk' N₂) f) (by simpa [ker_comp] using h)

@[simp]
lemma map_apply (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂) (f : M →ₗ⁅R,L⁆ M₂)
    {h : N ≤ comap f N₂} (x) : map N N₂ f h (mk x) = mk (f x) := by
  simp [map]

@[simp]
lemma map_mk' (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂) (f : M →ₗ⁅R,L⁆ M₂)
    (h : N ≤ comap f N₂) : (map N N₂ f h).comp (mk' N) = (mk' N₂).comp f := by
  ext x; simp

def equiv (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
    (f : M ≃ₗ⁅R,L⁆ M₂) (h : N.map f = N₂) : (M ⧸ N) ≃ₗ⁅R,L⁆ (M₂ ⧸ N₂) where
  toLieModuleHom := map N N₂ f (by simp_rw [← map_le_iff_le_comap, h, le_rfl])
  invFun := map N₂ N f.symm (by simp_rw [← map_equiv_eq_comap_symm, h, le_rfl])
  left_inv m := by
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N m; simp
  right_inv m := by
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N₂ m; simp

@[simp]
lemma equiv_apply (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
    (f : M ≃ₗ⁅R,L⁆ M₂) (h : N.map f = N₂) (x) :
    equiv N N₂ f h x = map N N₂ f (by simp_rw [← map_le_iff_le_comap, h, le_rfl]) x :=
  rfl

@[simp]
lemma equiv_symm (N : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
    (f : M ≃ₗ⁅R,L⁆ M₂) (h : N.map f = N₂) :
    (equiv N N₂ f h).symm = equiv N₂ N f.symm (by simp [← h, ← map_comp]) := by
  ext x
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N₂ x
  simp [equiv, LieModuleEquiv.symm, LieModuleHom.inverse, LinearMap.inverse]

end LieSubmodule.Quotient
