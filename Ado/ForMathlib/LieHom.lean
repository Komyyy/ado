/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieIdealOf

@[expose] public section

open Function LieIdeal

variable {R L L₂ L₃ : Type*} [CommRing R]
variable [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂] [LieRing L₃] [LieAlgebra R L₃]

namespace LieHom

def lieIdealComap (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) : comap f q →ₗ⁅R⁆ q where
  toLinearMap := LinearMap.submoduleComap f.toLinearMap q
  map_lie' {_ _} := Subtype.ext f.map_lie'

@[simp]
lemma lieIdealComap_apply_coe (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (x : comap f q) :
    (lieIdealComap f q x : L₂) = f x :=
  rfl

@[simp]
lemma lieIdealComap_surjective_of_surjective
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (hf : Surjective f) : Surjective (lieIdealComap f q) :=
  LinearMap.submoduleComap_surjective_of_surjective f.toLinearMap q hf

@[simp]
lemma lieIdealComap_ker (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) :
    ker (lieIdealComap f q) = lieIdealOf (ker f) (comap f q) := by
  ext; simp [Subtype.ext_iff]

end LieHom

namespace LieEquiv

lemma map_equiv_eq_comap_symm (e : L ≃ₗ⁅R⁆ L₂) (I : LieIdeal R L) :
    map e.toLieHom I = comap e.symm.toLieHom I := by
  apply le_antisymm
  on_goal 2 =>
    simp_rw [IsConcreteLE.le_iff, mem_comap, coe_coe]
    intro x hx
    simpa using mem_map (f := e.toLieHom) hx
  simp [map_le, Set.subset_def]

lemma comap_equiv_eq_map_symm (e : L ≃ₗ⁅R⁆ L₂) (I : LieIdeal R L₂) :
    comap e.toLieHom I = map e.symm.toLieHom I := by
  simpa using map_equiv_eq_comap_symm e.symm I |>.symm

@[simp high]
lemma mem_map_equiv {e : L ≃ₗ⁅R⁆ L₂} {I : LieIdeal R L} {x} : x ∈ map e I ↔ e.symm x ∈ I := by
  simp [map_equiv_eq_comap_symm]

@[simp]
lemma coe_map_equiv (e : L ≃ₗ⁅R⁆ L₂) (I : LieIdeal R L) :
    (↑(map e.toLieHom I) : Set L₂) = e '' I := by
  simp [Set.ext_iff, e.symm.surjective.exists]

def lieIdealMap (e : L ≃ₗ⁅R⁆ L₂) (I : LieIdeal R L) : I ≃ₗ⁅R⁆ map e.toLieHom I where
  __ :=
    (e.toLinearEquiv.submoduleMap I.toSubmodule).trans
      (LinearEquiv.ofEq (Submodule.map e.toLinearMap I.toSubmodule) (map e.toLieHom I).toSubmodule
        (by simp))
  map_lie' {x y} := Subtype.ext <| e.map_lie x y

@[simp]
lemma lieIdealMap_apply_coe (e : L ≃ₗ⁅R⁆ L₂) (I : LieIdeal R L) (x : I) :
    (lieIdealMap e I x : L₂) = e x :=
  rfl

end LieEquiv

namespace LieIdeal

lemma surjective_map_of_surjective (f : L →ₗ⁅R⁆ L₂) (hf : Surjective f) : Surjective (map f) := by
  intro I
  existsi comap f I
  simp [f.isIdealMorphism_of_surjective, hf]

lemma comap_comp (f : L →ₗ⁅R⁆ L₂) (g : L₂ →ₗ⁅R⁆ L₃) (I : LieIdeal R L₃) :
    comap (g.comp f) I = comap f (comap g I) := by
  ext; simp

end LieIdeal
