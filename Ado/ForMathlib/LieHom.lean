/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieIdealOf
public import Ado.ForMathlib.LieAssociative

@[expose] public section

open Function LieIdeal LieHom

variable {R L L₂ L₃ : Type*} [CommRing R]
variable [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂] [LieRing L₃] [LieAlgebra R L₃]

namespace LieHom

/-- {name}`coe_mk` の一般化 -/
@[simp]
lemma coe_mk' (f h) : ⇑(⟨f, h⟩ : L →ₗ⁅R⁆ L₂) = f :=
  rfl

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

@[simps toLinearMap]
def lieIdealMap (f : L →ₗ⁅R⁆ L₂) (I : LieIdeal R L) : I →ₗ⁅R⁆ map f I where
  toLinearMap := Submodule.inclusion ?_ ∘ₗ (LinearMap.submoduleMap f.toLinearMap I)
  map_lie' {_ _} := Subtype.ext f.map_lie'
where finally
  simp +contextual [IsConcreteLE.le_iff, LieIdeal.mem_map]

@[simp]
lemma lieIdealMap_apply_coe (f : L →ₗ⁅R⁆ L₂) (I : LieIdeal R L) (x : I) :
    (lieIdealMap f I x : L₂) = f x :=
  rfl

@[simp]
lemma lieIdealMap_injective_of_injective
    (f : L →ₗ⁅R⁆ L₂) (I : LieIdeal R L) (hf : Injective f) : Injective (lieIdealMap f I) :=
  fun _x₁ _x₂ hx ↦ Subtype.ext (hf congr(Subtype.val $hx))

@[simp]
lemma lieIdealMap_surjective_of_image_eq_map
    (f : L →ₗ⁅R⁆ L₂) (I : LieIdeal R L) (hI : f '' I = map f I) :
    Surjective (lieIdealMap f I) := by
  rintro ⟨x, hx⟩
  simp only [Subtype.ext_iff, lieIdealMap_apply_coe, Subtype.exists, exists_prop]
  simp_rw [← SetLike.mem_coe, ← hI, Set.mem_image, SetLike.mem_coe] at hx
  exact hx

@[simp]
lemma lieIdealMap_ker (f : L →ₗ⁅R⁆ L₂) (I : LieIdeal R L) :
    ker (lieIdealMap f I) = lieIdealOf (ker f) I := by
  ext; simp [Subtype.ext_iff]

attribute [local instance 100] LieRing.ofAssociativeRing in
variable (R L) in
@[simps ! toLinearMap apply]
def toSpanSingleton (x : L) : R →ₗ⁅R⁆ L where
  toLinearMap := LinearMap.toSpanSingleton R L x
  map_lie' {x y} := by simp [trivial_lie_zero]

lemma ker_comp (f : L →ₗ⁅R⁆ L₂) (g : L₂ →ₗ⁅R⁆ L₃) :
    ker (g.comp f) = comap f (ker g) := by
  ext x; simp

end LieHom

namespace LieEquiv

@[simp]
lemma toLieHom_refl : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).toLieHom = LieHom.id :=
  rfl

@[simp]
lemma coe_mk (f g h h₂) : ⇑(⟨f, g, h, h₂⟩ : L ≃ₗ⁅R⁆ L₂) = f :=
  rfl

@[simp]
lemma coe_symm_mk (f g h h₂) : ⇑(⟨f, g, h, h₂⟩ : L ≃ₗ⁅R⁆ L₂).symm = g :=
  rfl

@[simp]
lemma comp_symm (e : L ≃ₗ⁅R⁆ L₂) : e.toLieHom.comp e.symm = LieHom.id := by
  ext; simp

@[simp]
lemma symm_comp (e : L ≃ₗ⁅R⁆ L₂) : e.symm.toLieHom.comp e = LieHom.id := by
  ext; simp

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

@[simp]
lemma ker_eq (e : L ≃ₗ⁅R⁆ L₂) : ker e.toLieHom = ⊥ := by
  ext; simp

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

lemma map_comp (f : L →ₗ⁅R⁆ L₂) (g : L₂ →ₗ⁅R⁆ L₃) (I : LieIdeal R L) :
    map (g.comp f) I = map g (map f I) := by
  apply le_antisymm
  · grw [map_le_iff_le_comap, comap_comp, ← comap_map_le, ← comap_map_le]
  · grw [map_le_iff_le_comap, map_le_iff_le_comap, ← comap_comp, ← comap_map_le]

@[simp]
lemma comap_id (I : LieIdeal R L) : comap LieHom.id I = I := by
  ext; simp

@[simp]
lemma map_id (I : LieIdeal R L) : map LieHom.id I = I := by
  simp_rw [← LieEquiv.toLieHom_refl, LieEquiv.map_equiv_eq_comap_symm]
  simp

@[simp]
lemma comap_bot (f : L →ₗ⁅R⁆ L₂) : comap f ⊥ = ker f :=
  rfl

end LieIdeal
