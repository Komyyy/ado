module
public import Mathlib

open LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option allowUnsafeReducibility true in
attribute [reducible] Submodule.subtype

example (N : LieSubmodule R L M) (x : L) (h : ∀ y ∈ N, toEnd R L M x y ∈ N) :
    LinearMap.restrict (toEnd R L M x) h = toEnd R L N x := by
  ext; simp -- unsolved goal

example {α γ₁ γ₂} (s : γ₁) (coe : γ₁ → γ₂) :
    letI : Membership α γ₁ := { mem _s _a := True }
    letI : Membership α γ₂ := { mem _s _a := True }
    ∀ (f : { x : α // x ∈ s } → Nat) (hf : ∀ x : { x : α // x ∈ s }, f x = 0)
      (y : { x : α // x ∈ coe s }), f y = 0 := by
  intro f hf y
  simp [hf]

example {α γ₁ γ₂} (s : γ₁) (coe : γ₁ → γ₂) :
    letI : Membership α γ₁ := { mem _s _a := True }
    letI : Membership α γ₂ := { mem _s _a := True }
    { x : α // x ∈ s } = { x : α // x ∈ coe s } := by
  with_reducible rfl -- fail

set_option allowUnsafeReducibility true in
attribute [reducible] Membership.mem

example {α γ₁ γ₂} (s : γ₁) (coe : γ₁ → γ₂) :
    letI : Membership α γ₁ := { mem _s _a := True }
    letI : Membership α γ₂ := { mem _s _a := True }
    { x : α // x ∈ s } = { x : α // x ∈ coe s } := by
  with_reducible rfl
