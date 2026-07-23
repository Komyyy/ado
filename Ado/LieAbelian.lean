/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Ado.Statement

/-!
## 可換 Lie 代数に対する Ado の定理
-/

open LieModule LieSubmodule

def AbelianAdoSpace (K 𝔤 : Type*)
    [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤] [IsLieAbelian 𝔤] :=
  𝔤 × K
deriving AddCommGroup, Module K

variable {K 𝔤 : Type*}
variable [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤] [IsLieAbelian 𝔤]

namespace AbelianAdoSpace

def equiv : (𝔤 × K) ≃ₗ[K] AbelianAdoSpace K 𝔤 :=
  LinearEquiv.refl K (𝔤 × K)

@[ext]
lemma ext {p q : AbelianAdoSpace K 𝔤} (h : equiv.symm p = equiv.symm q) : p = q := by
  simpa using h

instance : FiniteDimensional K (AbelianAdoSpace K 𝔤) :=
  equiv.finiteDimensional

instance : LieRingModule 𝔤 (AbelianAdoSpace K 𝔤) where
  bracket x p := equiv ((equiv.symm p).2 • x, 0)
  add_lie x y p := by ext : 1; simp
  lie_add x p q := by ext : 1; simp [add_smul]
  leibniz_lie x y p := by ext : 1; simp [trivial_lie_zero]

lemma bracket_def (x : 𝔤) (p : AbelianAdoSpace K 𝔤) : ⁅x, p⁆ = equiv ((equiv.symm p).2 • x, 0) :=
  rfl

@[simp]
lemma equiv_symm_bracket (x : 𝔤) (p : AbelianAdoSpace K 𝔤) :
    equiv.symm ⁅x, p⁆ = ((equiv.symm p).2 • x, 0) := by
  simp [bracket_def]

@[simp]
lemma bracket_equiv (x : 𝔤) (p : 𝔤 × K) : ⁅x, equiv p⁆ = equiv (p.2 • x, 0) := by
  simp [bracket_def]

instance : LieModule K 𝔤 (AbelianAdoSpace K 𝔤) where
  smul_lie t x p := by ext : 1; simp [smul_comm (equiv.symm p).2 t]
  lie_smul t x p := by ext : 1; simp [mul_smul]

instance : IsFaithful K 𝔤 (AbelianAdoSpace K 𝔤) := by
  rw [isFaithful_iff']
  intro x h
  specialize h (equiv (0, 1))
  simpa using h

-- 冪零性は Engel を使えば少し短くなるが、インポートを抑えたい

variable (K 𝔤) in
@[simps toSubmodule]
def sndNulls : LieSubmodule K 𝔤 (AbelianAdoSpace K 𝔤) where
  -- `equiv` と書くだけでいいようにしたい
  toSubmodule := Submodule.map equiv.toLinearMap (Submodule.prod ⊤ ⊥)
  lie_mem {x p} _ := by rw [Submodule.carrier_eq_coe, SetLike.mem_coe]; simp

@[simp]
lemma mem_sndNulls (p : AbelianAdoSpace K 𝔤) : p ∈ sndNulls K 𝔤 ↔ (equiv.symm p).2 = 0 := by
  simp [← mem_toSubmodule]

@[simp]
lemma bracket_top_top :
    ⁅(⊤ : LieIdeal K 𝔤), (⊤ : LieSubmodule K 𝔤 (AbelianAdoSpace K 𝔤))⁆ = sndNulls K 𝔤 := by
  apply le_antisymm
  next => simp [lie_le_iff]
  next =>
    conv => equals ∀ x,
        equiv (x, 0) ∈ ⁅(⊤ : LieIdeal K 𝔤), (⊤ : LieSubmodule K 𝔤 (AbelianAdoSpace K 𝔤))⁆ =>
      simp [SetLike.le_def, equiv.surjective.forall]
    intro x
    convert lie_mem_lie (show x ∈ (⊤ : LieIdeal K 𝔤) by simp)
      (show equiv (0, 1) ∈ (⊤ : LieSubmodule K 𝔤 (AbelianAdoSpace K 𝔤)) by simp)
    simp

@[simp]
lemma bracket_top_sndNulls : ⁅(⊤ : LieIdeal K 𝔤), sndNulls K 𝔤⁆ = ⊥ := by
  simp [lie_eq_bot_iff, equiv.surjective.forall]

instance : IsNilpotent 𝔤 (AbelianAdoSpace K 𝔤) := by
  rw [isNilpotent_iff K]
  existsi 2
  simp

end AbelianAdoSpace

public instance LieAlgebra.IsAdo.of_isLieAbelian : IsAdo K 𝔤 :=
  .intro (AbelianAdoSpace K 𝔤)
