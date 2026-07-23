/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleNilpotent

@[expose] public section

open LieModule LieModuleHom

variable {R L M N : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [LieRingModule L M] [LieRingModule L N]
variable [LieModule R L M] [LieModule R L N]

namespace Prod

instance : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := by simp
  lie_add x p q := by simp
  leibniz_lie x y p := by simp

lemma lie_module_bracket_def (x : L) (p : M × N) : ⁅x, p⁆ = (⁅x, p.1⁆, ⁅x, p.2⁆) :=
  rfl

@[simp]
lemma fst_lie_module_bracket (x : L) (p : M × N) : ⁅x, p⁆.1 = ⁅x, p.1⁆ :=
  rfl

@[simp]
lemma snd_lie_module_bracket (x : L) (p : M × N) : ⁅x, p⁆.2 = ⁅x, p.2⁆ :=
  rfl

@[simp]
lemma lie_module_bracket_mk (x : L) (m : M) (n : N) : ⁅x, (m, n)⁆ = (⁅x, m⁆, ⁅x, n⁆) :=
  rfl

instance : LieModule R L (M × N) where
  smul_lie t x p := by simp [lie_module_bracket_def]
  lie_smul t x p := by simp [lie_module_bracket_def]

end Prod

namespace LieModuleHom

variable (R L M N) in
@[simps ! apply toLinearMap]
def inl : M →ₗ⁅R,L⁆ M × N where
  toLinearMap := LinearMap.inl R M N
  map_lie' {x m} := by simp

variable (R L M N) in
@[simps ! apply toLinearMap]
def inr : N →ₗ⁅R,L⁆ M × N where
  toLinearMap := LinearMap.inr R M N
  map_lie' {x n} := by simp

end LieModuleHom

namespace LieSubmodule

-- 本当は `SProd` にしたいが `Submodule` と慣習を合わせている
@[simps toSubmodule]
def prod (p : LieSubmodule R L M) (q : LieSubmodule R L N) : LieSubmodule R L (M × N) where
  toSubmodule := Submodule.prod p q
  lie_mem := by
    rintro c ⟨m, n⟩ h
    -- `lie_mem` が `SetLike.coe` ではなく `LieSubmodule.carrier` を使っているためおかしくなってる
    conv at h => equals m ∈ p ∧ n ∈ q => simp
    conv => equals ⁅c, m⁆ ∈ p ∧ ⁅c, n⁆ ∈ q => simp
    exact ⟨lie_mem p h.1, lie_mem q h.2⟩

section Prod

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N]

variable (p : LieSubmodule R L M) (q : LieSubmodule R L N)

@[simp]
lemma coe_prod : (prod p q : Set (M × N)) = (p : Set M) ×ˢ (q : Set N) :=
  rfl

@[simp]
lemma mem_prod (x : M × N) : x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q :=
  Iff.rfl

lemma prod_eq_sup_map : prod p q = map (inl R L M N) p ⊔ map (inr R L M N) q := by
  apply toSubmodule_injective; simp

@[simp]
lemma prod_top : prod (⊤ : LieSubmodule R L M) (⊤ : LieSubmodule R L N) = ⊤ := by
  apply toSubmodule_injective; simp

@[simp]
lemma prod_bot : prod (⊥ : LieSubmodule R L M) (⊥ : LieSubmodule R L N) = ⊥ := by
  apply toSubmodule_injective; simp

lemma prod_eq_top_iff : prod p q = ⊤ ↔ p = ⊤ ∧ q = ⊤ := by
  simp_rw [← toSubmodule_inj]; simp [Submodule.prod_eq_top_iff]

lemma prod_eq_bot_iff : prod p q = ⊥ ↔ p = ⊥ ∧ q = ⊥ := by
  simp_rw [← toSubmodule_inj]; simp [Submodule.prod_eq_bot_iff]

end Prod

@[simp]
lemma lie_module_bracket_prod (I : LieIdeal R L) (P : LieSubmodule R L M) (Q : LieSubmodule R L N) :
    ⁅I, P.prod Q⁆ = prod ⁅I, P⁆ ⁅I, Q⁆ := by
  simp [prod_eq_sup_map, map_bracket_eq]

@[simp]
lemma lcs_prod (P : LieSubmodule R L M) (Q : LieSubmodule R L N) (n : ℕ) :
    lcs n (prod P Q) = prod (lcs n P) (lcs n Q) := by
  induction n with
  | zero => simp
  | succ n hn => simp [hn]

end LieSubmodule

namespace Prod

@[simp]
lemma lowerCentralSeries_eq (n : ℕ) :
    lowerCentralSeries R L (M × N) n =
      LieSubmodule.prod (lowerCentralSeries R L M n) (lowerCentralSeries R L N n) := by
  simp [LieModule.lowerCentralSeries, ← LieSubmodule.prod_top]

@[simp]
lemma isNilpotent_iff : IsNilpotent L (M × N) ↔ IsNilpotent L M ∧ IsNilpotent L N := by
  simp_rw [isNilpotent_iff_eventually_int, lowerCentralSeries_eq, LieSubmodule.prod_eq_bot_iff,
    Filter.eventually_and]

instance [IsNilpotent L M] [IsNilpotent L N] : IsNilpotent L (M × N) :=
  isNilpotent_iff.mpr ⟨inferInstance, inferInstance⟩

end Prod
