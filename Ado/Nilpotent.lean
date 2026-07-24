/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib
public import Ado.LieAbelian
public import Ado.ForMathlib.LieModulePUnit
public import Ado.ForMathlib.LieModuleSubsingleton
public import Ado.ForMathlib.LieModuleKer

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

section ForMathlib

public section ModuleDimension

open Module

lemma Submodule.finrank_lt_iff {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {s : Submodule K V} : finrank K s < finrank K V ↔ s < ⊤ where
  mp := lt_top_of_finrank_lt_finrank
  mpr := finrank_lt ∘ ne_top_of_lt

end ModuleDimension

@[expose] public section LieModuleModule

open Module

universe u

namespace LieIdeal

variable {R L L₂ L₃ : Type*} [CommRing R]
variable [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂] [LieRing L₃] [LieAlgebra R L₃]

@[simp]
lemma comap_comp (f : L →ₗ⁅R⁆ L₂) (g : L₂ →ₗ⁅R⁆ L₃) (s : LieIdeal R L₃) :
    comap (g.comp f) s = comap f (comap g s) :=
  rfl

end LieIdeal

namespace LieIdeal.Quotient

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simps]
def mk' (s : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ s :=
  { s.toSubmodule.mkQ with
    toFun := LieSubmodule.Quotient.mk
    map_lie' := fun {_ _} => rfl }

@[simp]
theorem surjective_mk' (s : LieIdeal R L) : Function.Surjective (mk' s) :=
  Quot.mk_surjective

@[simp]
theorem mk'_ker (s : LieIdeal R L) : (mk' s).ker = s := by
  ext; simp

end LieIdeal.Quotient

namespace LieHom

lemma finrank_range_add_finrank_ker {K L L₂ : Type*} [Field K]
    [LieRing L] [LieAlgebra K L] [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L]
    (f : L →ₗ⁅K⁆ L₂) : Module.finrank K f.range + Module.finrank K f.ker = Module.finrank K L :=
  f.toLinearMap.finrank_range_add_finrank_ker

@[simps]
def lieIdealComap {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) : q.comap f →ₗ⁅R⁆ q where
  toFun x := ⟨f x, x.2⟩
  map_add' _ _ := by ext; simp
  map_smul'  _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp

@[simp]
lemma lieIdealComap_ker {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) :
    (lieIdealComap f q).ker = f.ker.comap (q.comap f).incl := by
  ext; simp [Subtype.ext_iff]

end LieHom

namespace LieSubmodule

@[congr]
lemma _root_.LieIdeal.finrank_congr {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} (h : p = q) :
    finrank R p = finrank R q :=
  (LieEquiv.ofEq p.toLieSubalgebra q.toLieSubalgebra (by simp [h])).toLinearEquiv.finrank_eq

-- defeq abuse
def toSubmoduleEquiv {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] (s : LieSubmodule R L M) :
    s.toSubmodule ≃ₗ[R] s := LinearEquiv.refl R s

-- also defeq abuse
def quotientToSubmoduleEquiv {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] (s : LieSubmodule R L M) :
    (M ⧸ s.toSubmodule) ≃ₗ[R] (M ⧸ s) := LinearEquiv.refl R (M ⧸ s)

@[simp]
lemma finrank_toSubmodule {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [Module.Finite R M] (s : LieSubmodule R L M) :
    finrank R s.toSubmodule = finrank R s :=
  LinearEquiv.finrank_eq s.toSubmoduleEquiv

@[simp]
lemma finrank_quotient_toSubmodule {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [Module.Finite R M] (s : LieSubmodule R L M) :
    finrank R (M ⧸ s.toSubmodule) = finrank R (M ⧸ s) :=
  LinearEquiv.finrank_eq s.quotientToSubmoduleEquiv

lemma finrank_lt_iff {K L V : Type*} [Field K] [LieRing L] [AddCommGroup V]
    [Module K V] [LieRingModule L V] [FiniteDimensional K V] {s : LieSubmodule K L V} :
    finrank K s < finrank K V ↔ s < ⊤ := by
  simpa [lt_top_iff_ne_top] using s.toSubmodule.finrank_lt_iff

@[simp]
lemma finrank_quotient {R L : Type*} {M : Type u} [CommRing R] [Nontrivial R]
    [LieRing L] [AddCommGroup M] [Module R M] [HasRankNullity.{u} R] [LieRingModule L M]
    [Module.Finite R M] (s : LieSubmodule R L M) :
    finrank R (M ⧸ s) = finrank R M - finrank R s := by
  simpa using s.toSubmodule.finrank_quotient (R := R)

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing.IsNilpotent L] (s : LieIdeal R L) : LieRing.IsNilpotent (L ⧸ s) :=
  (LieIdeal.Quotient.surjective_mk' s).lieAlgebra_isNilpotent

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieAlgebra.IsSolvable L] (s : LieIdeal R L) : LieAlgebra.IsSolvable (L ⧸ s) :=
  (LieIdeal.Quotient.surjective_mk' s).lieAlgebra_isSolvable

end LieSubmodule

end LieModuleModule

end ForMathlib

open Function Set Module LieAlgebra LieModule LieSubmodule LieIdeal
open scoped Pointwise

namespace LieAlgebra

variable {K 𝔫 : Type*}
variable [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

lemma IsAdo.of_isNilpotent_of_isFaithful_center
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔫 V]
    [LieModule K 𝔫 V] [IsFaithful K (center K 𝔫) V] [LieModule.IsNilpotent 𝔫 V] :
    IsAdo K 𝔫 := by
  suffices IsFaithful K 𝔫 (𝔫 × V) from .intro (𝔫 × V)
  rename IsFaithful K (center K 𝔫) V => h
  rw [isFaithful_iff_ker_eq_bot] at h ⊢
  simpa [← disjoint_iff] using h

public lemma IsAdo.of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing K 𝔫 with
  | zero => rw [finrank_zero_iff] at hn; exact .intro Unit
  | succ n hin =>
    by_cases h𝔫 : IsLieAbelian 𝔫
    case pos => exact .of_isLieAbelian
    replace h𝔫 : ∃ 𝔞 : LieIdeal K 𝔫, finrank K 𝔞 = n ∧ center K 𝔫 ≤ 𝔞 := by
      rw [isLieAbelian_iff_center_eq_top K, ← ne_eq, ← lt_top_iff_ne_top, ← finrank_lt_iff,
        ← Nat.sub_pos_iff_lt, ← finrank_quotient, finrank_pos_iff] at h𝔫
      have h𝔫' := derivedSeries_lt_top_of_solvable K (𝔫 ⧸ center K 𝔫)
      simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient,
        ← Order.one_le_iff_pos] at h𝔫'
      apply Nat.exists_eq_add_of_le' at h𝔫'
      have : IsLieAbelian ((𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1) :=
        { trivial x y := by
            obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
            obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
            simp [← Quotient.mk_bracket, lie_mem_lie] }
      obtain ⟨m, hm⟩ := h𝔫'
      -- 後で別の補題に分離
      have h𝔞' : ∃ 𝔞' : Submodule K ((𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1),
          finrank K 𝔞' = m := by
        obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank
          (by lia : m ≤ finrank K ((𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1))
        existsi Submodule.span K (range f)
        simp [finrank_span_eq_card hf]
      replace h𝔞' : ∃ 𝔞' : LieIdeal K ((𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1),
          finrank K 𝔞' = m := by
        obtain ⟨𝔞', h𝔞'⟩ := h𝔞'
        existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
        simp_rw [← finrank_toSubmodule, h𝔞']
      obtain ⟨𝔞', rfl⟩ := h𝔞'
      existsi comap ((LieIdeal.Quotient.mk' _).comp (LieIdeal.Quotient.mk' _)) 𝔞'
      constructor
      case right => grw [comap_comp, ← LieHom.ker_le_comap, LieIdeal.Quotient.mk'_ker]
      rw [← LieHom.lieIdealComap ((LieIdeal.Quotient.mk' _).comp (LieIdeal.Quotient.mk' _)) 𝔞'
        |>.finrank_range_add_finrank_ker]
      simp_rw [LieHom.lieIdealComap_ker]
      sorry
    sorry

end LieAlgebra
