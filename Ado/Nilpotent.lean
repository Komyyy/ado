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

open Function Module LieIdeal

universe u

namespace LieIdeal.Quotient

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simps]
def mk' (s : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ s :=
  { s.toSubmodule.mkQ with
    toFun := LieSubmodule.Quotient.mk
    map_lie' {_ _} := rfl }

@[simp]
theorem surjective_mk' (s : LieIdeal R L) : Function.Surjective (mk' s) :=
  Quot.mk_surjective

@[simp]
theorem mk'_ker (s : LieIdeal R L) : (mk' s).ker = s := by
  ext; simp

end LieIdeal.Quotient

@[congr]
lemma LieSubalgebra.finrank_congr {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieSubalgebra R L} (h : p = q) : finrank R p = finrank R q :=
  (LieEquiv.ofEq p q (by simp [h])).toLinearEquiv.finrank_eq

@[congr]
lemma Submodule.finrank_congr {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} (h : p = q) : finrank R p = finrank R q :=
  (LinearEquiv.ofEq p q h).finrank_eq

namespace LieIdeal

@[congr]
lemma finrank_congr {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} (h : p = q) : finrank R p = finrank R q :=
  (LieEquiv.ofEq p.toLieSubalgebra q.toLieSubalgebra (by simp [h])).toLinearEquiv.finrank_eq

@[simp]
lemma finrank_toLieSubalgebra {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R p.toLieSubalgebra = finrank R p :=
  rfl

@[simp]
lemma finrank_toSubmodule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R p.toSubmodule = finrank R p :=
  rfl

lemma finrank_lt_iff {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    {p : LieIdeal K L} :
    finrank K p < finrank K L ↔ p < ⊤ := by
  simpa [lt_top_iff_ne_top] using p.toSubmodule.finrank_lt_iff

@[simp]
lemma finrank_top {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] :
    finrank R (⊤ : LieIdeal R L) = finrank R L :=
  _root_.finrank_top R L

def lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (p q : LieIdeal R L) :
    LieIdeal R q :=
  comap (incl q) p

@[simp]
lemma comap_incl {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (p q : LieIdeal R L) :
    comap (incl q) p = lieIdealOf p q :=
  rfl

@[simp]
lemma mem_lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} {x} : x ∈ lieIdealOf p q ↔ (x : L) ∈ p :=
  Iff.rfl

@[simps]
def lieIdealOfEquivOfLe {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {p q : LieIdeal R L} (h : p ≤ q) : lieIdealOf p q ≃ₗ⁅R⁆ p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, h x.2⟩, x.2⟩
  map_add' x y := rfl
  map_smul' x y := rfl
  map_lie' {x y} := rfl

@[simp]
lemma finrank_lieIdealOf {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p q : LieIdeal R L) (h : p ≤ q) : finrank R (lieIdealOf p q) = finrank R p :=
  (lieIdealOfEquivOfLe h).toLinearEquiv.finrank_eq

@[simp]
lemma finrank_quotient_toSubmodule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : LieIdeal R L) : finrank R (L ⧸ p.toSubmodule) = finrank R (L ⧸ p) :=
  rfl

@[simp]
lemma finrank_quotient {R : Type*} {L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Nontrivial R] [HasRankNullity.{u} R] [Module.Finite R L] (p : LieIdeal R L) :
    finrank R (L ⧸ p) = finrank R L - finrank R p := by
  simpa using p.toSubmodule.finrank_quotient (R := R)

@[simp]
lemma finrank_le {R : Type*} {L : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
    [Nontrivial R] [HasRankNullity.{u} R] [Module.Finite R L] (p : LieIdeal R L) :
    finrank R p ≤ finrank R L :=
  p.toSubmodule.finrank_le

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing.IsNilpotent L] (s : LieIdeal R L) : LieRing.IsNilpotent (L ⧸ s) :=
  (LieIdeal.Quotient.surjective_mk' s).lieAlgebra_isNilpotent

instance {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing.IsNilpotent L] (s : LieIdeal R L) : LieRing.IsNilpotent s :=
  s.incl_injective.lieAlgebra_isNilpotent

end LieIdeal

namespace LieHom

lemma finrank_range_add_finrank_ker {K L L₂ : Type*} [Field K]
    [LieRing L] [LieAlgebra K L] [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L]
    (f : L →ₗ⁅K⁆ L₂) : Module.finrank K f.range + Module.finrank K f.ker = Module.finrank K L :=
  f.toLinearMap.finrank_range_add_finrank_ker

lemma finrank_idealRange_add_finrank_ker {K L L₂ : Type*} [Field K]
    [LieRing L] [LieAlgebra K L] [LieRing L₂] [LieAlgebra K L₂] [FiniteDimensional K L]
    (f : L →ₗ⁅K⁆ L₂) (hf : IsIdealMorphism f) :
    Module.finrank K f.idealRange + Module.finrank K f.ker = Module.finrank K L := by
  convert f.finrank_range_add_finrank_ker using 2; simp [← hf.eq]

def lieIdealComap {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) : comap f q →ₗ⁅R⁆ q where
  toLinearMap := LinearMap.submoduleComap f.toLinearMap q
  map_lie' {_ _} := Subtype.ext f.map_lie'

@[simp]
lemma lieIdealComap_apply_coe {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (x : comap f q) :
    (lieIdealComap f q x : L₂) = f x :=
  rfl

@[simp]
lemma lieIdealComap_surjective_of_surjective {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (hf : Surjective f) : Surjective (lieIdealComap f q) :=
  LinearMap.submoduleComap_surjective_of_surjective f.toLinearMap q hf

@[simp]
lemma lieIdealComap_ker {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) :
    ker (lieIdealComap f q) = lieIdealOf (ker f) (comap f q) := by
  ext; simp [Subtype.ext_iff]

end LieHom

end LieModuleModule

end ForMathlib

open Function Set Module LieAlgebra LieModule LieSubmodule LieIdeal LieHom
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
  -- `lieIdealOf` の問題を解決しても `Disjoint` の可換性の問題で詰む
  simpa [← disjoint_iff, - comap_incl] using h

public lemma IsAdo.of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing 𝔫 with
  | zero => rw [finrank_zero_iff] at hn; exact .intro Unit
  | succ n hin =>
    by_cases h𝔫 : IsLieAbelian 𝔫
    case pos => exact .of_isLieAbelian
    replace h𝔫 : ∃ 𝔞 : LieIdeal K 𝔫, finrank K 𝔞 = n ∧ center K 𝔫 ≤ 𝔞 := by
      rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K (𝔫 ⧸ center K 𝔫),
          finrank K 𝔞' + 1 = finrank K (𝔫 ⧸ center K 𝔫)
      · existsi comap (LieIdeal.Quotient.mk' (center K 𝔫)) 𝔞'
        constructor
        case right => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
        simp_rw [
          ← (LieIdeal.Quotient.mk' (center K 𝔫)).lieIdealComap 𝔞'
            |>.finrank_idealRange_add_finrank_ker
              (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
              (LieIdeal.Quotient.surjective_mk' _))),
          idealRange_eq_top_of_surjective _
            (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
          LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker]
        conv =>
          enter [1, 2]
          apply finrank_lieIdealOf
          tactic => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
        rw [finrank_quotient, eq_tsub_iff_add_eq_of_le (by simp)] at h𝔞'
        lia
      let 𝔫' := (𝔫 ⧸ center K 𝔫) ⧸ derivedSeries K (𝔫 ⧸ center K 𝔫) 1
      rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K 𝔫', finrank K 𝔞' + 1 = finrank K 𝔫'
      · existsi comap (LieIdeal.Quotient.mk' (derivedSeries K (𝔫 ⧸ center K 𝔫) 1)) 𝔞'
        simp_rw [
          ← (LieIdeal.Quotient.mk' (derivedSeries K (𝔫 ⧸ center K 𝔫) 1)).lieIdealComap 𝔞'
            |>.finrank_idealRange_add_finrank_ker
              (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
              (LieIdeal.Quotient.surjective_mk' _))),
          idealRange_eq_top_of_surjective _
            (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
          LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker]
        conv =>
          enter [1, 1, 2]
          apply finrank_lieIdealOf
          tactic => grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
        rw [finrank_quotient, eq_tsub_iff_add_eq_of_le (by simp [- finrank_quotient])] at h𝔞'
        subst 𝔫'
        lia
      rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : Submodule K 𝔫', finrank K 𝔞' + 1 = finrank K 𝔫'
      · have : IsLieAbelian 𝔫' := by
          subst 𝔫'
          refine { trivial x y := ?_ }
          obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
          obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
          simp [← Quotient.mk_bracket, lie_mem_lie]
        existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
        simp_rw [← finrank_toSubmodule, h𝔞']
      suffices h𝔫' : 0 < finrank K 𝔫' by
        rw [← Order.one_le_iff_pos] at h𝔫'
        apply Nat.exists_eq_add_of_le' at h𝔫'
        obtain ⟨m, hm⟩ := h𝔫'
        obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (by lia : m ≤ finrank K 𝔫')
        existsi Submodule.span K (range f)
        simp [finrank_span_eq_card hf, hm]
      subst 𝔫'
      rw [isLieAbelian_iff_center_eq_top K, ← ne_eq, ← lt_top_iff_ne_top, ← finrank_lt_iff,
        ← Nat.sub_pos_iff_lt, ← finrank_quotient, finrank_pos_iff] at h𝔫
      have h𝔫' := derivedSeries_lt_top_of_solvable K (𝔫 ⧸ center K 𝔫)
      simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔫'
      exact h𝔫'
    obtain ⟨𝔞, rfl, h𝔞⟩ := h𝔫
    specialize hin rfl
    obtain ⟨𝔥, h𝔥⟩ : ∃ 𝔥 : LieSubalgebra K 𝔫, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      rw [← Submodule.finrank_add_eq_of_isCompl h𝔥', finrank_toSubmodule,
        Nat.add_left_cancel_iff, finrank_eq_one_iff'] at hn
      obtain ⟨v, hv₁, hv₂⟩ := hn
      existsi
        { toSubmodule := 𝔥'
          lie_mem' {x y} hx hy := by
            obtain ⟨x', rfl, rfl⟩ : ∃ x' : 𝔥', x = x'.1 ∧ hx ≍ x'.2 := ⟨⟨x, hx⟩, rfl, HEq.rfl⟩
            obtain ⟨y', rfl, rfl⟩ : ∃ y' : 𝔥', y = y'.1 ∧ hy ≍ y'.2 := ⟨⟨y, hy⟩, rfl, HEq.rfl⟩
            obtain ⟨c₁, rfl⟩ := hv₂ x'
            obtain ⟨c₂, rfl⟩ := hv₂ y'
            simp }
      exact h𝔥'
    sorry

end LieAlgebra
