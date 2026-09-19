/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Nilpotent

/-!
## 可解 Lie 代数に対する Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section ForMathlib

public section IdealOperation

variable {R : Type*} [Semiring R]

open scoped Pointwise

namespace Ideal

instance (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] : (I ⊔ J).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    rw [Submodule.mem_sup] at ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := ha
    rw [add_mul]
    solve_by_elim (transparency := .reducible) (maxDepth := 10)
      [add_mem, Ideal.mul_mem_right, Ideal.mem_sup_left, Ideal.mem_sup_right]

lemma mul_eq_span_mul (I J : Ideal R) : I * J = span (I * J : Set R) :=
  Submodule.mul_def_noncomm I J

lemma pow_eq_span_pow_set (I : Ideal R) (n : ℕ) : I ^ n = span (I ^ n : Set R) :=
  Submodule.pow_eq_span_pow_set_noncomm I n

lemma span_pow (S : Set R) (n : ℕ) [(span S).IsTwoSided] :
    span S ^ n = span (S ^ n : Set R) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : (span (S ^ n : Set R)).IsTwoSided := by rw [← hn]; infer_instance
    rw [Submodule.pow_succ, hn, span_mul_span, pow_succ]

lemma mul_subset_mul (I J : Ideal R) : (I * J : Set R) ⊆ ↑(I * J) :=
  Submodule.mul_subset_mul I J

lemma pow_subset_pow (I : Ideal R) (n : ℕ) : (I : Set R) ^ n ⊆ ↑(I ^ n) :=
  Submodule.pow_subset_pow I

-- 後で `Submodule` に拡張
lemma sup_eq_span (I J : Ideal R) : I ⊔ J = span (I ∪ J) := by
  simp

@[elab_as_elim]
theorem span_induction {s : Set R} {p : (x : R) → x ∈ span s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (zero : p 0 (Ideal.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Ideal.add_mem _ ‹_› ‹_›))
    (mul : ∀ (a : R) (x hx), p x hx → p (a * x) (Ideal.mul_mem_left _ _ ‹_›)) {x}
    (hx : x ∈ span s) : p x hx :=
  Submodule.span_induction mem zero add mul hx

end Ideal

namespace TwoSidedIdeal

@[simp]
lemma fromIdeal_span {R : Type*} [Ring R] (S : Set R) : fromIdeal (Ideal.span S) = span S := by
  apply eq_of_forall_ge_iff
  intro I
  rw [TwoSidedIdeal.gc.le_iff_le, span_le, Ideal.span_le, coe_asIdeal]

lemma _root_.Ideal.le_toTwoSidedIdeal {R : Type*} [Ring R] {I : TwoSidedIdeal R} {J : Ideal R}
    [J.IsTwoSided] : I ≤ J.toTwoSided ↔ asIdeal I ≤ J := by
  simp [IsConcreteLE.le_iff]

lemma _root_.Ideal.toTwoSidedIdeal_le {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
    {J : TwoSidedIdeal R} : I.toTwoSided ≤ J ↔ I ≤ asIdeal J := by
  simp [IsConcreteLE.le_iff]

end TwoSidedIdeal

end IdealOperation

public section LieAssociative

variable {A : Type*} [Ring A]

open List Function

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieRing

lemma mul_lie_of_associative (x y z : A) : ⁅x * y, z⁆ = ⁅x, z⁆ * y + x * ⁅y, z⁆ := by
  simp_rw [of_associative_ring_bracket]; noncomm_ring

lemma list_prod_ofFn_lie_of_associative {n} (f : Fin n → A) (x : A) :
    ⁅prod (ofFn f), x⁆ = ∑ i : Fin n, prod (ofFn (update f i ⁅f i, x⁆)) := by
  induction f using Fin.consInduction with
  | elim0 => simp [of_associative_ring_bracket]
  | cons y f hf =>
    simp_rw [ofFn_cons, prod_cons, mul_lie_of_associative, hf, Fin.sum_univ_succ,
      Fin.update_cons_zero, Fin.cons_zero, ← Fin.cons_update, ofFn_cons, prod_cons, Fin.cons_succ,
      Finset.mul_sum]

end LieRing

end LieAssociative

public section UniversalEnvelopingAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

open Function TensorAlgebra

namespace UniversalEnvelopingAlgebra

lemma mkAlgHom_tprod_lie_of_associative {n} (f : Fin n → L) (x : L) :
    ⁅mkAlgHom R L (tprod R L n f), ι R x⁆ =
      ∑ i : Fin n, mkAlgHom R L (tprod R L n (update f i ⁅f i, x⁆)) := by
  simp_rw [tprod_apply, ← List.prod_hom, List.map_ofFn, comp_def, ← ι_apply,
    LieRing.list_prod_ofFn_lie_of_associative, ← LieHom.map_lie,
    apply_update (f := fun _ ↦ ι R) (g := f)]

end UniversalEnvelopingAlgebra

end UniversalEnvelopingAlgebra

public section UniversalEnvelopingAlgebraIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

open Ideal TensorAlgebra

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

instance (I : LieIdeal R L) : (span (ι R '' (I : Set L))).IsTwoSided where
  mul_mem_of_left {a} b ha := by
    induction ha using span_induction with
    | mem a h =>
      simp only [Set.mem_image, SetLike.mem_coe] at h
      obtain ⟨x, hx, rfl⟩ := h
      induction b with | mkAlgHom b
      revert x hx b
      conv =>
        equals Submodule.map₂ (LinearMap.mul R (UniversalEnvelopingAlgebra R L))
            (Submodule.map (ι R).toLinearMap I.toSubmodule)
              (LinearMap.range (mkAlgHom R L).toLinearMap) ≤
                Submodule.restrictScalars R (span (ι R '' (I : Set L))) =>
        simp [Submodule.map₂_le]
      conv_lhs =>
        enter [2]; rw [← Submodule.span_eq (Submodule.map (ι R).toLinearMap I.toSubmodule)]
      simp_rw [← Submodule.map_top, ← span_tprod_eq_top, Submodule.map_span,
        Submodule.map₂_span_span, Submodule.span_le, Set.image2_subset_iff]
      conv =>
        equals ∀ᵉ (x ∈ I) (n) (f : Fin n → L),
            ι R x * mkAlgHom R L (tprod R L n f) ∈ span ((ι R) '' I) =>
          simp [- TensorAlgebra.tprod_apply, - ι_apply]; grind only
      intro x hx n f
      induction n using Nat.strong_induction_on generalizing x with
      | _ n hn =>
        conv_rhs =>
          equals mkAlgHom R L (tprod R L n f) * ι R x - ⁅mkAlgHom R L (tprod R L n f), ι R x⁆ =>
            simp_rw [LieRing.of_associative_ring_bracket]; noncomm_ring
        refine sub_mem (Ideal.mul_mem_left _ _ ?hx) ?_
        case hx => grw [← SetLike.mem_coe, ← Ideal.subset_span]; exact Set.mem_image_of_mem (ι R) hx
        simp_rw [mkAlgHom_tprod_lie_of_associative]
        apply Ideal.sum_mem
        rintro ⟨i, hi⟩ -
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = i + (m + 1) := by existsi n - (i + 1); lia
        cases f using Fin.appendCases with | append f g
        cases g using Fin.consCases with | cons y g
        simp_rw [show Fin.mk i hi = Fin.natAdd i ⟨0, by lia⟩ by ext; simp, Fin.update_append_natAdd,
          Fin.append_right, Fin.mk_zero, Fin.update_cons_zero, Fin.cons_zero,
          ← TensorAlgebra.tprod_mul_tprod, ← TensorAlgebra.ι_mul_tprod, map_mul, ← ι_apply]
        apply Ideal.mul_mem_left
        apply hn
        · lia
        exact LieSubmodule.lie_mem _ hx
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ hia₁ hia₂ => simp only [add_mul, add_mem, hia₁, hia₂]
    | mul x a ha hia => simp only [mul_assoc, Ideal.mul_mem_left, hia]

end UniversalEnvelopingAlgebra

end UniversalEnvelopingAlgebraIdeal

end ForMathlib

open Set Module LieAlgebra LieModule LieHom LieSubmodule SemiDirectSum UniversalEnvelopingAlgebra
open scoped Pointwise

variable {K 𝔯 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔯] [LieAlgebra K 𝔯] [FiniteDimensional K 𝔯]

-- 注意: 正標数では成り立たない。別ファイルの反例を参照。
public axiom LieIdeal.lieIdealOf_nilradical_eq_of_le [CharZero K] [FiniteDimensional K 𝔯]
    (I : LieIdeal K 𝔯) (hN : nilradical K 𝔯 ≤ I) :
    nilradical K I = lieIdealOf (nilradical K 𝔯) I

variable [LieAlgebra.IsSolvable 𝔯]

variable (K 𝔯) in
lemma LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔯r : finrank K (𝔯 ⧸ nilradical K 𝔯) = n + 1) :
    ∃ 𝔞 : LieIdeal K 𝔯, finrank K (𝔞 ⧸ nilradical K 𝔞) = n ∧ nilradical K 𝔯 ≤ 𝔞 := by
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K (𝔯 ⧸ nilradical K 𝔯),
      finrank K 𝔞' + 1 = finrank K (𝔯 ⧸ nilradical K 𝔯)
  · existsi comap (LieIdeal.Quotient.mk' (nilradical K 𝔯)) 𝔞'
    have h𝔞'n : nilradical K 𝔯 ≤ comap (Quotient.mk' (nilradical K 𝔯)) 𝔞'
    · grw [← ker_le_comap, LieIdeal.Quotient.mk'_ker]
    constructor
    case right => assumption
    simp_rw [finrank_quotient,
      ← (LieIdeal.Quotient.mk' (nilradical K 𝔯)).lieIdealComap 𝔞'
        |>.finrank_idealRange_add_finrank_ker
          (isIdealMorphism_of_surjective _ (lieIdealComap_surjective_of_surjective _ _
          (LieIdeal.Quotient.surjective_mk' _))),
      idealRange_eq_top_of_surjective _
        (lieIdealComap_surjective_of_surjective _ _ (LieIdeal.Quotient.surjective_mk' _)),
      LieIdeal.finrank_top, lieIdealComap_ker, LieIdeal.Quotient.mk'_ker,
      lieIdealOf_nilradical_eq_of_le _ h𝔞'n, finrank_lieIdealOf _ _ h𝔞'n]
    lia
  let 𝔯' := (𝔯 ⧸ nilradical K 𝔯) ⧸ derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : LieIdeal K 𝔯', finrank K 𝔞' + 1 = finrank K 𝔯'
  · existsi comap (LieIdeal.Quotient.mk' (derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1)) 𝔞'
    simp_rw [
      ← (LieIdeal.Quotient.mk' (derivedSeries K (𝔯 ⧸ nilradical K 𝔯) 1)).lieIdealComap 𝔞'
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
    subst 𝔯'
    lia
  rsuffices ⟨𝔞', h𝔞'⟩ : ∃ 𝔞' : Submodule K 𝔯', finrank K 𝔞' + 1 = finrank K 𝔯'
  · have : IsLieAbelian 𝔯' := by
      subst 𝔯'
      refine { trivial x y := ?_ }
      obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
      obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ y
      simp [← Quotient.mk_bracket, lie_mem_lie]
    existsi { toSubmodule := 𝔞', lie_mem _ := by simp [trivial_lie_zero] }
    simp_rw [← finrank_toSubmodule, h𝔞']
  suffices h𝔯' : 0 < finrank K 𝔯' by
    rw [← Order.one_le_iff_pos] at h𝔯'
    apply Nat.exists_eq_add_of_le' at h𝔯'
    obtain ⟨m, hm⟩ := h𝔯'
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (by lia : m ≤ finrank K 𝔯')
    existsi Submodule.span K (range f)
    simp [finrank_span_eq_card hf, hm]
  subst 𝔯'
  have : Nontrivial (𝔯 ⧸ LieAlgebra.nilradical K 𝔯)
  · simp [← finrank_pos_iff (R := K), h𝔯r]
  have h𝔯' := derivedSeries_lt_top_of_solvable K (𝔯 ⧸ nilradical K 𝔯)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔯'
  exact h𝔯'

section Step

variable {𝔞 𝔥 : Type*}
variable [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥] [IsAdo K 𝔞]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)
variable (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (SemiDirectSum.inl ψ))

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K 𝔞) in
noncomputable def annihilatingIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) ⊔ Ideal.span (ι K '' nilradical K 𝔞)
deriving Ideal.IsTwoSided

variable (K 𝔞) in
noncomputable def nilIdeal : Ideal (UniversalEnvelopingAlgebra K 𝔞) :=
  annihilatingIdeal K 𝔞 ^ nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)
deriving Ideal.IsTwoSided

omit [CharZero K] in
lemma nilIdeal_le {I} : nilIdeal K 𝔞 ≤ I ↔
    ∀ l : List (UniversalEnvelopingAlgebra K 𝔞),
      List.length l = nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) →
      (∀ x ∈ l, lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) x = 0 ∨ x ∈ Ideal.span (ι K '' nilradical K 𝔞)) →
          List.prod l ∈ I := by
  have : (Ideal.span (RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) ∪
      Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) :
        Set (UniversalEnvelopingAlgebra K 𝔞))).IsTwoSided := by
    rw [← Ideal.sup_eq_span]; infer_instance
  simp_rw [nilIdeal, annihilatingIdeal, Ideal.sup_eq_span, Ideal.span_pow, Ideal.span_le,
    Set.pow_subset]
  simp

omit [CharZero K] in
variable (K 𝔞) in
lemma nilIdeal_le_ker_lift_toEnd :
    nilIdeal K 𝔞 ≤ RingHom.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))) := by
  simp_rw [nilIdeal_le, RingHom.mem_ker]
  intro l hll hl
  by_cases! hf₂ : ∃ x ∈ l, lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) x = 0
  case pos =>
    obtain ⟨x, hxl, hx⟩ := hf₂
    rw [map_list_prod]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exists x
  case neg =>
    replace hl x hx := (hl x hx).resolve_left (hf₂ x hx)
    clear hf₂
    revert l hll hl
    conv =>
      equals (Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) : Set (UniversalEnvelopingAlgebra K 𝔞)) ^
          nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) ⊆
            lift K (toEnd K 𝔞 (AdoSpace K 𝔞)) ⁻¹' {0} =>
        simp [Set.pow_subset]
    have : (Ideal.span
        (Ideal.span (ι K '' (nilradical K 𝔞 : Set 𝔞)) :
          Set (UniversalEnvelopingAlgebra K 𝔞))).IsTwoSided := by
      rw [Ideal.span_eq]; infer_instance
    simp_rw [← RingHom.ker_eq, ← Ideal.span_le, ← Ideal.span_pow, Ideal.span_eq, Ideal.span_pow,
      Ideal.span_le, RingHom.ker_eq, Set.pow_subset]
    intro l hll hl
    replace hl : l ∈ range (List.map (ι K ∘ ((↑) : nilradical K 𝔞 → 𝔞)))
    · simp_rw [Set.range_list_map, Set.range_comp, Subtype.range_coe_subtype,
        SetLike.setOfPred_mem_eq, Set.mem_ofPred]
      exact hl
    rw [Set.mem_range] at hl
    obtain ⟨l, rfl⟩ := hl
    rw [List.length_map] at hll
    conv =>
      equals ∀ x,
         (List.map (toEnd K (nilradical K 𝔞) (AdoSpace K 𝔞)) l).prod x ∈
            lowerCentralSeries K (nilradical K 𝔞) (AdoSpace K 𝔞)
              (nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)) =>
        simp [← List.prod_hom, Function.comp_def, DFunLike.ext_iff,
          - List.map_subtype, ← LieIdeal.toEnd_eq]
    intro x
    refine list_prod_map_toEnd_apply_mem_lowerCentralSeries K l x
        (nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)) ?_
    simp [hll]

public axiom range_leftLieUE_le_annihilatingIdeal
    [CharZero K] [FiniteDimensional K 𝔞] [IsSolvable 𝔞] (x : 𝔥) :
    LinearMap.range (leftLieUE ψ x) ≤ Submodule.restrictScalars K (annihilatingIdeal K 𝔞)

variable [FiniteDimensional K 𝔞] [IsSolvable 𝔞]

lemma leftLieUE_mem_annihilatingIdeal (x : 𝔥) {a : UniversalEnvelopingAlgebra K 𝔞} :
    leftLieUE ψ x a ∈ annihilatingIdeal K 𝔞 := by
  have h := range_leftLieUE_le_annihilatingIdeal ψ x
  rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff'] at h
  simp_all

lemma map_leftLieUE_nilIdeal_le_nilIdeal (x : 𝔥) :
    Submodule.map (leftLieUE ψ x) (Submodule.restrictScalars K (nilIdeal K 𝔞)) ≤
      Submodule.restrictScalars K (nilIdeal K 𝔞) := by
  unfold nilIdeal
  generalize nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞) = n
  induction n with
  | zero => simp [Submodule.pow_zero]
  | succ n hn =>
    simp only [Submodule.map_le_iff_le_comap] at hn ⊢
    -- `Submodule.restrictScalars_mem` という名前はよく無い
    simp only [IsConcreteLE.le_iff, Submodule.mem_comap, Submodule.restrictScalars_mem] at hn
    simp_rw [Submodule.pow_succ, Submodule.restrictScalars_mul, Submodule.mul_le,
      Submodule.mem_comap, ← Submodule.restrictScalars_mul, Submodule.restrictScalars_mem]
    intro a ha b hb
    rw [leftLieUE_mul]
    solve_by_elim (maxDepth := 10) (transparency := .instances)
      [hn, add_mem, Submodule.mul_mem_mul, leftLieUE_mem_annihilatingIdeal]

lemma leftLieUE_mem_nilIdeal (x : 𝔥) {a : UniversalEnvelopingAlgebra K 𝔞}
    (ha : a ∈ nilIdeal K 𝔞) : leftLieUE ψ x a ∈ nilIdeal K 𝔞 := by
  have h := map_leftLieUE_nilIdeal_le_nilIdeal ψ x
  rw [Submodule.map_le_iff_le_comap] at h
  apply mem_of_le_of_mem at h
  simp_all

noncomputable def nilLieSubmodule : LieSubmodule K (𝔞 ⋊⁅ψ⁆ 𝔥) (UniversalEnvelopingAlgebra K 𝔞) where
  __ := Submodule.restrictScalars K (nilIdeal K 𝔞)
  lie_mem {x a} ha := by
    simp_all only [Submodule.toAddSubmonoid_restrictScalars, Submodule.carrier_eq_coe,
      SetLike.mem_coe]
    obtain ⟨x, y⟩ := x
    simp only [lieUE_def, bracket_eq]
    solve_by_elim (transparency := .reducible) [add_mem, Ideal.mul_mem_left, leftLieUE_mem_nilIdeal]

end UniversalEnvelopingAlgebra

variable [FiniteDimensional K 𝔞] [IsSolvable 𝔞]

abbrev SolStepAdoSpace :=
  UniversalEnvelopingAlgebra K 𝔞 ⧸ nilLieSubmodule ψ

namespace SolStepAdoSpace

attribute [local instance 100]
  LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

instance isFaithful_idealRange_solStepAdoSpace :
    IsFaithful K (idealRange (inl ψ)) (SolStepAdoSpace ψ) := by
  simp_rw [isFaithful_iff', (equivIdealRangeInl ψ).surjective.forall, LieEquiv.coe_coe,
    LieIdeal.coe_bracket_of_module, equivIdealRangeInl_apply_coe,
    (LieSubmodule.Quotient.surjective_mk' _).forall, ← LieModuleHom.map_lie, inl_lieUE,
    LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero',
    EmbeddingLike.map_eq_zero_iff]
  intro x hx
  suffices h : ∀ y : AdoSpace K 𝔞, ⁅x, y⁆ = 0
  · apply LieModule.ext_of_isFaithful (R := K) (M := AdoSpace K 𝔞)
    simpa using h
  intro y
  specialize hx 1
  grw [bracket_eq, ι_apply, mul_one] at hx
  apply mem_of_le_of_mem (nilIdeal_le_ker_lift_toEnd K 𝔞) at hx
  simp_rw [RingHom.mem_ker, lift_ι_apply', toEnd_eq_zero_iff] at hx
  subst hx
  simp

lemma isFaithful_center_solStepAdoSpace
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (inl ψ)) :
    IsFaithful K (center K (𝔞 ⋊⁅ψ⁆ 𝔥)) (SolStepAdoSpace ψ) where
  injective_toEnd := by
    convert
      (isFaithful_idealRange_solStepAdoSpace ψ).injective_toEnd.comp
        (LieIdeal.inclusion_injective (center_le_nilradical.trans hn))
    ext
    simp

lemma isNilpotent_nilradical_solStepAdoSpace [FiniteDimensional K 𝔥]
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ idealRange (inl ψ)) :
    IsNilpotent (nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥)) (SolStepAdoSpace ψ) := by
  simp_rw +singlePass [LieModule.isNilpotent_iff_forall (R := K),
    LieIdeal.lieIdealOfEquivOfLe hn |>.surjective.forall, LieEquiv.coe_coe, LieIdeal.toEnd_eq,
    LieIdeal.lieIdealOfEquivOfLe_toFun_coe, Subtype.forall,
    ← LieIdeal.lieIdealOf_nilradical_eq_of_le _ hn, ← map_equiv_nilradical (equivIdealRangeInl ψ),
    (equivIdealRangeInl ψ).surjective.forall, LieEquiv.coe_coe, LieEquiv.mem_map_equiv,
    LieEquiv.symm_apply_apply, equivIdealRangeInl_apply_coe]
  intro x hx
  exists nilpotencyLength (nilradical K 𝔞) (AdoSpace K 𝔞)
  simp_rw [DFunLike.ext_iff, (LieSubmodule.Quotient.surjective_mk' _).forall, toEnd_pow_apply_map,
    LinearMap.zero_apply, LieSubmodule.Quotient.mk_eq_zero, toEndUE_inl, toEnd_eq,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
  intro a
  apply Ideal.mul_mem_right
  simp_rw [nilIdeal, annihilatingIdeal, Ideal.pow_eq_span_pow_set, ← SetLike.mem_coe,
    Ideal.sup_eq_span]
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.pow_mem_pow
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_union_right
  apply mem_of_subset_of_mem Ideal.subset_span
  apply Set.mem_image_of_mem
  simp [hx]

@[instance]
public axiom finiteDimensional_solStepAdoSpace [FiniteDimensional K 𝔥] :
    FiniteDimensional K (SolStepAdoSpace ψ)

end SolStepAdoSpace

end Step

-- 一般の場合でも使うので公開
public lemma LieAlgebra.IsAdo.semiDirectSum_of_isSolvable {𝔞 𝔥 : Type*}
    [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
    [FiniteDimensional K 𝔞] [FiniteDimensional K 𝔥] [IsAdo K 𝔞]
    (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞) [IsSolvable 𝔞]
    (hn : nilradical K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (inl ψ).idealRange) :
    IsAdo K (𝔞 ⋊⁅ψ⁆ 𝔥) := by
  have := SolStepAdoSpace.isFaithful_center_solStepAdoSpace ψ hn
  have := SolStepAdoSpace.isNilpotent_nilradical_solStepAdoSpace ψ hn
  exact .of_isNilpotent_of_isFaithful_center (SolStepAdoSpace ψ)

lemma LieAlgebra.IsAdo.of_isInnerSemiDirectSum_of_isSolvable
    (𝔞 : LieIdeal K 𝔯) (𝔥 : LieSubalgebra K 𝔯)
    (hi : IsInnerSemiDirectSum 𝔞 𝔥) (hn : nilradical K 𝔯 ≤ 𝔞) [IsAdo K 𝔞] : IsAdo K 𝔯 := by
  rw [(lieEquivLieSubalgebra hi).symm.isAdo_iff]
  have := (lieEquivLieSubalgebra hi).injective.lieAlgebra_isSolvable
  apply (LieIdeal.map_mono (f := (lieEquivLieSubalgebra hi).symm.toLieHom)).imp at hn
  rw [map_equiv_nilradical] at hn
  conv_rhs at hn => equals idealRange (inl ((LieDerivation.adoIdeal 𝔞).comp 𝔥.incl)) =>
    ext ⟨x, y⟩
    have h : y.1 ∈ 𝔞 ↔ y = 0 :=
      Submodule.mem_left_iff_eq_zero_of_disjoint hi.disjoint
    simp [add_mem_cancel_left, eq_comm (a := 0) (b := y), h]
  exact .semiDirectSum_of_isSolvable _ hn

public local instance LieAlgebra.IsAdo.of_isSolvable : IsAdo K 𝔯 := by
  generalize hn : finrank K (𝔯 ⧸ nilradical K 𝔯) = n
  induction n generalizing 𝔯 with
  | zero =>
    rw [LieIdeal.finrank_quotient, Nat.sub_eq_zero_iff_le, ← not_lt, LieIdeal.finrank_lt_iff,
      not_lt_top_iff, ← top_le_iff, ← LieIdeal.isNilpotent_iff_le_nilradical,
      LieRing.isNilpotent_lieIdeal_top_iff] at hn
    exact IsAdo.of_isNilpotent
  | succ n hin =>
    rsuffices ⟨𝔞, 𝔥, hi, hc, _⟩ : ∃ (𝔞 : LieIdeal K 𝔯) (𝔥 : LieSubalgebra K 𝔯),
        IsInnerSemiDirectSum 𝔞 𝔥 ∧ nilradical K 𝔯 ≤ 𝔞 ∧ IsAdo K 𝔞
    · exact .of_isInnerSemiDirectSum_of_isSolvable 𝔞 𝔥 hi hc
    obtain ⟨𝔞, hn𝔞, h𝔞⟩ := LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian K 𝔯 n hn
    specialize hin hn𝔞
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔯, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      simp_rw [← hn𝔞, LieIdeal.finrank_quotient, 𝔞.lieIdealOf_nilradical_eq_of_le h𝔞,
        LieIdeal.finrank_lieIdealOf _ _ h𝔞, ← Submodule.finrank_add_eq_of_isCompl h𝔥',
        LieIdeal.finrank_toSubmodule] at hn
      conv at hn => equals finrank K 𝔥' = 1 => grind only [LieIdeal.finrank_mono h𝔞]
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨𝔞, 𝔥, h𝔥₁.isInnerSemidirectSum, h𝔞, hin⟩
