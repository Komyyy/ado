/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.DirectSum
public import Ado.ForMathlib.FinAdd
public import Ado.ForMathlib.LieFinrank
public import Ado.ForMathlib.LieHom
public import Ado.ForMathlib.LieIdealCoe
public import Ado.ForMathlib.LieModuleKer
public import Ado.ForMathlib.LieModulePUnit
public import Ado.ForMathlib.LieModuleSubsingleton
public import Ado.ForMathlib.TensorAlgebra
public import Ado.ForMathlib.UniversalEnvelopingAlgebra
public import Ado.LieAbelian

section ForMathlib

@[expose] public section LieDerivation

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

namespace LieDerivation

@[simps ! apply_apply]
def adoIdeal (I : LieIdeal R L) : L →ₗ⁅R⁆ LieDerivation R I I where
  toFun x :=
    { toLinearMap := LieModule.toEnd R L I x
      leibniz' y z := by
        conv => equals ⁅x, ⁅y.1, z.1⁆⁆ = ⁅y.1, ⁅x, z.1⁆⁆ - ⁅z.1, ⁅x, y.1⁆⁆ =>
          simp [Subtype.ext_iff]
        grind only [= lie_lie, =_ lie_skew] }
  map_add' x y := by ext; simp
  map_smul' t x := by ext; simp
  map_lie' {x y} := by ext; simp

end LieDerivation

end LieDerivation

@[expose] public section LieSemiDirectSum

-- TODO: `SemidirectProduct` と同様に、`SemidirectSum` に変名

variable {R : Type*} [CommRing R]
variable {K : Type*} [LieRing K] [LieAlgebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

open LieHom LieSubalgebra LieDerivation

namespace LieAlgebra

namespace SemiDirectSum

@[simp]
lemma isIdealMorphism_inl : IsIdealMorphism (inl ψ) := by
  simp [isIdealMorphism_iff]

instance [Module.Finite R K] [Module.Finite R L] : Module.Finite R (K ⋊⁅ψ⁆ L) :=
  Module.Finite.equiv (toProdl ψ).symm

def equivIdealRangeInl : K ≃ₗ⁅R⁆ idealRange (inl ψ) where
  toLieHom :=
    comp (LieEquiv.ofEq (range (inl ψ)) (idealRange (inl ψ)) (by ext; simp)).toLieHom
      (rangeRestrict (inl ψ))
  invFun x := x.1.left
  right_inv := by
    rintro ⟨x, hx⟩
    simp only [isIdealMorphism_inl, mem_idealRange_iff, inl_eq_mk] at hx
    obtain ⟨x, rfl⟩ := hx
    rfl

@[simp]
lemma equivIdealRangeInl_apply_coe (x) : (equivIdealRangeInl ψ x).1 = inl ψ x :=
  rfl

@[simp]
lemma equivIdealRangeInl_symm_apply (x) : (equivIdealRangeInl ψ).symm x = x.1.left :=
  rfl

end SemiDirectSum

def IsInnerSemiDirectSum (I : LieIdeal R L) (L' : LieSubalgebra R L) : Prop :=
  IsCompl I.toSubmodule L'.toSubmodule

variable {I : LieIdeal R L} {L' : LieSubalgebra R L}

lemma isInnerSemiDirectSum_iff :
    IsInnerSemiDirectSum I L' ↔ IsCompl I.toSubmodule L'.toSubmodule :=
  Iff.rfl

alias ⟨IsInnerSemiDirectSum.isCompl, IsCompl.isInnerSemidirectSum⟩ :=
  isInnerSemiDirectSum_iff

namespace SemiDirectSum

noncomputable def lieEquivLieSubalgebra (h : IsInnerSemiDirectSum I L') :
    (I ⋊⁅comp (adoIdeal I) (incl L')⁆ L') ≃ₗ⁅R⁆ L where
  __ := LinearEquiv.trans (toProdl _) (Submodule.prodEquivOfIsCompl _ _ h.isCompl)
  map_lie' {x y} := by
    -- `SetLike` の defeq に対処
    have haux (x : I × L') :
        Submodule.prodEquivOfIsCompl _ _ h.isCompl x = (x.1 : L) + (x.2 : L) :=
      Submodule.coe_prodEquivOfIsCompl' ..
    conv => equals
        ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ -
          ⁅y.right.1, x.left.1⁆ + ⁅x.right.1, y.right.1⁆ =
            ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ +
              (⁅x.left.1, y.right.1⁆ + ⁅x.right.1, y.right.1⁆) =>
      -- `SetLike` の defeq に対処
      have haux (x : I × L') :
          Submodule.prodEquivOfIsCompl _ _ h.isCompl x = (x.1 : L) + (x.2 : L) :=
        Submodule.coe_prodEquivOfIsCompl' ..
      simp [haux]
    grind only [=_ lie_skew]

@[simp]
lemma lieEquivLieSubalgebra_apply (h : IsInnerSemiDirectSum I L')
    (x : I ⋊⁅comp (adoIdeal I) (incl L')⁆ L') : lieEquivLieSubalgebra h x = (x.1 : L) + (x.2 : L) :=
  rfl

lemma isInnerSemiDirectSum_self : IsInnerSemiDirectSum (idealRange (inl ψ)) (range (inr ψ)) := by
  simp_rw [isInnerSemiDirectSum_iff, isCompl_iff]
  constructor
  · simp [Submodule.disjoint_def]
  · rw [Submodule.codisjoint_iff_exists_add_eq]; simp

end SemiDirectSum

end LieAlgebra

end LieSemiDirectSum

public section LieSubobjectCoe

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]

namespace LieSubmodule

@[gcongr]
lemma toSubmodule_mono {N N' : LieSubmodule R L M} (h : N ≤ N') : (N : Submodule R M) ≤ N' :=
  (LieSubmodule.toSubmodule_le_toSubmodule _ _).mp h

end LieSubmodule

end LieSubobjectCoe

end ForMathlib

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set Finset LieAlgebra LieModule LieSubmodule LieIdeal LieHom
open Module hiding Injective
open TensorAlgebra hiding ringCon ι
open UniversalEnvelopingAlgebra hiding ι

variable {K 𝔫 : Type*}
variable [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

-- `expose` しないと `simps` でエラーになる
@[expose, simps toSubmodule]
public def Submodule.toLieSubalgebraOfDimOne (𝔥 : Submodule K 𝔫) (h𝔥 : finrank K 𝔥 = 1) :
    LieSubalgebra K 𝔫 where
  toSubmodule := 𝔥
  lie_mem' {x y} hx hy := by
    -- これ戦術化できないかな
    obtain ⟨x', rfl, rfl⟩ : ∃ x' : 𝔥, x = x'.1 ∧ hx ≍ x'.2 := ⟨⟨x, hx⟩, rfl, HEq.rfl⟩
    obtain ⟨y', rfl, rfl⟩ : ∃ y' : 𝔥, y = y'.1 ∧ hy ≍ y'.2 := ⟨⟨y, hy⟩, rfl, HEq.rfl⟩
    rw [finrank_eq_one_iff'] at h𝔥
    obtain ⟨v, hv, h𝔥⟩ := h𝔥
    obtain ⟨c₁, rfl⟩ := h𝔥 x'
    obtain ⟨c₂, rfl⟩ := h𝔥 y'
    simp

lemma LieAlgebra.IsAdo.of_isNilpotent_of_isFaithful_center
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔫 V]
    [LieModule K 𝔫 V] [IsFaithful K (center K 𝔫) V] [LieModule.IsNilpotent 𝔫 V] :
    IsAdo K 𝔫 := by
  suffices IsFaithful K 𝔫 (𝔫 × V) from .intro (𝔫 × V)
  rename IsFaithful K (center K 𝔫) V => h
  rw [isFaithful_iff_ker_eq_bot] at h ⊢
  -- `lieIdealOf` の問題を解決しても `Disjoint` の可換性の問題で詰む
  simpa [← disjoint_iff, - comap_incl] using h

variable (K 𝔫) in
lemma LieIdeal.exists_for_nilStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔫r : finrank K 𝔫 = n + 1) (h𝔫a : ¬IsLieAbelian 𝔫) :
    ∃ 𝔞 : LieIdeal K 𝔫, finrank K 𝔞 = n ∧ center K 𝔫 ≤ 𝔞 := by
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
    conv_lhs =>
      enter [2]
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
    ← Nat.sub_pos_iff_lt, ← finrank_quotient, finrank_pos_iff] at h𝔫a
  have h𝔫' := derivedSeries_lt_top_of_solvable K (𝔫 ⧸ center K 𝔫)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔫'
  exact h𝔫'

variable {𝔞 𝔥 : Type*}
variable [LieRing 𝔞] [LieAlgebra K 𝔞] [LieRing 𝔥] [LieAlgebra K 𝔥]
variable (ψ : 𝔥 →ₗ⁅K⁆ LieDerivation K 𝔞 𝔞)
variable (hc : center K (𝔞 ⋊⁅ψ⁆ 𝔥) ≤ (SemiDirectSum.inl ψ).idealRange)

namespace LieAlgebra.SemiDirectSum

open TensorAlgebra (ι)

attribute [local instance 100] LieRing.ofAssociativeRing

def leftLieUEAux (x : 𝔥) : End K (TensorAlgebra K 𝔞) :=
  LinearEquiv.conj TensorAlgebra.equivDirectSum.toLinearEquiv.symm
    (DirectSum.lmap (fun n ↦
      ∑ i : Fin n, PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i (ψ x))))

@[simp]
lemma leftLieUEAux_ι (x : 𝔥) (y : 𝔞) : leftLieUEAux ψ x (ι K y) = ι K (ψ x y) := by
  simp [leftLieUEAux]

@[simp]
lemma leftLieUEAux_tprod (x : 𝔥) {n} (f : Fin n → 𝔞) :
    leftLieUEAux ψ x (TensorAlgebra.tprod K 𝔞 n f) =
      ∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (f i))) := by
  simp [leftLieUEAux, - TensorAlgebra.tprod_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
    apply_update (f := fun (i : Fin n) (F : 𝔞 →ₗ[K] 𝔞) ↦ F (f i))]

lemma leftLieUEAux_leftLieUEAux_tprod (x y : 𝔥) {n} (f : Fin n → 𝔞) :
    leftLieUEAux ψ x (leftLieUEAux ψ y (TensorAlgebra.tprod K 𝔞 n f)) =
      (∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (ψ y (f i))))) +
        (∑ p ∈ offDiag (univ : Finset (Fin n)),
          TensorAlgebra.tprod K 𝔞 n (update (update f p.1 (ψ y (f p.1))) p.2 (ψ x (f p.2)))) :=
  calc _
    _ = ∑ i : Fin n, leftLieUEAux ψ x (TensorAlgebra.tprod K 𝔞 n (update f i (ψ y (f i)))) := by
      conv_lhs => rw [leftLieUEAux_tprod, map_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        TensorAlgebra.tprod K 𝔞 n
          (update (update f i (ψ y (f i))) j (ψ x (update f i (ψ y (f i)) j))) := by
      simp only [leftLieUEAux_tprod]
    _ = (∑ i : Fin n, TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (ψ y (f i))))) +
          (∑ i : Fin n, ∑ j ∈ ({i}ᶜ : Finset (Fin n)),
            TensorAlgebra.tprod K 𝔞 n (update (update f i (ψ y (f i))) j (ψ x (f j)))) := by
      conv_lhs =>
        conv => enter [2, i]; rw [Fintype.sum_eq_add_sum_compl i]
        rw [sum_add_distrib]
      congr! 3 with i _ i _ j hj <;> [simp; (congr! 3; apply update_of_ne; simpa using hj)]
    _ = _ := by
      congr! 1
      symm
      apply sum_finset_product
      simp [not_iff_not, iff_true_intro eq_comm]

lemma leftLieUEAux_lie_left (x y : 𝔥) (a) : leftLieUEAux ψ ⁅x, y⁆ a =
    leftLieUEAux ψ x (leftLieUEAux ψ y a) - leftLieUEAux ψ y (leftLieUEAux ψ x a) := by
  revert a
  suffices h : leftLieUEAux ψ ⁅x, y⁆ =
      leftLieUEAux ψ x * leftLieUEAux ψ y - leftLieUEAux ψ y * leftLieUEAux ψ x by
    simpa [DFunLike.ext_iff] using h
  ext n f
  conv_lhs => tactic =>
    simp_rw [leftLieUEAux_tprod, map_lie, LieDerivation.lie_apply, MultilinearMap.map_update_sub,
      sum_sub_distrib]
  conv_rhs =>
    simp only [LinearMap.sub_apply, End.mul_apply, leftLieUEAux_leftLieUEAux_tprod]
    enter [2, 2]
    conv =>
      apply_congr
      next => rfl
      tactic => rename_i p hp; rw [update_comm (by simpa using hp)]
    tactic =>
      symm
      apply sum_equiv (s := offDiag (univ : Finset (Fin n))) (Equiv.prodComm (Fin n) (Fin n))
      · simp [not_iff_not, iff_true_intro eq_comm]
      · intro i hi; simp only [Equiv.prodComm_apply, Prod.snd_swap, Prod.fst_swap]; rfl
  noncomm_ring

lemma leftLieUEAux_add_left (x y : 𝔥) (a) :
    leftLieUEAux ψ (x + y) a = leftLieUEAux ψ x a + leftLieUEAux ψ y a := by
  simp [leftLieUEAux, PiTensorProduct.map_update_add, Finset.sum_add_distrib]

lemma leftLieUEAux_smul_left (t : K) (x : 𝔥) (a) :
    leftLieUEAux ψ (t • x) a = t • leftLieUEAux ψ x a := by
  simp [leftLieUEAux, PiTensorProduct.map_update_smul, ← Finset.smul_sum]

lemma leftLieUEAux_mul (x : 𝔥) (a b) : leftLieUEAux ψ x (a * b) =
    a * leftLieUEAux ψ x b + leftLieUEAux ψ x a * b := by
  revert a b
  suffices h :
      (LinearMap.mul K (TensorAlgebra K 𝔞)).compr₂ (leftLieUEAux ψ x) =
        (LinearMap.mul K (TensorAlgebra K 𝔞)).compl₁₂ LinearMap.id (leftLieUEAux ψ x) +
          (LinearMap.mul K (TensorAlgebra K 𝔞)).compl₁₂ (leftLieUEAux ψ x) LinearMap.id by
    simpa [DFunLike.ext_iff] using h
  conv_rhs => apply add_comm
  ext m y n z
  simp [Fin.sum_univ_add, - LieSubalgebra.coe_bracket_of_module, - TensorAlgebra.tprod_apply]

lemma mkAlgHom_leftLieUEAux_eq_of_ringCon (x : 𝔥) (a b) (h : ringCon K 𝔞 a b) :
    mkAlgHom K 𝔞 (leftLieUEAux ψ x a) = mkAlgHom K 𝔞 (leftLieUEAux ψ x b) := by
  induction h using ringCon_induction with
  | refl | symm | trans | add => grind only [= map_add]
  | mul a b c d h₁ h₂ hi₁ hi₂ =>
    rw [← mkAlgHom_eq_mkAlgHom] at h₁ h₂; simp [leftLieUEAux_mul, *]
  | lie_compat a b =>
    simp_rw [map_add, ← eq_sub_iff_add_eq]
    conv_rhs => simp only [leftLieUEAux_mul, map_add, map_mul, leftLieUEAux_ι, ← ι_apply]
    conv_lhs =>
      rw [leftLieUEAux_ι, ← ι_apply, LieDerivation.apply_lie_eq_add, map_add, map_lie, map_lie,
        LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket]
    noncomm_ring

lemma ringCon_leftLieUEAux_of_ringCon (x : 𝔥) (a b) (h : ringCon K 𝔞 a b) :
    ringCon K 𝔞 (leftLieUEAux ψ x a) (leftLieUEAux ψ x b) :=
  mkAlgHom_eq_mkAlgHom.mp (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x a b h)

def leftLieUE (x : 𝔥) : End K (UniversalEnvelopingAlgebra K 𝔞) :=
  { toFun := tensorLift (mkAlgHom K 𝔞 ∘ leftLieUEAux ψ x) (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x)
    map_add' a b := by
      cases a with | mkAlgHom a
      cases b with | mkAlgHom b
      simp_rw [← map_add, tensorLift_mkAlgHom, comp_apply, map_add]
    map_smul' t a := by
      cases a with | mkAlgHom a
      simp_rw [RingHom.id_apply, ← map_smul, tensorLift_mkAlgHom, comp_apply, map_smul] }

lemma leftLieUE_def (x : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ x a =
      tensorLift (mkAlgHom K 𝔞 ∘ leftLieUEAux ψ x) (mkAlgHom_leftLieUEAux_eq_of_ringCon ψ x) a :=
  rfl

lemma leftLieUE_mkAlgHom (x : 𝔥) (a : TensorAlgebra K 𝔞) :
    leftLieUE ψ x (mkAlgHom K 𝔞 a) = mkAlgHom K 𝔞 (leftLieUEAux ψ x a) := by
  simp [leftLieUE_def]

lemma leftLieUE_add_left (x y : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ (x + y) a = leftLieUE ψ x a + leftLieUE ψ y a := by
  cases a with | mkAlgHom a; simp [leftLieUE_mkAlgHom, leftLieUEAux_add_left]

lemma leftLieUE_lie_left (x y : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ ⁅x, y⁆ a = leftLieUE ψ x (leftLieUE ψ y a) - leftLieUE ψ y (leftLieUE ψ x a) := by
  cases a with | mkAlgHom a; simp [leftLieUE_mkAlgHom, leftLieUEAux_lie_left]

lemma leftLieUE_smul_left (t : K) (x : 𝔥) (a : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ (t • x) a = t • leftLieUE ψ x a := by
  cases a with | mkAlgHom a; simp [leftLieUE_mkAlgHom, leftLieUEAux_smul_left]

@[simp]
lemma leftLieUE_mul (x : 𝔥) (a b : UniversalEnvelopingAlgebra K 𝔞) :
    leftLieUE ψ x (a * b) = a * leftLieUE ψ x b + leftLieUE ψ x a * b := by
  cases a with | mkAlgHom a
  cases b with | mkAlgHom b
  simp_rw [← map_mul, leftLieUE_mkAlgHom, leftLieUEAux_mul]
  simp

@[simp]
lemma leftLieUE_ι (x : 𝔥) (y : 𝔞) :
    leftLieUE ψ x (UniversalEnvelopingAlgebra.ι K y) = UniversalEnvelopingAlgebra.ι K (ψ x y) := by
  simp [leftLieUE_mkAlgHom]

section LengthSubmodule

-- TODO: `UniversalEnvelopingAlgebra` 名前空間に移動
variable (K 𝔞) in
def lengthSubmodule (m : ℕ) : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  Submodule.map (mkAlgHom K 𝔞).toLinearMap
    (⨆ k ≥ m, LinearMap.range (TensorPower.toTensorAlgebra (n := k)))

@[simp]
lemma mkAlgHom_tprod_mem_lengthSubmodule (m) {n} (f : Fin n → 𝔞) (hn : m ≤ n) :
    mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f) ∈ lengthSubmodule K 𝔞 m := by
  unfold lengthSubmodule
  apply Submodule.mem_map_of_mem
  apply Submodule.mem_iSup_of_mem n
  apply Submodule.mem_iSup_of_mem hn
  convert LinearMap.mem_range_self _ (PiTensorProduct.tprod K f)
  simp

lemma lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod (m) :
    lengthSubmodule K 𝔞 m =
      .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞), m ≤ n ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)} := by
  apply le_antisymm
  · simp_rw [lengthSubmodule, Submodule.map_le_iff_le_comap, iSup₂_le_iff,
      LinearMap.range_le_iff_comap, eq_top_iff, ← PiTensorProduct.span_tprod_eq_top,
      Submodule.span_le, range_subset_iff]
    intro n hn f
    apply Submodule.mem_span_of_mem
    rw [mem_ofPred]
    existsi n, f, hn
    simp
  · rw [Submodule.span_le, ofPred_subset]
    rintro _ ⟨n, f, hn, rfl⟩
    simp [hn, - TensorAlgebra.tprod_apply]

@[simp]
lemma lengthSubmodule_zero : lengthSubmodule K 𝔞 0 = ⊤ := by
  have hι := DirectSum.Decomposition.isInternal
      (fun n : ℕ ↦ LinearMap.range (TensorAlgebra.ι K : 𝔞 →ₗ[K] TensorAlgebra K 𝔞) ^ n)
  simp_rw [TensorAlgebra.ι_range_pow_eq] at hι
  apply DirectSum.IsInternal.submodule_iSup_eq_top at hι
  simp [lengthSubmodule, hι,
    LinearMap.range_eq_top_of_surjective (mkAlgHom K 𝔞).toLinearMap (mkAlgHom_surjective K 𝔞),
    - Submodule.map_iSup]

@[gcongr]
lemma lengthSubmodule_mono ⦃m n⦄ (h : m ≤ n) : lengthSubmodule K 𝔞 n ≤ lengthSubmodule K 𝔞 m := by
  simp_rw [lengthSubmodule]
  gcongr 1
  apply biSup_mono
  rwa [forall_ge_iff_le]

lemma antitone_lengthSubmodule : Antitone (lengthSubmodule K 𝔞) :=
  lengthSubmodule_mono

lemma ι_mul_mem_lengthSubmodule_succ_of_mem (m) (x : 𝔞) (a) (ha : a ∈ lengthSubmodule K 𝔞 m) :
    UniversalEnvelopingAlgebra.ι K x * a ∈ lengthSubmodule K 𝔞 (m + 1) := by
  revert a
  suffices h :
      Submodule.map (LinearMap.mul K _ (UniversalEnvelopingAlgebra.ι K x)) (lengthSubmodule K 𝔞 m)
        ≤ lengthSubmodule K 𝔞 (m + 1) by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage,
    LinearMap.mul_apply_apply]
  rintro _ ⟨n, f, hn, rfl⟩
  conv => equals
      mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 (n + 1) (Fin.cons x f))
        ∈ lengthSubmodule K 𝔞 (m + 1) =>
    simp
  exact mkAlgHom_tprod_mem_lengthSubmodule _ _ (by lia)

lemma bracket_𝔞_mem_lengthSubmodule_succ_of_mem (m) (x : 𝔞) (a) (ha : a ∈ lengthSubmodule K 𝔞 m) :
    ⁅x, a⁆ ∈ lengthSubmodule K 𝔞 (m + 1) := by
  rw [bracket_eq]
  exact ι_mul_mem_lengthSubmodule_succ_of_mem m x a ha

end LengthSubmodule

section NilSubmodule

variable [IsAdo K 𝔞]

variable (K 𝔞) in
noncomputable def nilSubmodule : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  lengthSubmodule K 𝔞 (nilpotencyLength 𝔞 (AdoSpace K 𝔞))

lemma nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod :
    nilSubmodule K 𝔞 =
      .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞), nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ n ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)} :=
  lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod (nilpotencyLength 𝔞 (AdoSpace K 𝔞))

lemma lengthSubmodule_nilpotenctLength :
    lengthSubmodule K 𝔞 (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) = nilSubmodule K 𝔞 :=
  rfl

@[simp]
lemma mkAlgHom_tprod_mem_nilSubmodule {n} (f : Fin n → 𝔞)
    (hn : nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ n) :
    mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f) ∈ nilSubmodule K 𝔞 :=
  mkAlgHom_tprod_mem_lengthSubmodule (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) f hn

@[simp]
lemma ι_mul_mem_nilSubmodule_of_mem (x : 𝔞) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    UniversalEnvelopingAlgebra.ι K x * a ∈ nilSubmodule K 𝔞 := by
  rw [← lengthSubmodule_nilpotenctLength] at ha ⊢
  grw [(by lia : nilpotencyLength 𝔞 (AdoSpace K 𝔞) ≤ nilpotencyLength 𝔞 (AdoSpace K 𝔞) + 1)]
  apply ι_mul_mem_lengthSubmodule_succ_of_mem
  exact ha

lemma bracket_mem_nilSubmodule_of_mem (x : 𝔞) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    ⁅x, a⁆ ∈ nilSubmodule K 𝔞 := by
  rw [bracket_eq]
  exact ι_mul_mem_nilSubmodule_of_mem x a ha

@[simp]
lemma leftLieUE_mem_nilSubmodule_of_mem (x : 𝔥) (a) (ha : a ∈ nilSubmodule K 𝔞) :
    leftLieUE ψ x a ∈ nilSubmodule K 𝔞 := by
  revert a
  suffices h :
      Submodule.map (leftLieUE ψ x) (nilSubmodule K 𝔞) ≤ nilSubmodule K 𝔞 by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage]
  rintro _ ⟨n, f, hn, rfl⟩
  conv => equals ∑ i : Fin n,
      mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n (update f i (ψ x (f i)))) ∈ nilSubmodule K 𝔞 =>
    simp [leftLieUE_mkAlgHom, - TensorAlgebra.tprod_apply]
  apply Submodule.sum_mem
  rintro i -
  exact mkAlgHom_tprod_mem_nilSubmodule _ hn

end NilSubmodule

section DepthSubmodule

def depthSubmodule (m : ℕ) : Submodule K (UniversalEnvelopingAlgebra K 𝔞) :=
  .span K {a | ∃ᵉ (n) (f : Fin n → 𝔞) (x : Fin n → ℕ),
      ∑ k, x k = m ∧
      (∀ k, (f k) ∈ (lowerCentralSeries K (inr ψ).range (inl ψ).idealRange (x k)).toSubmodule.comap
          (equivIdealRangeInl ψ).toLinearMap) ∧
        a = mkAlgHom K 𝔞 (TensorAlgebra.tprod K 𝔞 n f)}

@[simp]
lemma depththSubmodule_zero : depthSubmodule ψ 0 = ⊤ := by
  simp_rw [eq_top_iff, ← lengthSubmodule_zero, lengthSubmodule_eq_span_exists_eq_mkAlgHom_tprod,
    zero_le, true_and, Submodule.span_le, ofPred_subset, SetLike.mem_coe]
  rintro _ ⟨n, f, rfl⟩
  unfold depthSubmodule
  apply Submodule.mem_span_of_mem
  rw [mem_ofPred]
  existsi n, f, 0
  simp

@[gcongr]
lemma depthSubmodule_mono ⦃m n⦄ (h : m ≤ n) : depthSubmodule ψ n ≤ depthSubmodule ψ m := by
  simp_rw [depthSubmodule]
  gcongr 4 with _ n f
  rintro ⟨x, rfl, hf, rfl⟩
  rsuffices ⟨x', hx', rfl⟩ : ∃ x' : Fin n → ℕ, x' ≤ x ∧ ∑ k, x' k = m
  · existsi x'
    refine ⟨rfl, ?_, rfl⟩
    intro k
    grw [hx' k]
    exact hf k
  induction h using Nat.decreasingInduction with
  | self => exists x
  | of_succ k h hi =>
    obtain ⟨x', hx', hi⟩ := hi
    have hx'₂ : 0 < ∑ k, x' k := by lia
    simp_rw [Finset.sum_pos_iff, Finset.mem_univ, true_and] at hx'₂
    obtain ⟨j, hj⟩ := hx'₂
    existsi x' - Pi.single j 1
    constructor
    · grw [tsub_le_self, hx']
    · have hx'₂ : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          Pi.single (M := fun _ ↦ ℕ) j 1 i ≤ x' i
      · rintro i -
        obtain (rfl | hj) := eq_or_ne i j
        · simp [hj, Nat.succ_le_iff]
        · simp [hj]
      simp_rw [Pi.sub_apply, Finset.sum_tsub_distrib _ hx'₂]
      simp [hi]

lemma leftLieUE_mem_depthSubmodule_succ_of_mem (m) (x : 𝔥) (a) (ha : a ∈ depthSubmodule ψ m) :
    leftLieUE ψ x a ∈ depthSubmodule ψ (m + 1) := by
  revert a
  suffices h :
      Submodule.map (leftLieUE ψ x) (depthSubmodule ψ m) ≤ depthSubmodule ψ (m + 1) by
    rw [Submodule.map_le_iff_le_comap] at h
    simpa [IsConcreteLE.le_iff] using h
  conv_lhs => rw [depthSubmodule, Submodule.map_span]
  simp_rw [Submodule.span_le, image_subset_iff, ofPred_subset, Set.mem_preimage]
  rintro _ ⟨n, f, y, hy, hf, rfl⟩
  simp_rw [leftLieUE_mkAlgHom, leftLieUEAux_tprod, map_sum, SetLike.mem_coe]
  apply sum_mem; rintro k -
  simp_rw [depthSubmodule]; apply Submodule.mem_span_of_mem; simp_rw [mem_ofPred_eq]
  existsi n, update f k (ψ x (f k)), y + Pi.single k 1
  split_ands
  on_goal 3 => rfl
  · simp [Finset.sum_add_distrib, hy]
  · intro j
    obtain (rfl | hj) := eq_or_ne j k
    · specialize hf j
      conv at hf => equals
        equivIdealRangeInl ψ (f j) ∈ lowerCentralSeries K (inr ψ).range (inl ψ).idealRange (y j) =>
          simp
      replace hf := lie_mem_lie (by simp : ⟨inr ψ x, by simp⟩ ∈ (⊤ : LieIdeal K (inr ψ).range)) hf
      conv at hf => enter [2]; equals equivIdealRangeInl ψ (ψ x (f j)) => ext : 1; simp
      simpa using hf
    · simp [hj, hf]

variable [IsAdo K 𝔞]

noncomputable def depthLimit : ℕ :=
  Nat.pred (nilpotencyLength 𝔞 (AdoSpace K 𝔞)) *
    Nat.pred (nilpotencyLength (inr ψ).range (inl ψ).idealRange) + 1

variable {ψ} in
lemma exists_nilpotencyLength_le_of_depthLimit_le_sum {n} [NeZero n] (x : Fin n → ℕ)
    (hn : n < nilpotencyLength 𝔞 (AdoSpace K 𝔞)) (hx : depthLimit ψ ≤ ∑ i, x i) :
    ∃ i, nilpotencyLength (inr ψ).range (inl ψ).idealRange ≤ x i := by
  apply Nat.le_pred_of_lt at hn
  grw [depthLimit, Nat.succ_le_iff, ← hn] at hx
  conv_lhs at hx =>
    equals ∑ _ : Fin n, Nat.pred (nilpotencyLength (inr ψ).range (inl ψ).idealRange) => simp
  apply Finset.exists_lt_of_sum_lt at hx
  simp_rw [Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi⟩ := hx
  apply Nat.le_of_pred_lt at hi
  exists i

lemma depthSubmodule_depthLimit_le_nilSubmodule [LieRing.IsNilpotent (𝔞 ⋊⁅ψ⁆ 𝔥)] :
    depthSubmodule ψ (depthLimit ψ) ≤ nilSubmodule K 𝔞 := by
  simp_rw [depthSubmodule, Submodule.span_le, ofPred_subset, SetLike.mem_coe]
  rintro _ ⟨n, f, x, hx, hf, rfl⟩
  obtain (rfl | hn) := eq_or_ne n 0
  case inl => simp [depthLimit] at hx
  obtain (hn₂ | hn₂) := lt_or_ge n (nilpotencyLength 𝔞 (AdoSpace K 𝔞))
  case inr => apply mkAlgHom_tprod_mem_nilSubmodule _ hn₂
  apply NeZero.mk at hn
  replace hx := exists_nilpotencyLength_le_of_depthLimit_le_sum x hn₂ hx.ge
  obtain ⟨i, hi⟩ := hx
  specialize hf i
  grw [← hi, lowerCentralSeries_nilpotencyLength] at hf
  conv at hf => equals f i = 0 => simp
  simp [(TensorAlgebra.tprod K 𝔞 n).map_coord_zero i hf, - TensorAlgebra.tprod_apply]

end DepthSubmodule

variable [IsAdo K 𝔞]

instance [FiniteDimensional K 𝔞] :
    FiniteDimensional K (UniversalEnvelopingAlgebra K 𝔞 ⧸ nilSubmodule K 𝔞) := by
  -- `Submodule` を後で `open` した方がいいかな
  suffices h : Submodule.map (nilSubmodule K 𝔞).mkQ
      (Submodule.map (mkAlgHom K 𝔞).toLinearMap
        (⨆ k < nilpotencyLength 𝔞 (AdoSpace K 𝔞),
          LinearMap.range (TensorPower.toTensorAlgebra (n := k)))) = ⊤ by
    simp_rw [Module.finite_def, ← h]
    apply Submodule.FG.map
    apply Submodule.FG.map
    simp_rw [← Finset.mem_Iio]
    apply Submodule.fg_biSup
    rintro n -
    apply Submodule.fg_range
  suffices h : Submodule.map (nilSubmodule K 𝔞).mkQ
      (Submodule.map (mkAlgHom K 𝔞).toLinearMap
        (⨆ k ≥ nilpotencyLength 𝔞 (AdoSpace K 𝔞),
          LinearMap.range (TensorPower.toTensorAlgebra (n := k)))) = ⊥ by
    have hι := DirectSum.Decomposition.isInternal
        (fun n : ℕ ↦ LinearMap.range (TensorAlgebra.ι K : 𝔞 →ₗ[K] TensorAlgebra K 𝔞) ^ n)
    simp_rw [TensorAlgebra.ι_range_pow_eq] at hι
    apply DirectSum.IsInternal.submodule_iSup_eq_top at hι
    simp_rw +singlePass [iSup_split _ (· < nilpotencyLength 𝔞 (AdoSpace K 𝔞)), not_lt] at hι
    apply_fun Submodule.map (mkAlgHom K 𝔞).toLinearMap at hι
    apply_fun Submodule.map (nilSubmodule K 𝔞).mkQ at hι
    simp_rw [Submodule.map_sup, h, sup_bot_eq, Submodule.map_top,
      (mkAlgHom K 𝔞).toLinearMap.range_eq_top_of_surjective (mkAlgHom_surjective _ _),
      Submodule.map_top, Submodule.range_mkQ] at hι
    exact hι
  simp_rw [← lengthSubmodule.eq_1, lengthSubmodule_nilpotenctLength,
    nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.map_span, Submodule.span_eq_bot,
    forall_mem_image, mem_ofPred]
  rintro _ ⟨n, f, hn, rfl⟩
  simp_rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mkAlgHom_tprod_mem_nilSubmodule f hn]

lemma nilSubmodule_le_ker_lift_toEnd_adoSpace [LieRing.IsNilpotent 𝔞] :
    nilSubmodule K 𝔞 ≤ LinearMap.ker (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))).toLinearMap := by
  simp_rw [nilSubmodule_eq_span_exists_eq_mkAlgHom_tprod, Submodule.span_le, ofPred_subset,
    SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rintro _ ⟨n, f, hn, rfl⟩
  simp_rw [nilpotencyLength_le_iff K, SetLike.ext_iff, LieSubmodule.mem_bot] at hn
  simp_rw [DFunLike.ext_iff, LinearMap.zero_apply, ← hn]
  intro x
  conv =>
    enter [2, 1, 2, 2]
    equals List.prod (List.map (ι K) (List.ofFn f)) => simp [comp_def]
  simp_rw [map_list_prod, List.map_map, comp_def, lift_ι_apply']
  convert list_prod_map_toEnd_apply_mem_lowerCentralSeries K (List.ofFn f) x
  simp

lemma injective_quotient_mk_nilSubmodule [LieRing.IsNilpotent 𝔞] :
    Injective (fun x ↦
      (Submodule.Quotient.mk (.ι K x) : UniversalEnvelopingAlgebra K 𝔞 ⧸ nilSubmodule K 𝔞)) := by
  apply Function.Injective.of_comp
      (f := (nilSubmodule K 𝔞).liftQ (lift K (toEnd K 𝔞 (AdoSpace K 𝔞))).toLinearMap
        nilSubmodule_le_ker_lift_toEnd_adoSpace)
  simpa [comp_def] using IsFaithful.injective_toEnd

end LieAlgebra.SemiDirectSum

/-

def PreNilStepAdoSpace (D : NilStepAdoData K 𝔫) :=
  UniversalEnvelopingAlgebra K 𝔞
deriving Ring, Algebra K

open UniversalEnvelopingAlgebra (ι)

namespace PreNilStepAdoSpace

variable {D : NilStepAdoData K 𝔫}

def equiv : UniversalEnvelopingAlgebra K 𝔞 ≃ₐ[K] PreNilStepAdoSpace D :=
  AlgEquiv.refl (R := K) (A₁ := UniversalEnvelopingAlgebra K 𝔞)

@[ext]
lemma ext {p q : PreNilStepAdoSpace D} (h : equiv.symm p = equiv.symm q) : p = q := by
  simpa using h

@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {motive : PreNilStepAdoSpace D → Sort*} :
    (equiv : Π a, motive (equiv a)) → Π a, motive a :=
  fun equiv' a ↦ equiv' (equiv.symm a)

noncomputable instance : Bracket 𝔫 (PreNilStepAdoSpace D) where
  bracket x := LinearEquiv.conj equiv.toLinearEquiv
    (LinearMap.ofIsCompl D.isCompl_toSubmodule
      (toEnd K 𝔞 (UniversalEnvelopingAlgebra K 𝔞))
        (toEnd K 𝔥 (UniversalEnvelopingAlgebra K 𝔞)) x)

lemma bracket_def (x : 𝔫) (a : PreNilStepAdoSpace D) :
    ⁅x, a⁆ = LinearEquiv.conj equiv.toLinearEquiv
      (LinearMap.ofIsCompl D.isCompl_toSubmodule
        (toEnd K 𝔞 (UniversalEnvelopingAlgebra K 𝔞))
          (toEnd K 𝔥 (UniversalEnvelopingAlgebra K 𝔞)) x) a :=
  rfl

-- encapsulate the type defeq hell in this lemma
@[simp]
lemma bracket_𝔞 (x : 𝔞) (a : PreNilStepAdoSpace D) : ⁅(x : 𝔫), a⁆ = equiv ⁅x, equiv.symm a⁆ := by
  simp only [bracket_def, LinearMap.ofIsCompl_apply_left, coe_toLinearMap,
    LinearEquiv.conj_apply_apply, bracket_eq, ι_apply]
  rfl

-- encapsulate the type defeq hell in this lemma
@[simp]
lemma bracket_𝔥 (x : 𝔥) (a : PreNilStepAdoSpace D) : ⁅(x : 𝔫), a⁆ = equiv ⁅x, equiv.symm a⁆ := by
  simp only [bracket_def, LinearMap.ofIsCompl_apply_right, coe_toLinearMap,
    LinearEquiv.conj_apply_apply]
  rfl

protected lemma add_lie (x y : 𝔫) (a : PreNilStepAdoSpace D) : ⁅x + y, a⁆ = ⁅x, a⁆ + ⁅y, a⁆ := by
  simp [bracket_def]

protected lemma smul_lie (t : K) (x : 𝔫) (a : PreNilStepAdoSpace D) : ⁅t • x, a⁆ = t • ⁅x, a⁆ := by
  simp [bracket_def]

protected lemma neg_lie (x : 𝔫) (a : PreNilStepAdoSpace D) : ⁅-x, a⁆ = -⁅x, a⁆ := by
  simpa using smul_lie (-1 : K) x a

noncomputable instance : LieRingModule 𝔫 (PreNilStepAdoSpace D) where
  add_lie := PreNilStepAdoSpace.add_lie
  lie_add x a b := by simp [bracket_def]
  leibniz_lie x y a := by
    conv => equals ⁅⁅x, y⁆, a⁆ = ⁅x, ⁅y, a⁆⁆ - ⁅y, ⁅x, a⁆⁆ => grind only
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := D.existsUnique_add_prod x |>.exists
    obtain ⟨⟨y₁, y₂⟩, rfl⟩ := D.existsUnique_add_prod y |>.exists
    cases a with | equiv a
    conv => equals
        ⁅⁅(x₁ : 𝔫), (y₁ : 𝔫)⁆, equiv a⁆ + ⁅⁅(x₂ : 𝔫), (y₁ : 𝔫)⁆, equiv a⁆ +
          ⁅⁅(x₁ : 𝔫), (y₂ : 𝔫)⁆, equiv a⁆ + ⁅⁅(x₂ : 𝔫), (y₂ : 𝔫)⁆, equiv a⁆ =
          equiv ⁅x₁, ⁅y₁, a⁆⁆ + equiv ⁅x₁, ⁅y₂, a⁆⁆ + equiv ⁅x₂, ⁅y₁, a⁆⁆ + equiv ⁅x₂, ⁅y₂, a⁆⁆ -
          (equiv ⁅y₁, ⁅x₁, a⁆⁆ + equiv ⁅y₁, ⁅x₂, a⁆⁆ + equiv ⁅y₂, ⁅x₁, a⁆⁆ + equiv ⁅y₂, ⁅x₂, a⁆⁆) =>
      simp [PreNilStepAdoSpace.add_lie, - ι_apply, - bracket_eq, ← add_assoc]
    conv_lhs =>
      conv =>
        enter [1, 1, 1]
        equals equiv ⁅x₁, ⁅y₁, a⁆⁆ - equiv ⁅y₁, ⁅x₁, a⁆⁆ =>
          simp_rw [← LieIdeal.coe_bracket, bracket_𝔞, lie_lie]; simp
      conv =>
        enter [2]
        equals equiv ⁅x₂, ⁅y₂, a⁆⁆ - equiv ⁅y₂, ⁅x₂, a⁆⁆ =>
          simp_rw [← LieSubalgebra.coe_bracket, bracket_𝔥, lie_lie]; simp
    conv => equals
        ⁅⁅(x₂ : 𝔫), (y₁ : 𝔫)⁆, equiv a⁆ + ⁅⁅(x₁ : 𝔫), (y₂ : 𝔫)⁆, equiv a⁆ =
          equiv ⁅x₁, ⁅y₂, a⁆⁆ + equiv ⁅x₂, ⁅y₁, a⁆⁆ - (equiv ⁅y₁, ⁅x₂, a⁆⁆ + equiv ⁅y₂, ⁅x₁, a⁆⁆) =>
      grind only
    conv_lhs =>
      conv =>
        enter [1]
        rw [← LieSubmodule.coe_bracket, bracket_𝔞, AlgEquiv.symm_apply_apply, bracket_eq]
      conv =>
        enter [2]
        rw [← lie_skew, PreNilStepAdoSpace.neg_lie, ← LieSubmodule.coe_bracket, bracket_𝔞,
          AlgEquiv.symm_apply_apply, bracket_eq]
    conv_rhs =>
      simp only [bracket_eq]
      conv =>
        enter [1, 2]
        rw [D.bracket_𝔥_mul, map_add, D.bracket_𝔥_ι, LieSubalgebra.coe_bracket_of_module]
      conv =>
        enter [2, 2]
        rw [D.bracket_𝔥_mul, map_add, D.bracket_𝔥_ι, LieSubalgebra.coe_bracket_of_module]
    noncomm_ring

instance : LieModule K 𝔫 (PreNilStepAdoSpace D) where
  smul_lie := PreNilStepAdoSpace.smul_lie
  lie_smul t x a := by simp [bracket_def]

end PreNilStepAdoSpace

open PreNilStepAdoSpace

namespace NilStepAdoData

variable (D : NilStepAdoData K 𝔫)

@[simps toSubmodule]
noncomputable def nilLieSubmodule : LieSubmodule K 𝔫 (PreNilStepAdoSpace D) where
  toSubmodule := Submodule.map equiv.toLinearMap nilSubmodule K 𝔞
  lie_mem {x a} ha := by
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := D.existsUnique_add_prod x |>.exists
    cases a with | equiv a
    conv at ha => equals a ∈ nilSubmodule K 𝔞 => simp
    conv => equals ι K x₁ * a + ⁅x₂, a⁆ ∈ nilSubmodule K 𝔞 =>
      rw [Submodule.mem_carrier, SetLike.mem_coe]; simp
    simp [- ι_apply, add_mem, ha]

end NilStepAdoData

abbrev NilStepAdoSpace (D : NilStepAdoData K 𝔫) :=
  PreNilStepAdoSpace D ⧸ D.nilLieSubmodule

namespace NilStepAdoSpace

attribute [local instance 100] LieRing.ofAssociativeRing

variable (D : NilStepAdoData K 𝔫)

@[simp]
lemma quotient_equiv_mk (a : UniversalEnvelopingAlgebra K 𝔞) :
    Submodule.Quotient.equiv nilSubmodule K 𝔞 D.nilLieSubmodule.toSubmodule
      PreNilStepAdoSpace.equiv.toLinearEquiv rfl (Submodule.Quotient.mk a) =
        (LieSubmodule.Quotient.mk (equiv a)) :=
  rfl

instance : FiniteDimensional K (NilStepAdoSpace D) :=
  LinearEquiv.finiteDimensional <|
    Submodule.Quotient.equiv nilSubmodule K 𝔞 D.nilLieSubmodule.toSubmodule
      PreNilStepAdoSpace.equiv.toLinearEquiv rfl

instance : IsFaithful K (center K 𝔫) (NilStepAdoSpace D) := by
  suffices h : IsFaithful K 𝔞 (NilStepAdoSpace D) by
    rw [isFaithful_iff] at h ⊢
    replace h := h.comp (LieSubmodule.inclusion_injective D.center_le_𝔞)
    convert h using 1
    ext x a
    simp
  suffices h :
      Injective (fun x ↦ (LieSubmodule.Quotient.mk (equiv (ι K x)) : NilStepAdoSpace D)) by
    rw [isFaithful_iff']
    intro x hx
    specialize hx (LieSubmodule.Quotient.mk 1)
    simp_rw [coe_bracket_of_module, Quotient.lie_bracket_mk, bracket_𝔞, map_one, bracket_eq,
      mul_one] at hx
    conv_rhs at hx => equals LieSubmodule.Quotient.mk (equiv (ι K 0)) => simp
    apply h at hx
    exact hx
  have h := D.injective_quotient_mk_nilSubmodule
  apply (Submodule.Quotient.equiv nilSubmodule K 𝔞 D.nilLieSubmodule.toSubmodule
    PreNilStepAdoSpace.equiv.toLinearEquiv rfl).injective.comp at h
  simp_rw [comp_def, quotient_equiv_mk] at h
  exact h

local instance : IsNilpotent 𝔞 (NilStepAdoSpace D) := by
  suffices h : ∀ k,
      (𝔞.lcs (PreNilStepAdoSpace D) k).toSubmodule ≤
        Submodule.map equiv.toLinearMap (lengthSubmodule K 𝔞 k) by
    change IsNilpotent 𝔞.toLieSubalgebra (PreNilStepAdoSpace D ⧸ D.nilLieSubmodule.restr 𝔞)
    simp_rw [isNilpotent_quotient_iff, ← toSubmodule_le_toSubmodule]
    conv => enter [1, k, 1, 1]; change lowerCentralSeries K 𝔞 (PreNilStepAdoSpace D) k
    simp_rw [← coe_lcs_eq, restr_toSubmodule, toSubmodule_le_toSubmodule]
    existsi nilpotencyLength 𝔞 (AdoSpace K 𝔞)
    specialize h (nilpotencyLength 𝔞 (AdoSpace K 𝔞))
    simp_rw [lengthSubmodule K 𝔞_nilpotenctLength, ← D.nilLieSubmodule_toSubmodule,
      toSubmodule_le_toSubmodule] at h
    exact h
  intro k
  induction k with
  | zero => simp
  | succ n hn =>
    simp_rw [LieIdeal.lcs_succ, lieIdeal_oper_eq_linear_span', ← exists_prop (a := _ ∈ 𝔞),
      Subtype.exists', Submodule.span_le, ofPred_subset, SetLike.mem_coe, Submodule.mem_map_equiv]
    rintro _ ⟨x, a, ha, rfl⟩
    cases a with | equiv a
    conv => equals ⁅x, a⁆ ∈ lengthSubmodule K 𝔞 (n + 1) => simp
    simp_rw [IsConcreteLE.le_iff, mem_toSubmodule, Submodule.mem_map_equiv,
      AlgEquiv.coe_symm_toLinearEquiv] at hn
    specialize hn ha
    rw [AlgEquiv.symm_apply_apply] at hn
    exact D.bracket_𝔞_mem_lengthSubmodule_succ_of_mem n x a hn

local instance isNilpotent𝔥 : IsNilpotent 𝔥 (NilStepAdoSpace D) := by
  suffices h : ∀ k,
      (lowerCentralSeries K 𝔥 (PreNilStepAdoSpace D) k).toSubmodule ≤
        Submodule.map equiv.toLinearMap (depthSubmodule ψ k) by
    change IsNilpotent 𝔥 (PreNilStepAdoSpace D ⧸ D.nilLieSubmodule.restr 𝔥)
    simp_rw [isNilpotent_quotient_iff, ← toSubmodule_le_toSubmodule, restr_toSubmodule]
    existsi D.depthLimit
    specialize h D.depthLimit
    grw [depthSubmodule ψ_depthLimit_le_nilSubmodule, ← D.nilLieSubmodule_toSubmodule] at h
    exact h
  intro k
  induction k with
  | zero => simp
  | succ n hn =>
    simp_rw [lowerCentralSeries_succ, lieIdeal_oper_eq_linear_span', ← exists_prop (a := _ ∈ ⊤),
      Subtype.exists', Submodule.span_le, ofPred_subset, SetLike.mem_coe, Submodule.mem_map_equiv]
    rintro _ ⟨x, a, ha, rfl⟩
    cases a with | equiv a
    conv => equals ⁅x, a⁆ ∈ depthSubmodule ψ (n + 1) => simp
    simp_rw [IsConcreteLE.le_iff, mem_toSubmodule, Submodule.mem_map_equiv,
      AlgEquiv.coe_symm_toLinearEquiv] at hn
    specialize hn ha
    rw [AlgEquiv.symm_apply_apply] at hn
    exact D.leftLieUE_mem_depthSubmodule_succ_of_mem n x a hn

instance : IsNilpotent 𝔫 (NilStepAdoSpace D) := by
  conv => equals IsNilpotent ↥(𝔥 ⊔ 𝔞.toLieSubalgebra) (NilStepAdoSpace D) =>
    have h : 𝔥 ⊔ 𝔞.toLieSubalgebra = ⊤
    · simp [← LieSubalgebra.toSubmodule_inj, sup_comm 𝔥.toSubmodule 𝔞.toSubmodule,
        D.isCompl_toSubmodule.codisjoint.eq_top]
    simp [h]
  infer_instance

end NilStepAdoSpace

lemma NilStepAdoData.isAdo (D : NilStepAdoData K 𝔫) : IsAdo K 𝔫 :=
  .of_isNilpotent_of_isFaithful_center (NilStepAdoSpace D)

public instance LieAlgebra.IsAdo.of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing 𝔫 with
  | zero => rw [finrank_zero_iff] at hn; exact .intro Unit
  | succ n hin =>
    by_cases h𝔫 : IsLieAbelian 𝔫
    case pos => exact .of_isLieAbelian
    rsuffices ⟨D⟩ : Nonempty (NilStepAdoData K 𝔫)
    · exact D.isAdo
    obtain ⟨𝔞, rfl, h𝔞⟩ := exists_for_nilStepAdoData_of_not_isLieAbelian K 𝔫 n hn h𝔫
    specialize hin rfl
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔫, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      rw [← Submodule.finrank_add_eq_of_isCompl h𝔥', finrank_toSubmodule,
        Nat.add_left_cancel_iff] at hn
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨{ 𝔞, 𝔥, center_le_𝔞 := h𝔞, isCompl_toSubmodule := h𝔥₁ }⟩

-/

@[instance]
public axiom LieAlgebra.IsAdo.of_isNilpotent : IsAdo K 𝔫
