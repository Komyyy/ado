/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib
public import Ado.ForMathlib.LieModulePUnit
public import Ado.ForMathlib.LieModuleSubsingleton
public import Ado.ForMathlib.LieModuleKer
public import Ado.ForMathlib.LieFinrank
public import Ado.ForMathlib.LieQuotient
public import Ado.ForMathlib.LieHom
public import Ado.ForMathlib.DirectSum
public import Ado.ForMathlib.FinAdd
public import Ado.ForMathlib.TensorAlgebra
public import Ado.ForMathlib.LieIdealCoe
public import Ado.LieAbelian
public import Ado.UniversalEnvelopingAlgebraTrick

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set Finset Module LieAlgebra LieModule LieSubmodule LieIdeal LieHom
open TensorAlgebra hiding ringCon ι
open UniversalEnvelopingAlgebra hiding ι

variable {K 𝔫 : Type*}
variable [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

@[simps toSubmodule]
def Submodule.toLieSubalgebraOfDimOne (𝔥 : Submodule K 𝔫) (h𝔥 : finrank K 𝔥 = 1) :
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
    ← Nat.sub_pos_iff_lt, ← finrank_quotient, finrank_pos_iff] at h𝔫a
  have h𝔫' := derivedSeries_lt_top_of_solvable K (𝔫 ⧸ center K 𝔫)
  simp_rw +singlePass [← finrank_lt_iff, ← Nat.sub_pos_iff_lt, ← finrank_quotient] at h𝔫'
  exact h𝔫'

structure NilStepAdoData (K 𝔫 : Type*)
    [Field K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫] [LieRing.IsNilpotent 𝔫] where
  protected 𝔞 : LieIdeal K 𝔫
  protected 𝔥 : LieSubalgebra K 𝔫
  center_le_𝔞 : center K 𝔫 ≤ 𝔞
  finrank_𝔥 : finrank K 𝔥 = 1
  isCompl_toSubmodule : IsCompl 𝔞.toSubmodule 𝔥.toSubmodule
  [instIsAdo𝔞 : IsAdo K 𝔞]

attribute [instance] NilStepAdoData.instIsAdo𝔞

namespace NilStepAdoData

open TensorAlgebra (ι)

variable (D : NilStepAdoData K 𝔫)

attribute [local instance 100] LieRing.ofAssociativeRing

def bracketAux (x : D.𝔥) : End K (TensorAlgebra K D.𝔞) :=
  LinearEquiv.conj TensorAlgebra.equivDirectSum.toLinearEquiv.symm
    (DirectSum.lmap (fun n ↦
      ∑ i : Fin n, PiTensorProduct.map (update (fun _ ↦ LinearMap.id) i (toEnd K D.𝔥 D.𝔞 x))))

@[simp]
lemma bracketAux_ι (x : D.𝔥) (y : D.𝔞) : D.bracketAux x (ι K y) = ι K ⁅x, y⁆ := by
  simp [bracketAux]

@[simp]
lemma bracketAux_tprod (x : D.𝔥) {n} (f : Fin n → D.𝔞) :
    D.bracketAux x (TensorAlgebra.tprod K D.𝔞 n f) =
      ∑ i : Fin n, TensorAlgebra.tprod K D.𝔞 n (update f i ⁅x, f i⁆) := by
  simp [bracketAux, - TensorAlgebra.tprod_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
    apply_update (f := fun (i : Fin n) (F : D.𝔞 →ₗ[K] D.𝔞) ↦ F (f i))]

lemma bracketAux_bracketAux_tprod (x y : D.𝔥) {n} (f : Fin n → D.𝔞) :
    D.bracketAux x (D.bracketAux y (TensorAlgebra.tprod K D.𝔞 n f)) =
      (∑ i : Fin n, TensorAlgebra.tprod K D.𝔞 n (update f i ⁅x, ⁅y, f i⁆⁆)) +
        (∑ p ∈ offDiag (univ : Finset (Fin n)),
          TensorAlgebra.tprod K D.𝔞 n (update (update f p.1 ⁅y, f p.1⁆) p.2 ⁅x, f p.2⁆)) :=
  calc _
    _ = ∑ i : Fin n, D.bracketAux x (TensorAlgebra.tprod K D.𝔞 n (update f i ⁅y, f i⁆)) := by
      conv_lhs => rw [bracketAux_tprod, map_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        TensorAlgebra.tprod K D.𝔞 n
          (update (update f i ⁅y, f i⁆) j (⁅x, update f i ⁅y, f i⁆ j⁆)) := by
      simp only [bracketAux_tprod]
    _ = (∑ i : Fin n, TensorAlgebra.tprod K D.𝔞 n (update f i ⁅x, ⁅y, f i⁆⁆)) +
          (∑ i : Fin n, ∑ j ∈ ({i}ᶜ : Finset (Fin n)),
            TensorAlgebra.tprod K D.𝔞 n (update (update f i ⁅y, f i⁆) j (⁅x, f j⁆))) := by
      conv_lhs =>
        conv => enter [2, i]; rw [Fintype.sum_eq_add_sum_compl i]
        rw [sum_add_distrib]
      congr! 3 with i _ i _ j hj <;> [simp; (congr! 3; apply update_of_ne; simpa using hj)]
    _ = _ := by
      congr! 1
      symm
      apply sum_finset_product
      simp [not_iff_not, iff_true_intro eq_comm]

lemma bracketAux_lie_left (x y : D.𝔥) (a) : D.bracketAux ⁅x, y⁆ a =
    D.bracketAux x (D.bracketAux y a) - D.bracketAux y (D.bracketAux x a) := by
  revert a
  suffices h : D.bracketAux ⁅x, y⁆ =
      D.bracketAux x * D.bracketAux y - D.bracketAux y * D.bracketAux x by
    simpa [DFunLike.ext_iff] using h
  ext n f
  conv_lhs => tactic =>
    simp_rw [bracketAux_tprod, lie_lie, MultilinearMap.map_update_sub, sum_sub_distrib]
  conv_rhs =>
    simp only [LinearMap.sub_apply, End.mul_apply, bracketAux_bracketAux_tprod]
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

lemma bracketAux_add_left (x y : D.𝔥) (a) :
    D.bracketAux (x + y) a = D.bracketAux x a + D.bracketAux y a := by
  simp [bracketAux, PiTensorProduct.map_update_add, Finset.sum_add_distrib]

lemma bracketAux_smul_left (t : K) (x : D.𝔥) (a) :
    D.bracketAux (t • x) a = t • D.bracketAux x a := by
  simp [bracketAux, PiTensorProduct.map_update_smul, ← Finset.smul_sum]

lemma bracketAux_mul (x : D.𝔥) (a b) : D.bracketAux x (a * b) =
    a * D.bracketAux x b + D.bracketAux x a * b := by
  revert a b
  suffices h :
      (LinearMap.mul K (TensorAlgebra K D.𝔞)).compr₂ (D.bracketAux x) =
        (LinearMap.mul K (TensorAlgebra K D.𝔞)).compl₁₂ LinearMap.id (D.bracketAux x) +
          (LinearMap.mul K (TensorAlgebra K D.𝔞)).compl₁₂ (D.bracketAux x) LinearMap.id by
    simpa [DFunLike.ext_iff] using h
  conv_rhs => apply add_comm
  ext m y n z
  simp [Fin.sum_univ_add, - LieSubalgebra.coe_bracket_of_module, - TensorAlgebra.tprod_apply]

lemma mkAlgHom_bracketAux_eq_of_ringCon (x : D.𝔥) (a b) (h : ringCon K D.𝔞 a b) :
    mkAlgHom K D.𝔞 (D.bracketAux x a) = mkAlgHom K D.𝔞 (D.bracketAux x b) := by
  induction h using ringCon_induction with
  | refl | symm | trans | add => grind only [= map_add]
  | mul a b c d h₁ h₂ hi₁ hi₂ =>
    rw [← mkAlgHom_eq_mkAlgHom] at h₁ h₂; simp [bracketAux_mul, *]
  | lie_compat a b =>
    simp_rw [map_add, ← eq_sub_iff_add_eq]
    conv_rhs => simp only [bracketAux_mul, map_add, map_mul, bracketAux_ι, ← ι_apply]
    conv_lhs =>
      rw [bracketAux_ι, ← ι_apply, D.𝔥.coe_bracket_of_module, leibniz_lie,
        ← D.𝔥.coe_bracket_of_module, ← D.𝔥.coe_bracket_of_module, map_add, map_lie, map_lie,
        LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket]
    noncomm_ring

lemma ringCon_bracketAux_of_ringCon (x : D.𝔥) (a b) (h : ringCon K D.𝔞 a b) :
    ringCon K D.𝔞 (D.bracketAux x a) (D.bracketAux x b) :=
  mkAlgHom_eq_mkAlgHom.mp (D.mkAlgHom_bracketAux_eq_of_ringCon x a b h)

instance : Bracket D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞) where
  bracket x := tensorLift (mkAlgHom K D.𝔞 ∘ D.bracketAux x) (D.mkAlgHom_bracketAux_eq_of_ringCon x)

lemma bracket_𝔥_def (x : D.𝔥) (a : UniversalEnvelopingAlgebra K D.𝔞) :
    ⁅x, a⁆ =
      tensorLift (mkAlgHom K D.𝔞 ∘ D.bracketAux x) (D.mkAlgHom_bracketAux_eq_of_ringCon x) a :=
  rfl

lemma bracket_𝔥_mkAlgHom (x : D.𝔥) (a : TensorAlgebra K D.𝔞) :
    ⁅x, mkAlgHom K D.𝔞 a⁆ = mkAlgHom K D.𝔞 (D.bracketAux x a) := by
  simp [bracket_𝔥_def]

instance : LieRingModule D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞) where
  add_lie x y a := by
    cases a with | mkAlgHom a; simp [bracket_𝔥_mkAlgHom, bracketAux_add_left]
  lie_add x a b := by
    cases a with | mkAlgHom a
    cases b with | mkAlgHom b
    simp_rw [← map_add, bracket_𝔥_mkAlgHom, map_add]
  leibniz_lie x y a := by
    cases a with | mkAlgHom a; simp [bracket_𝔥_mkAlgHom, bracketAux_lie_left]

instance : LieModule K D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞) where
  smul_lie t x a := by
    cases a with | mkAlgHom a; simp [bracket_𝔥_mkAlgHom, bracketAux_smul_left]
  lie_smul t x a := by
    cases a with | mkAlgHom a
    simp_rw [← map_smul, bracket_𝔥_mkAlgHom, map_smul]

@[simp]
lemma bracket_𝔥_mul (x : D.𝔥) (a b : UniversalEnvelopingAlgebra K D.𝔞) :
    ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b := by
  cases a with | mkAlgHom a
  cases b with | mkAlgHom b
  simp_rw [← map_mul, bracket_𝔥_mkAlgHom, bracketAux_mul]
  simp

@[simp]
lemma bracket_𝔥_ι (x : D.𝔥) (y : D.𝔞) :
    ⁅x, UniversalEnvelopingAlgebra.ι K y⁆ = UniversalEnvelopingAlgebra.ι K ⁅x, y⁆ := by
  simp [bracket_𝔥_mkAlgHom]

/-!
## `reducible` レベル下での型の不一致への対応策

```lean4
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

example (s : LieIdeal R L) : ↥s = ↥s.toSubmodule := by
  fail_if_success with_reducible rfl
  with_reducible_and_instances rfl
```

本来これは `reducible` 下で defeq となって欲しいが、`↥s := { x // x ∈ s }` と定義されており、
`Membership` インスタンスが `reducible` 下で defeq にならず、構造体の射影に本来ある `reducible` 下での
defeq が享受できていない。このため、インスタンス合成が絡む箇所で問題を起こしている。修正されるまで、以下の
補助補題を用いる。
-/

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] in
example (s : LieIdeal R L) : ↥s = ↥s.toSubmodule := by
  fail_if_success with_reducible rfl
  with_reducible_and_instances rfl

-- encapsulate the type defeq hell in this lemma
lemma existsUnique_add_prod (x : 𝔫) : ∃! p : D.𝔞 × D.𝔥, (p.1 : 𝔫) + p.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod D.isCompl_toSubmodule x

end NilStepAdoData

def PreNilStepAdoSpace (D : NilStepAdoData K 𝔫) :=
  UniversalEnvelopingAlgebra K D.𝔞
deriving AddCommGroup, Module K

namespace PreNilStepAdoSpace

open UniversalEnvelopingAlgebra (ι)

variable {D : NilStepAdoData K 𝔫}

def equiv : UniversalEnvelopingAlgebra K D.𝔞 ≃ₗ[K] PreNilStepAdoSpace D :=
  LinearEquiv.refl K (UniversalEnvelopingAlgebra K D.𝔞)

@[ext]
lemma ext {p q : PreNilStepAdoSpace D} (h : equiv.symm p = equiv.symm q) : p = q := by
  simpa using h

@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {motive : PreNilStepAdoSpace D → Sort*} :
    (equiv : Π a, motive (equiv a)) → Π a, motive a :=
  fun equiv' a ↦ equiv' (equiv.symm a)

noncomputable instance : Bracket 𝔫 (PreNilStepAdoSpace D) where
  bracket x := LinearEquiv.conj equiv
    (LinearMap.ofIsCompl D.isCompl_toSubmodule
      (toEnd K D.𝔞 (UniversalEnvelopingAlgebra K D.𝔞))
        (toEnd K D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞)) x)

lemma bracket_def (x : 𝔫) (a : PreNilStepAdoSpace D) :
    ⁅x, a⁆ = LinearEquiv.conj equiv
      (LinearMap.ofIsCompl D.isCompl_toSubmodule
        (toEnd K D.𝔞 (UniversalEnvelopingAlgebra K D.𝔞))
          (toEnd K D.𝔥 (UniversalEnvelopingAlgebra K D.𝔞)) x) a :=
  rfl

-- encapsulate the type defeq hell in this lemma
@[simp]
lemma bracket_𝔞 (x : D.𝔞) (a : PreNilStepAdoSpace D) : ⁅(x : 𝔫), a⁆ = equiv ⁅x, equiv.symm a⁆ := by
  simp only [bracket_def, LinearMap.ofIsCompl_apply_left, coe_toLinearMap,
    LinearEquiv.conj_apply_apply, bracket_eq, ι_apply, EmbeddingLike.apply_eq_iff_eq]
  rfl

-- encapsulate the type defeq hell in this lemma
@[simp]
lemma bracket_𝔥 (x : D.𝔥) (a : PreNilStepAdoSpace D) : ⁅(x : 𝔫), a⁆ = equiv ⁅x, equiv.symm a⁆ := by
  simp only [bracket_def, LinearMap.ofIsCompl_apply_right, coe_toLinearMap,
    LinearEquiv.conj_apply_apply, EmbeddingLike.apply_eq_iff_eq]
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
        rw [← LieSubmodule.coe_bracket, bracket_𝔞, LinearEquiv.symm_apply_apply, bracket_eq]
      conv =>
        enter [2]
        rw [← lie_skew, PreNilStepAdoSpace.neg_lie, ← LieSubmodule.coe_bracket, bracket_𝔞,
          LinearEquiv.symm_apply_apply, bracket_eq]
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

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
public axiom NilStepAdoData.isAdo (D : NilStepAdoData K 𝔫) : IsAdo K 𝔫

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
    obtain ⟨𝔥, h𝔥₁, h𝔥₂⟩ : ∃ 𝔥 : LieSubalgebra K 𝔫,
        IsCompl 𝔞.toSubmodule 𝔥.toSubmodule ∧ finrank K 𝔥 = 1 := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      rw [← Submodule.finrank_add_eq_of_isCompl h𝔥', finrank_toSubmodule,
        Nat.add_left_cancel_iff] at hn
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact ⟨h𝔥', hn⟩
    exact ⟨{ 𝔞, 𝔥, center_le_𝔞 := h𝔞, finrank_𝔥 := h𝔥₂, isCompl_toSubmodule := h𝔥₁ }⟩
