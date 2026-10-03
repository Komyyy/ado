/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Solvable
public import Ado.WeylReducibility
public import Ado.ForMathlib.Radical
public import Ado.ForMathlib.LieIdealCoe
public import Ado.ForMathlib.LieRing

/-!
## 一般の場合の Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section WhiteheadSecond

open Set LieAlgebra LieModule

public axiom LieModule.Cohomology.surjective_d₁₂_of_hasTrivialRadical
    (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V)

end WhiteheadSecond

section Levi

open Function Module LieAlgebra LieSubmodule LieIdeal LieSubalgebra LieHom LieModule
open _root_.LieIdeal renaming map → mapᵢ, Quotient.mk' → mkQ', Quotient.mk → mkQ
open LieHom renaming range → rangeₗ

attribute [local instance 100] LieRing.ofAssociativeRing

public theorem LieHom.exists_levi_splitting (K L : Type*)
    [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] :
    ∃ (s : L ⧸ radical K L →ₗ⁅K⁆ L), LeftInverse LieIdeal.Quotient.mk s := by
  induction hn : finrank K (radical K L) using Nat.strongRec generalizing L with | ind n hin
  subst hn
  replace hin L inst inst_1 inst_2 hL := @hin _ hL L inst inst_1 inst_2 rfl
  obtain hn | hn := Nat.eq_zero_or_pos (finrank K (radical K L))
  next =>
    rw [finrank_eq_zero_iff_of_free, ← not_nontrivial_iff_subsingleton, nontrivial_iff_ne_bot,
      not_ne_iff] at hn
    existsi LieIdeal.Quotient.lift _ .id (by simp [hn])
    intro x
    obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk' _ x
    simp
  replace hn : 0 < finrank K (derivedAbelianOfIdeal (radical K L))
  · simp_rw [finrank_pos_iff, nontrivial_iff_ne_bot, ne_eq, abelian_of_solvable_ideal_eq_bot_iff,
      ← ne_eq, ← nontrivial_iff_ne_bot, ← finrank_pos_iff (R := K), hn]
  have hr : radical K (L ⧸ derivedAbelianOfIdeal (radical K L)) = mapᵢ (mkQ' _) (radical K L)
  · simp [radical_quotient_eq_of_isSolvable]
  specialize hin (L ⧸ derivedAbelianOfIdeal (radical K L)) inferInstance inferInstance inferInstance
    ?_
  · convert_to finrank K
        (LieHom.range (lieIdealMap (mkQ' (derivedAbelianOfIdeal (radical K L))) (radical K L))) < _
    · simp [hr, range_eq_top _ |>.mpr]
    simp_rw [(LieHom.quotKerEquivRange _).symm.finrank_eq, finrank_quotient, lieIdealMap_ker,
      LieIdeal.Quotient.mk'_ker, (lieIdealOfEquivOfLe (derivedAbelianOfIdeal_le_self _)).finrank_eq]
    simp [hn, hn.trans_le <| finrank_mono (derivedAbelianOfIdeal_le_self _)]
  replace hin : ∃ (s : L ⧸ radical K L →ₗ⁅K⁆  L ⧸ derivedAbelianOfIdeal (radical K L)),
      LeftInverse (LieIdeal.Quotient.map _ _ .id (by simp)) s
  · obtain ⟨s, hs⟩ := hin
    let e : (L ⧸ radical K L) ≃ₗ⁅K⁆
        _ ⧸ radical K (L ⧸ derivedAbelianOfIdeal (radical K L)) :=
      LieEquiv.trans (LieIdeal.Quotient.quotientEquivQuotient
          (derivedAbelianOfIdeal (radical K L)) _ (by simp)).symm
        (LieIdeal.Quotient.equiv _ _ .refl (by simp [hr]))
    existsi LieHom.comp s e
    intro q
    obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk _ q
    convert_to LieIdeal.Quotient.map _ (radical K L) .id (by simp) (s (mkQ (mkQ x)))
        = mkQ x using 0
    · simp [e]
    generalize hq : s (mkQ (mkQ x)) = q
    obtain ⟨y, rfl⟩ := LieIdeal.Quotient.surjective_mk _ q
    specialize hs (mkQ (mkQ x))
    apply_fun e.symm at hs
    simpa [e, hq] using hs
  obtain ⟨s, hs⟩ := hin
  clear hn hr
  rsuffices ⟨s', hs'⟩ : ∃ (s' : rangeₗ s →ₗ⁅K⁆ L), ∀ x,
      (mkQ (s' x) : L ⧸ derivedAbelianOfIdeal (radical K L)) = x
  · existsi LieHom.comp s' (LieEquiv.ofInjective _ hs.injective).toLieHom
    intro q
    obtain ⟨x, rfl⟩ := LieIdeal.Quotient.surjective_mk _ q
    replace hs' := hs' (LieEquiv.ofInjective _ hs.injective (mkQ x))
    apply_fun LieIdeal.Quotient.map _ (radical K L) .id (by simp) at hs'
    simpa [hs.eq] using hs'
  let : LieRingModule
      (L ⧸ derivedAbelianOfIdeal (radical K L)) (derivedAbelianOfIdeal (radical K L)) :=
    LieRingModule.compLieHom _ (LieIdeal.Quotient.lift _
      (toEnd K L (derivedAbelianOfIdeal (radical K L))) ?wd)
  case wd =>
    simp [IsConcreteLE.le_iff, DFunLike.ext_iff,
      Subtype.forall' (p := (· ∈ derivedAbelianOfIdeal (radical K L))), - Subtype.forall,
      ← LieIdeal.coe_bracket_of_module, trivial_lie_zero]
  have : LieModule
      K (L ⧸ derivedAbelianOfIdeal (radical K L)) (derivedAbelianOfIdeal (radical K L)) :=
    LieModule.compLieHom _ _
  have : HasTrivialRadical K (rangeₗ s) :=
    (LieEquiv.ofInjective _ hs.injective).hasTrivialRadical_iff_equiv_hasTrivialRadical.mp
      inferInstance
  obtain ⟨s', hs'⟩ : ∃ (s' : rangeₗ s →ₗ[K] L), ∀ x,
      (mkQ (s' x) : L ⧸ derivedAbelianOfIdeal (radical K L)) = x := by
    convert projective_lifting_property (mkQ' (derivedAbelianOfIdeal (radical K L))).toLinearMap
        (LieSubalgebra.incl (rangeₗ s)).toLinearMap (LieIdeal.Quotient.surjective_mk' _)
    simp [DFunLike.ext_iff]
  have coe_range_s'_lie (x : rangeₗ s) (y : derivedAbelianOfIdeal (radical K L)) :
      ((⁅x, y⁆ : derivedAbelianOfIdeal (radical K L)) : L) = ⁅s' x, (y : L)⁆
  · obtain ⟨x', hx'⟩ := LieIdeal.Quotient.surjective_mk _ x.1
    specialize hs' x
    apply_fun fun x ↦ ((⁅x, y⁆ : derivedAbelianOfIdeal (radical K L)) : L) at hs'
    simpa [LieRingModule.compLieHom_apply, ← hx'] using hs'.symm
  let ω : Cohomology.twoCochain K (rangeₗ s) (derivedAbelianOfIdeal (radical K L)) :=
    ⟨LinearMap.mk₂ _ (fun x y ↦ ⟨s' ⁅x, y⁆ - ⁅s' x, s' y⁆, ?inD⟩)
      (fun _ _ _ ↦ by ext; simp only [add_lie, map_add, AddMemClass.mk_add_mk]; abel)
      (fun _ _ _ ↦ by ext; simp only [smul_lie, map_smul, SetLike.mk_smul_mk]; module)
      (fun _ _ _ ↦ by ext; simp only [lie_add, map_add, AddMemClass.mk_add_mk]; abel)
      (fun _ _ _ ↦ by ext; simp only [lie_smul, map_smul, SetLike.mk_smul_mk]; module),
      (by simp)⟩
  case inD => rw [← LieSubmodule.Quotient.mk_eq_zero]; simp [hs']
  have ω_apply_coe x y : (ω x y : L) = s' ⁅x, y⁆ - ⁅s' x, s' y⁆
  · simp [ω]
  suffices hω : ω ∈ Cohomology.twoCocycle K (rangeₗ s) (derivedAbelianOfIdeal (radical K L))
  · obtain ⟨f, -, hf⟩ := Cohomology.surjective_d₁₂_of_hasTrivialRadical K (rangeₗ s)
        (derivedAbelianOfIdeal (radical K L)) hω
    have hf₂ : ∀ x y, s' ⁅x, y⁆ + f ⁅x, y⁆ = ⁅s' x + f x, s' y + f y⁆
    · simp_rw [DFunLike.ext_iff, Subtype.ext_iff, ω_apply_coe, Cohomology.d₁₂_apply_apply,
        AddSubgroupClass.coe_sub, coe_range_s'_lie] at hf
      gconvert hf using 2 with x y hxy
      simp_rw [add_lie, lie_add, ← LieIdeal.coe_bracket, trivial_lie_zero, ZeroMemClass.coe_zero,
        add_zero, ← lie_skew (x := (f x : L)) (y := s' y)]
      linear_combination (norm := abel) -hxy
    existsi
      { s' + LieIdeal.incl (derivedAbelianOfIdeal (radical K L)) ∘ₗ f with
        map_lie' {x y} := by simp [- LieIdeal.incl_coe, hf₂] }
    intro x
    simp [hs', - LieIdeal.incl_coe]
  simp_rw [Cohomology.mem_twoCocycle_iff, DFunLike.ext_iff, Cohomology.d₂₃_apply,
    LinearMap.zero_apply]
  conv => enter [x, y, z, 1, 1, 1, 1, 1, 2]; rw [← Cohomology.twoCochain_skew]
  conv => enter [x, y, z, 1, 1, 2, 1, 2]; rw [← lie_skew]
  simp_rw [lie_neg, sub_neg_eq_add, map_neg, LinearMap.neg_apply, ← sub_eq_add_neg]
  convert_to ∀ (x y z : rangeₗ s),
      (⁅x, ω y z⁆ - ω ⁅y, z⁆ x) + (⁅y, ω z x⁆ - ω ⁅z, x⁆ y) + (⁅z, ω x y⁆ - ω ⁅x, y⁆ z) = 0 using 4
  · abel
  have h (x y z : rangeₗ s) : ⁅x, ω y z⁆ - ω ⁅y, z⁆ x = -(s' ⁅⁅y, z⁆, x⁆ + ⁅s' x, ⁅s' y, s' z⁆⁆)
  · simp_rw [coe_range_s'_lie, ω_apply_coe, lie_sub, ← lie_skew (x := s' ⁅y, z⁆) (y := s' x)]
    abel
  simp_rw [Subtype.ext_iff, coe_add, coe_sub, ZeroMemClass.coe_zero, h]
  convert_to ∀ (x y z : rangeₗ s),
      -(s' (⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆) +
        (⁅s' x, ⁅s' y, s' z⁆⁆ + ⁅s' y, ⁅s' z, s' x⁆⁆ + ⁅s' z, ⁅s' x, s' y⁆⁆)) = 0 using 4
  · simp_rw [map_add]; abel
  simp_rw [lie_jacobi, lie_jacobi_swap]
  simp

end Levi

open Function LieAlgebra LieIdeal SemiDirectSum

variable {K 𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]

attribute [local instance] LieAlgebra.IsAdo.of_isSolvable_of_charZero in
public instance LieAlgebra.IsAdo.of_charZero : IsAdo K 𝔤 := by
  obtain ⟨s, hs⟩ := LieHom.exists_levi_splitting K 𝔤
  let ψ : 𝔤 ⧸ radical K 𝔤 →ₗ⁅K⁆ LieDerivation K (radical K 𝔤) (radical K 𝔤) :=
    LieHom.comp (LieDerivation.adIdeal (radical K 𝔤)) s
  let f : 𝔤 →ₗ[K] radical K 𝔤 :=
    show 𝔤 →ₗ[K] (radical K 𝔤).toSubmodule from
    LinearMap.codRestrict _ (LinearMap.id - (LieHom.comp s (LieIdeal.Quotient.mk' _)).toLinearMap)
      (by simp [← LieSubmodule.Quotient.mk_eq_zero, hs.eq])
  have hf x : (f x : 𝔤) = x - s (LieIdeal.Quotient.mk x) :=
    rfl
  let e : (radical K 𝔤 ⋊⁅ψ⁆ 𝔤 ⧸ radical K 𝔤) ≃ₗ⁅K⁆ 𝔤 :=
    { toLieHom := lift ψ (incl (radical K 𝔤)) s (by intro x; ext y; simp [ψ, - incl_coe])
      invFun x := ⟨f x, LieIdeal.Quotient.mk x⟩
      left_inv x := by ext <;> simp [hf, hs.eq, LieSubmodule.Quotient.mk_eq_zero'.mpr]
      right_inv x := by simp [hf] }
  have he x : e.symm x = ⟨f x, LieIdeal.Quotient.mk x⟩ := rfl
  rw [← e.isAdo_iff]
  apply IsAdo.semiDirectSum_of_isSolvable
  grw [← map_equiv_nilradical e.symm, map_le_iff_le_comap, nilradical_le_radical,
    IsConcreteLE.le_iff, Subtype.forall']
  simp +contextual [he, eq_comm (a := (0 : 𝔤 ⧸ radical K 𝔤))]
