/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.WeylReducibility
public import Ado.ForMathlib.LieIrreducible

/-!
## Whitehead の第二補題
-/

open Set Function LieAlgebra Module LieModule LieSubmodule UniversalEnvelopingAlgebra

variable (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace LieModule.Cohomology

lemma surjOn_d₁₂_trivial_scalar_twoCocycle_of_hasTrivialRadical :
    SurjOn (d₁₂ K L (TrivialLieModule K L K)) univ
      (Cohomology.twoCocycle K L (TrivialLieModule K L K)) := by
  intro f hf
  simp only [SetLike.mem_coe, image_univ, mem_range] at hf ⊢
  let A : oneCochain K L (L →ₗ[K] TrivialLieModule K L K) := -LinearMap.flip f.val
  have A_apply (x y) : A x y = -f y x := rfl
  suffices hA : ∀ (x y : L), A ⁅x, y⁆ = ⁅x, A y⁆ - ⁅y, A x⁆
  · let A' : LieDerivation K L (L →ₗ[K] TrivialLieModule K L K) := { A with leibniz' := hA }
    obtain ⟨g, hg⟩ := A'.surjective_inner_of_hasTrivialRadical
    existsi g
    simpa [DFunLike.ext_iff, A', A_apply, trivial_lie_zero, neg_eq_iff_eq_neg,
      twoCochain_skew] using hg
  -- `LieHom.lie_apply` って名前おかしくない？
  simp_rw [DFunLike.ext_iff, LinearMap.sub_apply, LieHom.lie_apply, A_apply, trivial_lie_zero]
  simp_rw [mem_twoCocycle_iff_of_trivial] at hf
  intro y z x
  specialize hf x y z
  conv_rhs => enter [1, 2, 1]; rw [← lie_skew, map_neg, LinearMap.neg_apply]
  conv_rhs => enter [2, 2]; rw [twoCochain_skew, ← lie_skew, map_neg]
  linear_combination (norm := abel) -hf

omit [FiniteDimensional K V] in
lemma surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible_of_isTrivial
    [IsIrreducible K L V] [IsTrivial L V] :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V) := by
  obtain ⟨e⟩ := Field.nonempty_lieModuleEquiv_of_isIrreducible_of_isTrivial K L V
  intro f hf
  simp only [image_univ, mem_range]
  obtain ⟨g, -, hg⟩ := surjOn_d₁₂_trivial_scalar_twoCocycle_of_hasTrivialRadical K L
    (twoCochain.compCodomain_mem_twoCocycle f e.toLieModuleHom hf)
  existsi e.symm.toLinearMap ∘ₗ g
  simp_rw [DFunLike.ext_iff, d₁₂_apply_apply_ofTrivial, LinearMap.comp_apply,
    LieModuleHom.coe_toLinearMap, LieModuleEquiv.coe_coe, neg_eq_iff_eq_neg,
    twoCochain.compCodomain_apply_apply] at hg ⊢
  simp [hg]

variable {K L V} in
lemma surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible_of_bijective_casimir
    [IsIrreducible K L V] (h : Bijective (lift K (toEnd K L V) (casimir K L V))) :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V) := by
  intro f hf
  simp only [image_univ, mem_range]
  obtain ⟨g, hg⟩ := exists_lift_casimir_twoCocycle_apply_eq_d₁₂ f hf
  let e := LinearEquiv.ofBijective _ h
  have he : ∀ (x : L) (v : V), e.symm ⁅x, v⁆ = ⁅x, e.symm v⁆
  · simp_rw +zetaDelta +singlePass [e.surjective.forall, LinearEquiv.ofBijective_apply,
      ← lift_casimir_comm, LinearEquiv.ofBijective_symm_apply_apply, implies_true]
  existsi e.symm ∘ₗ g
  simp_rw [d₁₂_apply_apply] at hg
  simp +zetaDelta [← he, LinearEquiv.symm_apply_eq, ← map_sub, DFunLike.ext_iff, hg]

lemma surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible
    [IsIrreducible K L V] : SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V) := by
  let πc : V →ₗ⁅K,L⁆ V :=
    { __ := lift K (toEnd K L V) (casimir K L V)
      map_lie' := by simp [lift_casimir_comm] }
  obtain (hc | hc) := eq_or_ne πc 0
  case inl =>
    apply_fun LinearMap.trace K V at hc
    simp_rw [πc, LieModuleHom.toLinearMap_zero, map_zero, trace_lift_casimir, sub_eq_zero,
      Nat.cast_inj, eq_comm (a := finrank K L), ← eq_top_iff_finrank_eq, ← isTrivial_iff_ker] at hc
    apply surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible_of_isTrivial
  case inr =>
    apply LieModuleHom.bijective_of_ne_zero at hc
    apply surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible_of_bijective_casimir hc

public lemma surjOn_d₁₂_twoCocycle_of_hasTrivialRadical :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V) := by
  induction hn : finrank K V using Nat.strongRec generalizing V with | ind n hin
  subst hn
  replace hin V inst inst_1 inst_2 inst_3 inst_4 hV :=
    @hin _ hV V inst inst_1 inst_2 inst_3 inst_4 rfl
  by_cases hL : IsIrreducible K L V
  case pos => apply surjOn_d₁₂_twoCocycle_of_hasTrivialRadical_of_isIrreducible
  obtain hLs | hLn := subsingleton_or_nontrivial V
  · apply surjOn_of_subsingleton'; simp
  replace hL : ∃ (W₀ W₁ : LieSubmodule K L V), IsCompl W₀ W₁ ∧ W₀ < ⊤ ∧ W₁ < ⊤
  · simp_rw [isSimpleOrder_iff] at hL
    push Not at hL
    specialize hL (by simp [hLn])
    obtain ⟨W₀, hW₀b, hW₀t⟩ := hL
    obtain ⟨W₁, hW⟩ := exists_isCompl W₀
    existsi W₀, W₁, hW
    constructor
    · rwa [lt_top_iff_ne_top]
    · rw [lt_top_iff_ne_top]
      exact hW.disjoint.ne_top_of_ne_bot hW₀b
  obtain ⟨W₀, W₁, hW, hW₀t, hW₁t⟩ := hL
  intro f hf
  simp_rw [image_univ, mem_range]
  obtain ⟨g₀, -, hg₀⟩ :=
    hin W₀ inferInstance inferInstance inferInstance inferInstance inferInstance
      (by rwa [finrank_lt_iff])
      (twoCochain.compCodomain_mem_twoCocycle f (projectionOnto W₀ W₁ hW) hf)
  obtain ⟨g₁, -, hg₁⟩ :=
    hin W₁ inferInstance inferInstance inferInstance inferInstance inferInstance
      (by rwa [finrank_lt_iff])
      (twoCochain.compCodomain_mem_twoCocycle f (projectionOnto W₁ W₀ hW.symm) hf)
  existsi LinearMap.comp (incl W₀).toLinearMap g₀ + LinearMap.comp (incl W₁).toLinearMap g₁
  simp only [DFunLike.ext_iff, d₁₂_apply_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LieModuleHom.coe_toLinearMap, incl_apply, lie_add, Subtype.ext_iff, coe_sub,
    twoCochain.compCodomain_apply_apply, coe_projectionOnto_apply, coe_bracket] at hg₀ hg₁ ⊢
  intro x y
  convert_to projection W₀ W₁ hW (f x y) + projection W₁ W₀ hW.symm (f x y) = _
  · linear_combination (norm := abel) (hg₀ x y) + (hg₁ x y)
  rw [projection_add_projection_eq_self]

end LieModule.Cohomology
