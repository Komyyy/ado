/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.WeylReducibility

/-!
## Whitehead の第二補題
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Set LieAlgebra Module LieModule LieSubmodule

public axiom LieModule.Cohomology.surjOn_twoCocycle_d₁₂_of_hasTrivialRadical_of_isIrreducible
    (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] [IsIrreducible K L V] :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V)

public lemma LieModule.Cohomology.surjOn_twoCocycle_d₁₂_of_hasTrivialRadical
    (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V) := by
  induction hn : finrank K V using Nat.strongRec generalizing V with | ind n hin
  subst hn
  replace hin V inst inst_1 inst_2 inst_3 inst_4 hV :=
    @hin _ hV V inst inst_1 inst_2 inst_3 inst_4 rfl
  by_cases hL : IsIrreducible K L V
  case pos => apply surjOn_twoCocycle_d₁₂_of_hasTrivialRadical_of_isIrreducible
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
