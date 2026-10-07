/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Casimir
public import Ado.ForMathlib.Complemented
public import Ado.ForMathlib.LieDerivation
public import Ado.ForMathlib.LieIrreducible

/-!
# Whitehead の第一補題
-/

open Function Filter Module LieAlgebra LieModule LieSubmodule LieModuleHom
open UniversalEnvelopingAlgebra
open LinearMap hiding restrict

variable (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace LieDerivation

variable {K L V} in
lemma surjective_inner_of_hasTrivialRadical_of_casimir_eq_zero
    (h : lift K (toEnd K L V) (casimir K L V) = 0) :
    Surjective (inner K L V) := by
  apply_fun trace K V at h
  simp_rw [map_zero, trace_lift_casimir, sub_eq_zero, Nat.cast_inj,
    eq_comm (a := Module.finrank K L), ← eq_top_iff_finrank_eq, ← isTrivial_iff_ker] at h
  intro D
  existsi 0
  suffices h : Submodule.map D.toLinearMap (derivedSeries K L 1) = ⊥
  · simp_all [↓derivedSeries_one_eq_top_of_isSemisimple, LinearMap.range_eq_bot, DFunLike.ext_iff]
  simp_rw [_root_.eq_bot_iff, coe_derivedSeries_one_eq, Submodule.map_span, Submodule.span_le,
    Submodule.bot_coe, Set.subset_singleton_iff, Set.forall_mem_image, Set.mem_ofPred]
  rintro _ ⟨x, y, rfl⟩
  simp [trivial_lie_zero]

variable {K L V} in
lemma surjective_inner_of_hasTrivialRadical_of_bijective_casimir
    (h : Bijective (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V) := by
  intro D
  obtain ⟨v, hv⟩ := exists_lift_casimir_apply_eq_lie D
  let e := LinearEquiv.ofBijective _ h
  have he : ∀ (x : L) (v : V), e.symm ⁅x, v⁆ = ⁅x, e.symm v⁆
  · simp_rw +zetaDelta +singlePass [e.surjective.forall, LinearEquiv.ofBijective_apply,
      ← lift_casimir_comm, LinearEquiv.ofBijective_symm_apply_apply, implies_true]
  existsi e.symm v
  ext x
  simp +zetaDelta [← he, LinearEquiv.symm_apply_eq, hv]

lemma surjective_inner_of_hasTrivialRadical_of_isIrreducible
    [IsIrreducible K L V] : Surjective (inner K L V) := by
  let πc : V →ₗ⁅K,L⁆ V :=
    { __ := lift K (toEnd K L V) (casimir K L V)
      map_lie' := by simp [lift_casimir_comm] }
  obtain (hc | hc) := LieModuleHom.bijective_or_eq_zero πc
  case inl => apply surjective_inner_of_hasTrivialRadical_of_bijective_casimir hc
  case inr =>
    apply_fun LieModuleHom.toLinearMap at hc
    simp_rw [πc, toLinearMap_zero] at hc
    apply surjective_inner_of_hasTrivialRadical_of_casimir_eq_zero hc

variable {K L V} in
omit [CharZero K] [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] in
lemma surjective_inner_of_hasTrivialRadical_of_quotient (W : LieSubmodule K L V)
    (hW : Surjective (inner K L W)) (hWq : Surjective (inner K L (V ⧸ W))) :
    Surjective (inner K L V) := by
  intro D
  obtain ⟨v, hv⟩ := hWq (compCodomain D (LieSubmodule.Quotient.mk' W))
  obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W v
  simp_rw +singlePass [DFunLike.ext_iff, inner_apply_apply, ← LieModuleHom.map_lie,
    compCodomain_apply, ← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero] at hv
  obtain ⟨w, hw⟩ := hW (codRestrict W (inner K L V v - D) (by simp [hv]))
  convert_to ∀ x : L, ⁅x, (w : V)⁆ = ⁅x, v⁆ - D x using 0 at hw
  · simp [DFunLike.ext_iff, Subtype.ext_iff]
  existsi v - w
  simp [DFunLike.ext_iff, hw]

public theorem surjective_inner_of_hasTrivialRadical : Surjective (inner K L V) := by
  induction hn : finrank K V using Nat.strongRec generalizing V with | ind n hin
  subst hn
  replace hin V inst inst_1 inst_2 inst_3 inst_4 hV :=
    @hin _ hV V inst inst_1 inst_2 inst_3 inst_4 rfl
  by_cases hL : IsIrreducible K L V
  case pos => apply surjective_inner_of_hasTrivialRadical_of_isIrreducible
  obtain hLs | hLn := subsingleton_or_nontrivial V
  · apply surjective_to_subsingleton
  simp_rw [isSimpleOrder_iff] at hL
  push Not at hL
  specialize hL (by simp [hLn])
  obtain ⟨W, hWb, hWt⟩ := hL
  rw [← nontrivial_iff_ne_bot] at hWb
  have hW :=
    hin W inferInstance inferInstance inferInstance inferInstance inferInstance
      (by rwa [finrank_lt_iff, lt_top_iff_ne_top])
  have hWq :=
    hin (V ⧸ W) inferInstance inferInstance inferInstance inferInstance inferInstance
      (by simp_rw [finrank_quotient, tsub_lt_self_iff, finrank_pos_iff, hWb, and_true,
        (injective_incl W).nontrivial])
  exact surjective_inner_of_hasTrivialRadical_of_quotient W hW hWq

end LieDerivation
