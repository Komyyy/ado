/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Casimir
public import Ado.ForMathlib.Complemented
public import Ado.ForMathlib.LieDerivation
public import Ado.ForMathlib.LieFitting

/-!
## Whitehead の第一補題
-/

open Function Filter LieAlgebra LieModule LieSubmodule LieModuleHom
open UniversalEnvelopingAlgebra
open LinearMap hiding restrict

variable (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
variable [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L]

namespace LieDerivation

lemma surjective_inner_of_hasTrivialRadical_of_isNilpotent_casimir
    (h : _root_.IsNilpotent (lift K (toEnd K L V) (casimir K L V))) :
    Surjective (inner K L V) := by
  apply isNilpotent_trace_of_isNilpotent at h
  simp_rw [isNilpotent_iff_eq_zero, trace_lift_casimir, sub_eq_zero, Nat.cast_inj,
    eq_comm (a := Module.finrank K L), ← eq_top_iff_finrank_eq, ← isTrivial_iff_ker] at h
  intro D
  existsi 0
  suffices h : Submodule.map D.toLinearMap (derivedSeries K L 1) = ⊥
  · simp_all [↓derivedSeries_one_eq_top_of_isSemisimple, LinearMap.range_eq_bot, DFunLike.ext_iff]
  simp_rw [_root_.eq_bot_iff, coe_derivedSeries_one_eq, Submodule.map_span, Submodule.span_le,
    Submodule.bot_coe, Set.subset_singleton_iff, Set.forall_mem_image, Set.mem_ofPred]
  rintro _ ⟨x, y, rfl⟩
  simp [trivial_lie_zero]

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

public theorem surjective_inner_of_hasTrivialRadical : Surjective (inner K L V) := by
  let πc : V →ₗ⁅K,L⁆ V :=
    { __ := lift K (toEnd K L V) (casimir K L V)
      map_lie' := by simp [lift_casimir_comm] }
  obtain ⟨W₀, W₁, hWc, ⟨hWm, hWn⟩, hWb⟩ := πc.fitting
  simp_rw +zetaDelta [← isNilpotent_toLinearMap, restrict_toLinearMap,
    restrict_lift_casimir _ hWc.isComplemented] at hWn
  intro D
  obtain ⟨v₀, hv₀⟩ :=
    surjective_inner_of_hasTrivialRadical_of_isNilpotent_casimir K L W₀ hWn
      (compCodomain D (projectionOnto W₀ W₁ hWc))
  have hWb₂ : Bijective (LinearMap.restrict πc.toLinearMap hWb.mapsTo.imp) := hWb.bijective
  rw [restrict_lift_casimir _ hWc.isComplemented_right] at hWb₂
  obtain ⟨v₁, hv₁⟩ :=
    surjective_inner_of_hasTrivialRadical_of_bijective_casimir K L W₁ hWb₂
      (compCodomain D (projectionOnto W₁ W₀ hWc.symm))
  existsi v₀ + v₁
  convert_to ∀ x : L, ⁅x, (v₀ : V)⁆ = projection W₀ W₁ hWc (D x) at hv₀
  · simp [DFunLike.ext_iff, Subtype.ext_iff]
  convert_to ∀ x : L, ⁅x, (v₁ : V)⁆ = projection W₁ W₀ hWc.symm (D x) at hv₁
  · simp [DFunLike.ext_iff, Subtype.ext_iff]
  ext x
  simp [hv₀, hv₁, projection_add_projection_eq_self]

end LieDerivation
