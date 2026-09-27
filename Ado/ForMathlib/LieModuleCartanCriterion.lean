/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō, Scott Carnahan
-/
module
public import Ado.ForMathlib.LieAssociative
public import Ado.ForMathlib.LieModuleNilpotent
public import Ado.ForMathlib.LieModuleTransferInstance
public import Ado.ForMathlib.LieSolvable
public import Mathlib.Algebra.Lie.CartanCriterion

public section

open Module LieModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Proof by Scott Carnahan. [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Another.20form.20of.20Cartan.27s.20criterion.20for.20solvability/near/627103984) -/
lemma LieAlgebra.isSolvable_of_traceFrom_apply_lie_eq_zero_of_isFaithful
    (R L M) [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [IsNoetherian R M] [Module.Free R M] [IsFaithful R L M]
    (h : ∀ x, ∀ y ∈ derivedSeries R L 1, traceForm R L M x y = 0) :
    IsSolvable L := by
  let I := (derivedSeries R (derivedSeries R L 1) 1)
  suffices h : IsSolvable I by simpa [I] using h
  suffices h : LieRing.IsNilpotent I by infer_instance
  suffices h : IsNilpotent I M
  · simp_rw +singlePass [← isNilpotent_range_toEnd_iff R, isNilpotent_iff_eventually R,
      ← LieSubmodule.toSubmodule_eq_bot, End.toSubmodule_lowerCentralSeries_lieSubalgebra_eq] at h
    simp_rw +singlePass [LieEquiv.ofInjective (toEnd R I M)
        IsFaithful.injective_toEnd |>.nilpotent_iff_equiv_nilpotent, isNilpotent_iff_eventually R]
    apply h.mono
    intro k h
    conv =>
      change LieModule.lowerCentralSeries R (LieHom.range (toEnd R I M))
        (LieHom.range (toEnd R I M)).toLieSubmodule k =
          (⊥ : LieSubmodule R (LieHom.range (toEnd R I M))
            (LieHom.range (toEnd R I M)).toLieSubmodule)
    grw [LieSubmodule.lowerCentralSeries_eq_bot_iff_lcs_eq_bot, ← LieSubmodule.toSubmodule_eq_bot,
      eq_bot_iff, toSubmodule_lowerCentralSeries_lieSubalgebra_le_top_pow, ← eq_bot_iff]
    simp_rw [eq_bot_iff, Submodule.map₂_le, LinearMap.applyₗ_apply_apply, Submodule.mem_top,
      true_implies, Submodule.mem_bot] at h
    simp_rw +contextual [Submodule.pow_succ, eq_bot_iff, Submodule.mul_le, Submodule.mem_bot,
      LinearMap.ext_iff, End.mul_apply, LinearMap.zero_apply, h, implies_true]
  apply isNilpotent_derivedSeries_of_traceForm_eq_zero
  simp_rw +contextual [DFunLike.ext_iff, SetLike.forall, LinearMap.zero_apply,
    traceForm_apply_apply, LieIdeal.toEnd_mk, ← traceForm_apply_apply, h, implies_true]
