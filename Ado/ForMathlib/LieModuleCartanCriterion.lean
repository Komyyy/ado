/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō, Scott Carnahan, Chris Henson
-/
module
public import Ado.ForMathlib.LieAssociative
public import Ado.ForMathlib.LieModuleNilpotent
public import Ado.ForMathlib.LieModuleTransferInstance
public import Ado.ForMathlib.LieSolvable
public import Mathlib.Algebra.Lie.CartanCriterion

public section

open Module LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Proof by Scott Carnahan & Chris Henson.
[Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Another.20form.20of.20Cartan.27s.20criterion.20for.20solvability/near/627103984) -/
lemma LieIdeal.isSolvable_of_traceFrom_apply_lie_eq_zero_of_isFaithful
    {R L} (M) [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [IsNoetherian R M] [Module.Free R M]
    (I : LieIdeal R L) [IsFaithful R I M]
    (h : ∀ x, ∀ y ∈ ⁅I, I⁆, traceForm R L M x y = 0) :
    IsSolvable I := by
  let J := (derivedSeries R (derivedSeriesOfIdeal R L 1 I) 1)
  have : IsFaithful R J M
  · have : IsFaithful R (derivedSeriesOfIdeal R L 1 I) M :=
      { injective_toEnd :=
          IsFaithful.injective_toEnd (L := I) |>.comp
            (LieIdeal.inclusion_injective (derivedSeriesOfIdeal_le_self I 1)) }
    infer_instance
  suffices h : IsSolvable J by simpa [J] using h
  suffices h : LieRing.IsNilpotent J by infer_instance
  suffices h : IsNilpotent J M
  · simp_rw +singlePass [LieHom.equivRangeOfInjective (toEnd R J M) IsFaithful.injective_toEnd
        |>.nilpotent_iff_equiv_nilpotent, LieAlgebra.isNilpotent_iff_forall (R := R),
      (toEnd R J M).surjective_rangeRestrict.forall, LieHom.rangeRestrict_apply]
    intro x
    apply isNilpotent_ad_of_isNilpotent
    apply LieModule.isNilpotent_toEnd_of_isNilpotent
  apply isNilpotent_derivedSeries_of_traceForm_eq_zero
  simp_rw +contextual [DFunLike.ext_iff, SetLike.forall, LinearMap.zero_apply,
    traceForm_apply_apply, LieIdeal.toEnd_mk, ← traceForm_apply_apply, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero, h, implies_true]

lemma LieAlgebra.isSolvable_of_traceFrom_apply_lie_eq_zero_of_isFaithful
    (R L M) [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [IsNoetherian R M] [Module.Free R M] [IsFaithful R L M]
    (h : ∀ x, ∀ y ∈ derivedSeries R L 1, traceForm R L M x y = 0) :
    IsSolvable L := by
  simpa using
    LieIdeal.isSolvable_of_traceFrom_apply_lie_eq_zero_of_isFaithful M (⊤ : LieIdeal R L) h
