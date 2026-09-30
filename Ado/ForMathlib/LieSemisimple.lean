/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleKer

public section

open LieAlgebra LieHom LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsSemisimple R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieIdeal

instance : IsFaithful R ↥(LieModule.ker R L M)ᶜ M := by
  simp_rw [isFaithful_iff_ker_eq_bot, LieIdeal.ker_eq, LieIdeal.comap_incl_eq_bot,
    disjoint_compl_left]

end LieIdeal

namespace LieAlgebra

variable (R L) in
lemma derivedSeries_one_eq_top_of_isSemisimple : derivedSeries R L 1 = ⊤ := by
  suffices h : IsSolvable ↥(derivedSeries R L 1)ᶜ
  · simpa using HasTrivialRadical.eq_bot_of_isSolvable (derivedSeries R L 1)ᶜ
  apply IsSolvable.mk (R := R) (k := 1)
  simp_rw [LieIdeal.derivedSeries_eq_bot_iff, eq_bot_iff,
    ← inf_compl_eq_bot (a := derivedSeries R L 1), le_inf_iff,
    derivedSeriesOfIdeal_le le_top le_rfl, true_and, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero, LieSubmodule.lie_le_left]

end LieAlgebra
