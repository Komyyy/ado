/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleKer
public import Ado.ForMathlib.LieFinrank
public import Ado.ForMathlib.LieModuleCompl

public section

open LieAlgebra LieHom LieModule LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsSemisimple R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieIdeal

instance : IsFaithful R ↥(LieModule.ker R L M)ᶜ M := by
  simp_rw [isFaithful_iff_ker_eq_bot, LieIdeal.ker_eq, LieIdeal.comap_incl_eq_bot,
    disjoint_compl_left]

@[simp]
lemma finrank_compl {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsSemisimple K L]
    [FiniteDimensional K L] (I : LieIdeal K L) :
    Module.finrank K ↥Iᶜ = Module.finrank K L - Module.finrank K I := by
  simp [← LieSubmodule.finrank_add_eq_of_isCompl (isCompl_compl (x := I))]

variable (R) in
lemma projectionOnto_lieModule_ker_compl_lie (x : L) (m : M) :
    ⁅projectionOnto (LieModule.ker R L M)ᶜ _ isCompl_compl.symm x, m⁆ = ⁅x, m⁆ := by
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ :=
    existsUnique_add_of_isCompl_prod (isCompl_compl (x := LieModule.ker R L M)).symm x |>.exists
  simp [LieModule.mem_ker _ _ _ _ |>.mp x₂.2]

variable (R) in
lemma projection_lieModule_ker_compl_lie (x : L) (m : M) :
    ⁅projection (LieModule.ker R L M)ᶜ _ isCompl_compl.symm x, m⁆ = ⁅x, m⁆ := by
  simpa using projectionOnto_lieModule_ker_compl_lie R x m

end LieIdeal

namespace LieAlgebra

variable (R L) in
lemma derivedSeries_one_eq_top_of_isSemisimple : derivedSeries R L 1 = ⊤ := by
  suffices h : IsSolvable ↥(derivedSeries R L 1)ᶜ
  · simpa using HasTrivialRadical.eq_bot_of_isSolvable (derivedSeries R L 1)ᶜ
  apply IsSolvable.mk (R := R) (k := 1)
  simp_rw [LieIdeal.derivedSeries_eq_bot_iff, _root_.eq_bot_iff,
    ← inf_compl_eq_bot (a := derivedSeries R L 1), le_inf_iff,
    derivedSeriesOfIdeal_le le_top le_rfl, true_and, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero, LieSubmodule.lie_le_left]

end LieAlgebra
