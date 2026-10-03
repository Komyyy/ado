/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Solvable
public import Ado.ForMathlib.LieIdealLieSubalgebra
public import Ado.ForMathlib.LieSolvable

public import Mathlib.Tactic.Replace

public section

open Function LieAlgebra

variable {R L} [CommRing R] [LieRing L] [LieAlgebra R L]

lemma LieIdeal.radical_quotient_eq_of_isSolvable (I : LieIdeal R L) [IsSolvable I] :
    radical R (L ⧸ I) = map (LieIdeal.Quotient.mk' I) (radical R L) := by
  apply le_antisymm
  · simp_rw [radical, LieIdeal.gc_map_comap _ |>.l_sSup, sSup_le_iff, Set.mem_ofPred]
    intro J hJ
    apply le_iSup₂_of_le (comap (LieIdeal.Quotient.mk' I) J)
    · simp [LieIdeal.map_comap_eq
        (LieHom.isIdealMorphism_of_surjective _ <| LieIdeal.Quotient.surjective_mk' I)]
    have hI : I ≤ comap (LieIdeal.Quotient.mk' I) J
    · grw [← LieHom.ker_le_comap, LieIdeal.Quotient.mk'_ker]
    rw [← isSolvable_short_exact_iff (lieIdealOf I (comap (LieIdeal.Quotient.mk' I) J))]
    constructor
    · rwa [solvable_iff_equiv_solvable (lieIdealOfEquivOfLe hI)]
    · replace hI : Nonempty ((_ ⧸ lieIdealOf I (comap (LieIdeal.Quotient.mk' I) J)) ≃ₗ⁅R⁆
          (_ ⧸ LieHom.ker (LieHom.lieIdealComap (LieIdeal.Quotient.mk' I) J))) :=
        ⟨LieIdeal.Quotient.equiv _ _ LieEquiv.refl (by simp)⟩
      rwa [hI.elim fun e ↦ solvable_iff_equiv_solvable e,
        solvable_iff_equiv_solvable (LieHom.quotKerEquivRange _),
        solvable_iff_equiv_solvable (LieEquiv.ofEq (LieHom.range
          (LieHom.lieIdealComap (LieIdeal.Quotient.mk' I) J)) ⊤
          (by norm_cast; simp [LieHom.range_eq_top])),
        solvable_iff_equiv_solvable LieSubalgebra.topEquiv]
  · simp_rw [radical, LieIdeal.gc_map_comap _ |>.l_sSup, iSup₂_le_iff, Set.mem_ofPred]
    intro J hJ
    suffices h : ∃ J' : LieIdeal R (L ⧸ I), J'.toLieSubalgebra =
        LieSubalgebra.map (LieIdeal.Quotient.mk' I) J.toLieSubalgebra
    · rw [← image_eq_map_iff_exists_lieIdeal_toLieSubalgebra_eq_map] at h
      have hJ₂ : IsSolvable (map (LieIdeal.Quotient.mk' I) J) :=
        (LieHom.lieIdealMap_surjective_of_image_eq_map _ _ h).lieAlgebra_isSolvable
      apply le_sSup
      simp [hJ₂]
    convert_to ∀ (x a : L), a ∈ J → ∃ y ∈ J,
        (LieIdeal.Quotient.mk y : L ⧸ I) =
          ⁅(LieIdeal.Quotient.mk x : L ⧸ I), (LieIdeal.Quotient.mk a : L ⧸ I)⁆ using 0
    · simp [LieSubalgebra.exists_lieIdeal_coe_eq_iff, LieIdeal.Quotient.surjective_mk' _ |>.forall]
    intro x a ha
    existsi ⁅x, a⁆, LieSubmodule.lie_mem _ ha
    simp
