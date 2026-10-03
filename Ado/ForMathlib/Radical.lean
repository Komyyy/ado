/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Ado.ForMathlib.LieSolvable

public import Mathlib.Tactic.Replace

public section

open Function LieAlgebra LieIdeal

variable {R L L₂} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

attribute [instance] LieAlgebra.abelian_derivedAbelianOfIdeal

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
    have hJ₂ : IsSolvable (map (LieIdeal.Quotient.mk' I) J) :=
      (LieHom.lieIdealMap_surjective_of_image_eq_map _ _ (by simp)).lieAlgebra_isSolvable
    apply le_sSup
    simp [hJ₂]

@[simp]
lemma LieAlgebra.map_equiv_radical (e : L ≃ₗ⁅R⁆ L₂) :
    map e (radical R L) = radical R L₂ := by
  simp_rw [radical, LieIdeal.gc_map_comap e.toLieHom |>.l_sSup, sSup_eq_iSup]
  apply eq_of_forall_ge_iff
  intro I
  simp_rw [iSup₂_le_iff, Set.mem_ofPred, surjective_map_of_surjective _ e.surjective |>.forall]
  conv_rhs =>
    enter [J, 1]
    rw [← solvable_iff_equiv_solvable <| LieEquiv.lieIdealMap e J]

lemma LieEquiv.hasTrivialRadical_iff_equiv_hasTrivialRadical (e : L ≃ₗ⁅R⁆ L₂) :
    HasTrivialRadical R L ↔ HasTrivialRadical R L₂ := by
  simp [hasTrivialRadical_iff, ← map_equiv_radical e, - map_equiv_radical]

instance [IsNoetherian R L] : HasTrivialRadical R (L ⧸ radical R L) where
  radical_eq_bot := by simp [radical_quotient_eq_of_isSolvable]
