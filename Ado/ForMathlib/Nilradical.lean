/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieHom
public import Ado.ForMathlib.LieModuleNilpotent

public section

open Function LieAlgebra LieIdeal

variable (R L L₂ : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

/-- **注意:** これは `maxNilpotentIdeal` とは異なります。`maxNilpotentIdeal` は最大の `L`-冪零イデアル
ですが、`nilradical R L = 𝔫` は最大の `𝔫`-冪零イデアルです。 -/
def LieAlgebra.nilradical : LieIdeal R L :=
  sSup {N | LieRing.IsNilpotent N}

variable {R L L₂}

namespace LieRing

instance [IsNoetherian R L] : LieRing.IsNilpotent (nilradical R L) := by
  have hwf := WellFoundedGT.isSupClosedCompact (α := LieIdeal R L) inferInstance
  refine hwf {N | LieRing.IsNilpotent N} ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all only [Set.mem_ofPred] <;> infer_instance

end LieRing

namespace LieAlgebra

@[simp]
lemma nilradical_eq_top_of_isNilpotent [LieRing.IsNilpotent L] : nilradical R L = ⊤ := by
  rw [nilradical, eq_top_iff]
  apply le_sSup
  simp [‹LieRing.IsNilpotent L›]

@[simp]
lemma map_equiv_nilradical (e : L ≃ₗ⁅R⁆ L₂) :
    map e (nilradical R L) = nilradical R L₂ := by
  simp_rw [nilradical, LieIdeal.gc_map_comap e.toLieHom |>.l_sSup, sSup_eq_iSup]
  apply eq_of_forall_ge_iff
  intro I
  simp_rw [iSup₂_le_iff, Set.mem_ofPred, surjective_map_of_surjective _ e.surjective |>.forall]
  conv_rhs =>
    enter [J, 1]
    rw [← LieEquiv.lieIdealMap e J |>.nilpotent_iff_equiv_nilpotent]

@[simp]
lemma comap_equiv_nilradical (e : L ≃ₗ⁅R⁆ L₂) :
    comap e (nilradical R L₂) = nilradical R L := by
  rw [LieEquiv.comap_equiv_eq_map_symm, map_equiv_nilradical]

lemma center_le_nilradical : center R L ≤ nilradical R L :=
  have h : LieRing.IsNilpotent (center R L) := inferInstance
  le_sSup h

end LieAlgebra

namespace LieIdeal

lemma isNilpotent_iff_le_nilradical [IsNoetherian R L] (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ I ≤ nilradical R L :=
  ⟨fun h ↦ le_sSup h, fun h ↦ LieRing.isNilpotent_of_lieIdeal_le I (nilradical R L) h⟩

end LieIdeal
