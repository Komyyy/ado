/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleNilpotent

public section

open LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **注意:** これは `maxNilpotentIdeal` とは異なります。`maxNilpotentIdeal` は最大の `L`-冪零イデアル
ですが、`nilradical R L = 𝔫` は最大の `𝔫`-冪零イデアルです。 -/
def LieAlgebra.nilradical : LieIdeal R L :=
  sSup {N | LieRing.IsNilpotent N}

variable {R L}

namespace LieAlgebra

instance [IsNoetherian R L] : LieRing.IsNilpotent (nilradical R L) := by
  have hwf := WellFoundedGT.isSupClosedCompact (α := LieIdeal R L) inferInstance
  refine hwf {N | LieRing.IsNilpotent N} ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all only [Set.mem_ofPred] <;> infer_instance

@[simp]
lemma nilradical_eq_top_of_isNilpotent [LieRing.IsNilpotent L] : nilradical R L = ⊤ := by
  rw [nilradical, eq_top_iff]
  apply le_sSup
  simp [‹LieRing.IsNilpotent L›]

end LieAlgebra

namespace LieIdeal

lemma isNilpotent_iff_le_nilradical [IsNoetherian R L] (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ I ≤ nilradical R L :=
  ⟨fun h ↦ le_sSup h, fun h ↦ LieRing.isNilpotent_of_lieIdeal_le I (nilradical R L) h⟩

end LieIdeal
