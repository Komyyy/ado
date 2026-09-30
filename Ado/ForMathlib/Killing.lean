/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

open LinearMap.BilinForm Submodule LieAlgebra LieModule LieIdeal
open LinearMap hiding Nondegenerate

section CommRing

variable {R L : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieAlgebra

attribute [mk_iff isKilling_iff_killingCompl_top_eq_bot] IsKilling

lemma isKilling_iff_nondegenerate_killingForm :
    IsKilling R L ↔ Nondegenerate (killingForm R L) := by
  simp_rw [isKilling_iff_killingCompl_top_eq_bot,
    traceForm_isSymm R L L |>.isRefl.nondegenerate_iff_separatingRight,
    SeparatingRight, eq_bot_iff, IsConcreteLE.le_iff]
  simp

end LieAlgebra

namespace LieIdeal

/-- `BilinForm.orthogonal` と `Submodule.orthogonalBilin` で重複があってややこしい。統合したい。 -/
lemma toSubmodule_killingCompl_eq_orthogonalBilin (I : LieIdeal R L) :
    (killingCompl R L I).toSubmodule = orthogonalBilin (killingForm R L) I.toSubmodule := by
  ext; simp

lemma killingCompl_sup (I J : LieIdeal R L) :
    killingCompl R L (I ⊔ J) = killingCompl R L I ⊓ killingCompl R L J := by
  simp only [← LieSubmodule.toSubmodule_inj, toSubmodule_killingCompl_eq_orthogonalBilin,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule, orthogonalBilin_sup]

end LieIdeal

end CommRing

section Field

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

namespace LieIdeal

set_option allowUnsafeReducibility true in
attribute [local reducible] LieIdeal.toLieSubalgebra in
lemma isKilling_iff_isCompl_killingForm {I : LieIdeal K L} :
    IsKilling K I ↔ IsCompl I (killingCompl K L I) := by
  simp_rw [isKilling_iff_nondegenerate_killingForm, killingForm_eq,
    restrict_nondegenerate_iff_isCompl_orthogonal <| traceForm_isSymm K L L |>.isRefl,
    ← toSubmodule_killingCompl, LieSubmodule.isCompl_toSubmodule]

lemma isKilling_iff_disjoint_killingForm {I : LieIdeal K L} :
    IsKilling K I ↔ Disjoint I (killingCompl K L I) := by
  simp_rw [isKilling_iff_isCompl_killingForm, ← LieSubmodule.isCompl_toSubmodule,
    ← LieSubmodule.disjoint_toSubmodule, toSubmodule_killingCompl,
    isCompl_orthogonal_iff_disjoint <| traceForm_isSymm K L L |>.isRefl]

instance (I : LieIdeal K L) [IsKilling K L] : IsKilling K I := by
  simp [isKilling_iff_isCompl_killingForm, LieIdeal.isCompl_killingCompl]

-- `LieIdeal K L` が分配束であれば解けるが、モジュラー束なので、良い示し方が分からない
theorem_wanted isKilling_iff_of_isCompl (I J : LieIdeal K L) (h : IsCompl I J) :
    IsKilling K L ↔ IsKilling K I ∧ IsKilling K J

end LieIdeal

end Field
