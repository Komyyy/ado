/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleHom
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.RingTheory.SimpleRing.DivisionRing

section ForMathlib

public section LieModuleTrivial

open LieModule

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [IsTrivial L M]

namespace LieSubmodule

variable (R L M) in
@[expose]
def equivSubmoduleOfTrivial : LieSubmodule R L M ≃o Submodule R M where
  toFun N := N
  invFun N := { N with lie_mem := by simp [trivial_lie_zero] }
  map_rel_iff' {N₀ N₁} := by simp

@[simp]
lemma equivSubmoduleOfTrivial_apply (N) : equivSubmoduleOfTrivial R L M N = N.toSubmodule :=
  rfl

@[simp]
lemma toSubmodule_equivSubmoduleOfTrivial_symm (N) :
   ((equivSubmoduleOfTrivial R L M).symm N).toSubmodule = N :=
  rfl

@[simp]
lemma mem_equivSubmoduleOfTrivial_symm (x N) :
    x ∈ (equivSubmoduleOfTrivial R L M).symm N ↔ x ∈ N :=
  Iff.rfl

end LieSubmodule

namespace LieModule

end LieModule

end LieModuleTrivial

end ForMathlib

public section

open Function LieModule

variable {R L M M₂ : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

namespace LieModuleHom

lemma injective_or_eq_zero [IsIrreducible R L M] (f : M →ₗ⁅R,L⁆ M₂) : Injective f ∨ f = 0 := by
  have h := eq_bot_or_eq_top (ker f)
  simpa [LieModuleHom.ker_eq_bot] using h

lemma injective_of_ne_zero [IsIrreducible R L M] {f : M →ₗ⁅R,L⁆ M₂} (h : f ≠ 0) : Injective f :=
  injective_or_eq_zero f |>.resolve_right h

lemma surjective_or_eq_zero [IsIrreducible R L M₂] (f : M →ₗ⁅R,L⁆ M₂) : Surjective f ∨ f = 0 := by
  have h := eq_top_or_eq_bot (range f)
  simpa [LieModuleHom.range_eq_top, LieModuleHom.range_eq_bot] using h

lemma surjective_of_ne_zero [IsIrreducible R L M₂] {f : M →ₗ⁅R,L⁆ M₂} (h : f ≠ 0) : Surjective f :=
  surjective_or_eq_zero f |>.resolve_right h

lemma bijective_of_ne_zero [IsIrreducible R L M] [IsIrreducible R L M₂] {f : M →ₗ⁅R,L⁆ M₂}
    (h : f ≠ 0) : Bijective f :=
  ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩

lemma bijective_or_eq_zero [IsIrreducible R L M] [IsIrreducible R L M₂] {f : M →ₗ⁅R,L⁆ M₂} :
    Bijective f ∨ f = 0 :=
  or_iff_not_imp_right.mpr bijective_of_ne_zero

end LieModuleHom

lemma Field.nonempty_lieModuleEquiv_of_isIrreducible_of_isTrivial (K L V)
    [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup V] [Module K V]
    [LieRingModule L V] [LieModule K L V] [IsIrreducible K L V] [IsTrivial L V] :
    Nonempty (V ≃ₗ⁅K,L⁆ TrivialLieModule K L K) := by
  rename IsIrreducible K L V => hV
  simp_rw [(LieSubmodule.equivSubmoduleOfTrivial K L V).isSimpleOrder_iff,
    ← isSimpleModule_iff] at hV
  obtain ⟨e⟩ := DivisionRing.nonempty_linearEquiv_of_isSimpleModule K V
  replace e := e.trans (TrivialLieModule.equiv K L K).symm
  replace e : V ≃ₗ⁅K,L⁆ TrivialLieModule K L K := { e with map_lie' := by simp [trivial_lie_zero] }
  exact ⟨e⟩
