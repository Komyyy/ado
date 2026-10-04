/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.LieModuleHom
public import Mathlib.Algebra.Lie.Semisimple.Defs

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
