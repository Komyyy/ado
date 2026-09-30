/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Module.Submodule.Ker

public section

open Submodule LinearMap

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]

lemma Submodule.map_le_iff_mapsTo {f : M →ₗ[R] M₂} {p q} : map f p ≤ q ↔ Set.MapsTo f p q :=
  map_le_iff_le_comap

@[simp]
lemma Submodule.map_ker {f : M →ₗ[R] M₂} : map f (ker f) = ⊥ := by
  simp [← le_ker_iff_map]
