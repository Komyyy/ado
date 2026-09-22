/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.LinearAlgebra.Charpoly.Basic

public section

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Polynomial Module

namespace LinearMap

lemma charpoly_degree [StrongRankCondition R] : degree (charpoly f) = finrank R M := by
  have := nontrivial_of_invariantBasisNumber
  rw [charpoly, Matrix.charpoly_degree_eq_dim, finrank_eq_card_chooseBasisIndex]

end LinearMap
