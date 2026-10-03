/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Basic

public section

variable {L} [LieRing L]

lemma lie_jacobi_swap (x y z : L) : ⁅⁅x, y⁆, z⁆ + ⁅⁅y, z⁆, x⁆ + ⁅⁅z, x⁆, y⁆ = 0 := by
  grind only [= lie_lie, . lie_jacobi]
