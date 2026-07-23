/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib
public import Ado.Statement

/-!
## 冪零 Lie 代数に対する Ado の定理
-/

open Function Set Module LieAlgebra LieModule
open scoped Pointwise

namespace LieAlgebra

universe u

variable {K 𝔫 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔫] [LieAlgebra K 𝔫] [FiniteDimensional K 𝔫]
variable [LieRing.IsNilpotent 𝔫]

public theorem ado_of_isNilpotent : IsAdo K 𝔫 := by
  generalize hn : finrank K 𝔫 = n
  induction n generalizing K 𝔫 with
  | zero =>
    rw [finrank_zero_iff] at hn
    fail_if_success exact .intro Unit
    sorry
  | succ n hin => sorry

end LieAlgebra
