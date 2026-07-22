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

variable {K 𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]
variable [LieRing.IsNilpotent 𝔤]

-- TODO: 後でインスタンスにする
attribute [local instance 100] LieRing.ofAssociativeRing

public theorem ado_of_isNilpotent : IsAdo K 𝔤 := by
  sorry

end LieAlgebra
