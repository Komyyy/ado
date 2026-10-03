/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.WeylReducibility

/-!
## Whitehead の第二補題
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Set LieAlgebra LieModule

public axiom LieModule.Cohomology.surjective_d₁₂_of_hasTrivialRadical
    (K L V) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K L] [FiniteDimensional K V] [HasTrivialRadical K L] :
    SurjOn (d₁₂ K L V) univ (Cohomology.twoCocycle K L V)
