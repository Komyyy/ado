/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

open Module

namespace LinearMap.BilinForm

@[simp]
lemma dualBasis_reindex {K V} [Field K] [AddCommGroup V] [Module K V]
    {ι ι'} [DecidableEq ι] [DecidableEq ι'] [Finite ι] [Finite ι']
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (e : ι ≃ ι') :
    dualBasis B hB (Basis.reindex b e) = Basis.reindex (dualBasis B hB b) e := by
  ext; simp [dualBasis, LinearMap.ext_iff]

end LinearMap.BilinForm
