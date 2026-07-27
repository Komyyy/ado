/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.ApplyFun

public section

open Function

namespace Fin

@[simp]
lemma castAdd_ne_natAdd {m n} (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j := by
  apply_fun addCases (fun _ ↦ false) (fun _ ↦ true); simp

@[simp]
lemma natAdd_ne_castAdd {m n} (i : Fin n) (j : Fin m) : natAdd m i ≠ castAdd n j :=
  castAdd_ne_natAdd j i |>.symm

@[simp]
lemma update_append_castAdd {α m n} (x : Fin m → α) (y : Fin n → α) (i : Fin m) (a : α) :
    update (append x y) (castAdd n i) a = append (update x i a) y := by
  ext j; cases j using addCases <;> simp [update_apply]

@[simp]
lemma update_append_natAdd {α m n} (x : Fin m → α) (y : Fin n → α) (i : Fin n) (a : α) :
    update (append x y) (natAdd m i) a = append x (update y i a) := by
  ext j; cases j using addCases <;> simp [update_apply]

end Fin
