/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Order.Disjoint

public section Complemented

variable {α} [Lattice α] [BoundedOrder α]

lemma IsCompl.isComplemented {a b : α} (h : IsCompl a b) : IsComplemented a :=
  ⟨b, h⟩

alias IsCompl.isComplemented_left := IsCompl.isComplemented

lemma IsCompl.isComplemented_right {a b : α} (h : IsCompl a b) : IsComplemented b :=
  h.symm.isComplemented
