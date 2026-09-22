/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Data.Multiset.Replicate

public section

namespace Multiset

lemma replicate_lt_replicate {α} (a : α) {k n} : replicate k a < replicate n a ↔ k < n := by
  simp +contextual [lt_iff_le_not_ge (α := Multiset α), replicate_le_replicate, le_of_lt]

end Multiset
