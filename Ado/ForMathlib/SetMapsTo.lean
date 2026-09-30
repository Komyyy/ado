/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Data.Set.Operations

public section

variable {α β : Type*}

namespace Set

lemma MapsTo.imp {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t) : ∀ x ∈ s, f x ∈ t :=
  h

end Set
