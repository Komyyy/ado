/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog
open Verso Genre Blog

#doc (Post) "Subobject Hell" =>

```leanInit hellExample
```

```lean hellExample
structure A where
  val : Nat

structure B extends A

attribute [coe] B.toA

instance : Coe B A where
  coe x := x.toA

structure C extends A

attribute [coe] C.toA

instance : Coe C A where
  coe x := x.toA

structure D extends B, C

attribute [coe] D.toB D.toC

instance : Coe D B where
  coe x := x.toB

instance : Coe D C where
  coe x := x.toC

def A.myDef : A where
  val := 37

def D.myDef : D where
  val := 37

@[simp, norm_cast]
theorem D.toC_toA_myDef : ((D.myDef : C) : A) = A.myDef :=
  rfl

theorem D.toB_toA_myDef : ((D.myDef : B) : A) = A.myDef := by
  norm_cast
```
