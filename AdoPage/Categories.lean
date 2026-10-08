/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog

open Verso.Genre.Blog.Post

namespace AdoPage

def japanese : Category where
  name := "Written in Japanese"
  slug := "japanese"

def english : Category where
  name := "Written in English"
  slug := "english"

def proposal : Category where
  name := "Proposal which came up during Ado's theorem formalization"
  slug := "proposal"

def aiTranslated : Category where
  name := "Translated by AI"
  slug := "ai-transtlated"

end AdoPage
