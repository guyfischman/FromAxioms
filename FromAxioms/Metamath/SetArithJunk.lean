/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import FromAxioms.Metamath.SetArith

namespace Metamath

/-! ## Packaging -/

/-- Excluded middle at `natF`, as one closed sentence. -/

def junkEmS : Formula := .all (.disj (natF 0) (.imp (natF 0) .fls))

/-- The layer on ω, as one closed sentence. -/

def junkLayS : Formula := .all (.imp (natF 0) (deltaF 0))

def junkAx : List Formula :=
  [zfPair, zfUnion, zfFound, zfExt, zfSep .fls, junkEmS, junkLayS]

def JunkOk (Γ : List Formula) : Prop := ∀ φ, φ ∈ junkAx → φ ∈ Γ

theorem JunkOk.em {Γ : List Formula} (h : JunkOk Γ) : junkEmS ∈ Γ :=
  h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))

#print axioms JunkOk.em

end Metamath
