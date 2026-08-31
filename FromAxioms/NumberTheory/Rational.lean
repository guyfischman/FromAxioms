/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The rationals.

`ℚ` is `ℤ × ℤ_{>0}` modulo `(a,b) ~ (c,d) ↔ a·d = c·b`.

Denominators are strictly positive, not merely nonzero. With arbitrary
nonzero denominators every rational has two representations of opposite sign,
and the order `a/b ≤ c/d ↔ a·d ≤ c·b` then needs a case split on the sign of
`b·d`. Restricting to positive denominators removes the case split, so the
order on ℚ is -- and hence Dedekind cuts -- tractable.

Transitivity is where ℤ has to be a domain: from `a·d = c·b` and `c·f = e·d`
one reaches `d·(a·f) = d·(e·b)` by associativity and commutativity, and then
needs `intMul_left_cancel` to drop the `d`.
-/

import FromAxioms.NumberTheory.Integer

universe u

open Algebra SetTheory
namespace NumberTheory

def ratPairs : ZFSet.{u} := prod Int.{u} intPositive.{u}

theorem mem_ratPairs_iff (p : ZFSet.{u}) :
    p ∈ ratPairs.{u} ↔ ∃ a, a ∈ Int.{u} ∧ ∃ b, b ∈ intPositive.{u} ∧ p = opair a b :=
  mem_prod_iff p _ _

def ratRel : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, p = opair (opair a b) (opair c d) ∧ intMul a d = intMul c b)
    (prod ratPairs.{u} ratPairs.{u})

theorem mem_ratRel_iff {a b c d : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    opair (opair a b) (opair c d) ∈ ratRel.{u} ↔ intMul a d = intMul c b :=
  mem_pairRel_iff (opair_mem_prod ha hb) (opair_mem_prod hc hd)

theorem ratRel_isEquivRel : IsEquivRel ratRel.{u} ratPairs.{u} where
  refl p hp := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_ratPairs_iff p).mp hp
    exact (mem_ratRel_iff ha hb ha hb).mpr rfl
  symm p q hp hq h := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_ratPairs_iff p).mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_ratPairs_iff q).mp hq
    exact (mem_ratRel_iff hc hd ha hb).mpr ((mem_ratRel_iff ha hb hc hd).mp h).symm
  trans p q s hp hq hs h₁ h₂ := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_ratPairs_iff p).mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_ratPairs_iff q).mp hq
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_ratPairs_iff s).mp hs
    have hbI := intPositive_subset _ hb
    have hdI := intPositive_subset _ hd
    have hfI := intPositive_subset _ hf
    have e₁ := (mem_ratRel_iff ha hb hc hd).mp h₁
    have e₂ := (mem_ratRel_iff hc hd he hf).mp h₂
    refine (mem_ratRel_iff ha hb he hf).mpr ?_
    refine intMul_left_cancel hdI (intMul_mem_Int ha hfI) (intMul_mem_Int he hbI)
      (intPositive_ne_zero hd) ?_
    calc intMul d (intMul a f)
        = intMul (intMul d a) f := (intMul_assoc hdI ha hfI).symm
      _ = intMul (intMul a d) f := by rw [intMul_comm hdI ha]
      _ = intMul (intMul c b) f := by rw [e₁]
      _ = intMul c (intMul b f) := intMul_assoc hc hbI hfI
      _ = intMul c (intMul f b) := by rw [intMul_comm hbI hfI]
      _ = intMul (intMul c f) b := (intMul_assoc hc hfI hbI).symm
      _ = intMul (intMul e d) b := by rw [e₂]
      _ = intMul e (intMul d b) := intMul_assoc he hdI hbI
      _ = intMul e (intMul b d) := by rw [intMul_comm hdI hbI]
      _ = intMul (intMul e b) d := (intMul_assoc he hbI hdI).symm
      _ = intMul d (intMul e b) := intMul_comm (intMul_mem_Int he hbI) hdI

/-- The rationals. -/
def Rat : ZFSet.{u} := quotientSet ratRel.{u} ratPairs.{u}

/-- `a / b` as a rational. -/
def ratOf (a b : ZFSet.{u}) : ZFSet.{u} := cls ratRel.{u} ratPairs.{u} (opair a b)

theorem ratOf_mem_Rat {a b : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u}) :
    ratOf a b ∈ Rat.{u} :=
  cls_mem_quotientSet (opair_mem_prod ha hb)

theorem ratOf_eq_ratOf_iff {a b c d : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ratOf a b = ratOf c d ↔ intMul a d = intMul c b :=
  Iff.trans
    (cls_eq_cls_iff ratRel_isEquivRel (opair_mem_prod ha hb) (opair_mem_prod hc hd))
    (mem_ratRel_iff ha hb hc hd)

theorem mem_Rat_iff (r : ZFSet.{u}) :
    r ∈ Rat.{u} ↔ ∃ a, a ∈ Int.{u} ∧ ∃ b, b ∈ intPositive.{u} ∧ r = ratOf a b := by
  refine Iff.trans (mem_quotientSet_iff _ _ r) ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_ratPairs_iff p).mp hp
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨opair a b, opair_mem_prod ha hb, rfl⟩

/-! ## Arithmetic

The operations quantify into the classes rather than selecting representatives,
as ℤ's do. The condition is stated as membership in the class of the result *of
those representatives*, so well-definedness is one equality of classes --
`ratOf_add_congr`, `ratOf_mul_congr` -- instead of an equation to be replayed in
every proof. -/

theorem ratOf_subset (a b : ZFSet.{u}) : ratOf a b ⊆ ratPairs.{u} := cls_subset _ _ _

theorem mem_ratOf_iff {a b : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (p : ZFSet.{u}) :
    p ∈ ratOf a b ↔ ∃ x, x ∈ Int.{u} ∧ ∃ y, y ∈ intPositive.{u} ∧
      p = opair x y ∧ intMul a y = intMul x b := by
  refine Iff.trans (mem_cls_iff _ _ _ p) ⟨?_, ?_⟩
  · rintro ⟨hp, hr⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_ratPairs_iff p).mp hp
    exact ⟨x, hx, y, hy, rfl, (mem_ratRel_iff ha hb hx hy).mp hr⟩
  · rintro ⟨x, hx, y, hy, rfl, he⟩
    exact ⟨opair_mem_prod hx hy, (mem_ratRel_iff ha hb hx hy).mpr he⟩

def ratAdd (r s : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ r ∧ opair c d ∈ s ∧
        p ∈ ratOf (intAdd (intMul a d) (intMul c b)) (intMul b d)) ratPairs.{u}

def ratNeg (r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b, opair a b ∈ r ∧ p ∈ ratOf (intNeg a) b) ratPairs.{u}

theorem ratOf_add_congr {a b c d a' b' c' d' : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u})
    (ha' : a' ∈ Int.{u}) (hb' : b' ∈ intPositive.{u})
    (hc' : c' ∈ Int.{u}) (hd' : d' ∈ intPositive.{u})
    (h₁ : intMul a b' = intMul a' b) (h₂ : intMul c d' = intMul c' d) :
    ratOf (intAdd (intMul a d) (intMul c b)) (intMul b d)
      = ratOf (intAdd (intMul a' d') (intMul c' b')) (intMul b' d') := by
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hb'I := intPositive_subset _ hb'
  have hd'I := intPositive_subset _ hd'
  have e₁ : intMul (intMul a d) (intMul b' d') = intMul (intMul a' d') (intMul b d) :=
    calc intMul (intMul a d) (intMul b' d')
        = intMul (intMul a b') (intMul d d') := intMul_mul_comm ha hdI hb'I hd'I
      _ = intMul (intMul a' b) (intMul d d') := by rw [h₁]
      _ = intMul (intMul a' b) (intMul d' d) := by rw [intMul_comm hdI hd'I]
      _ = intMul (intMul a' d') (intMul b d) := intMul_mul_comm ha' hbI hd'I hdI
  have e₂ : intMul (intMul c b) (intMul b' d') = intMul (intMul c' b') (intMul b d) :=
    calc intMul (intMul c b) (intMul b' d')
        = intMul (intMul c b) (intMul d' b') := by rw [intMul_comm hb'I hd'I]
      _ = intMul (intMul c d') (intMul b b') := intMul_mul_comm hc hbI hd'I hb'I
      _ = intMul (intMul c' d) (intMul b b') := by rw [h₂]
      _ = intMul (intMul c' d) (intMul b' b) := by rw [intMul_comm hbI hb'I]
      _ = intMul (intMul c' b') (intMul d b) := intMul_mul_comm hc' hdI hb'I hbI
      _ = intMul (intMul c' b') (intMul b d) := by rw [intMul_comm hdI hbI]
  refine (ratOf_eq_ratOf_iff
    (intAdd_mem_Int (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI))
    (intMul_mem_intPositive hb hd)
    (intAdd_mem_Int (intMul_mem_Int ha' hd'I) (intMul_mem_Int hc' hb'I))
    (intMul_mem_intPositive hb' hd')).mpr ?_
  rw [intAdd_mul (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI)
        (intMul_mem_Int hb'I hd'I),
      intAdd_mul (intMul_mem_Int ha' hd'I) (intMul_mem_Int hc' hb'I)
        (intMul_mem_Int hbI hdI),
      e₁, e₂]

theorem ratOf_neg_congr {a b a' b' : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (ha' : a' ∈ Int.{u}) (hb' : b' ∈ intPositive.{u})
    (h : intMul a b' = intMul a' b) : ratOf (intNeg a) b = ratOf (intNeg a') b' := by
  have hbI := intPositive_subset _ hb
  have hb'I := intPositive_subset _ hb'
  refine (ratOf_eq_ratOf_iff (intNeg_mem_Int ha) hb (intNeg_mem_Int ha') hb').mpr ?_
  rw [intNeg_mul ha hb'I, intNeg_mul ha' hbI, h]

theorem ratAdd_ratOf {a b c d : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ratAdd (ratOf a b) (ratOf c d)
      = ratOf (intAdd (intMul a d) (intMul c b)) (intMul b d) := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', c', d', h₁, h₂, hmem⟩
    obtain ⟨_, ha', _, hb', he₁, r₁⟩ := (mem_ratOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    obtain ⟨_, hc', _, hd', he₂, r₂⟩ := (mem_ratOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective he₂
    rwa [← ratOf_add_congr ha hb hc hd ha' hb' hc' hd' r₁ r₂] at hmem
  · intro hmem
    exact ⟨ratOf_subset _ _ p hmem, a, b, c, d,
      mem_cls_self ratRel_isEquivRel (opair_mem_prod ha hb),
      mem_cls_self ratRel_isEquivRel (opair_mem_prod hc hd), hmem⟩

theorem ratNeg_ratOf {a b : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u}) :
    ratNeg (ratOf a b) = ratOf (intNeg a) b := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', h₁, hmem⟩
    obtain ⟨_, ha', _, hb', he₁, r₁⟩ := (mem_ratOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    rwa [← ratOf_neg_congr ha hb ha' hb' r₁] at hmem
  · intro hmem
    exact ⟨ratOf_subset _ _ p hmem, a, b,
      mem_cls_self ratRel_isEquivRel (opair_mem_prod ha hb), hmem⟩

theorem ratAdd_mem_Rat {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratAdd r s ∈ Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  rw [ratAdd_ratOf ha hb hc hd]
  exact ratOf_mem_Rat
    (intAdd_mem_Int (intMul_mem_Int ha (intPositive_subset _ hd))
      (intMul_mem_Int hc (intPositive_subset _ hb)))
    (intMul_mem_intPositive hb hd)

theorem ratNeg_mem_Rat {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) : ratNeg r ∈ Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  rw [ratNeg_ratOf ha hb]
  exact ratOf_mem_Rat (intNeg_mem_Int ha) hb

theorem ratAdd_comm {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratAdd r s = ratAdd s r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  rw [ratAdd_ratOf ha hb hc hd, ratAdd_ratOf hc hd ha hb,
      intAdd_comm (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI),
      intMul_comm hdI hbI]

theorem ratAdd_assoc {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) : ratAdd (ratAdd r s) t = ratAdd r (ratAdd s t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hfI := intPositive_subset _ hf
  -- the denominators agree by associativity, so only the numerators are at issue
  have hn : intAdd (intMul (intAdd (intMul a d) (intMul c b)) f) (intMul e (intMul b d))
      = intAdd (intMul a (intMul d f)) (intMul (intAdd (intMul c f) (intMul e d)) b) := by
    have g₁ : intMul (intMul c b) f = intMul (intMul c f) b := by
      rw [intMul_assoc hc hbI hfI, intMul_comm hbI hfI, ← intMul_assoc hc hfI hbI]
    have g₂ : intMul e (intMul b d) = intMul (intMul e d) b := by
      rw [intMul_comm hbI hdI, ← intMul_assoc he hdI hbI]
    rw [intAdd_mul (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI) hfI,
        intAdd_mul (intMul_mem_Int hc hfI) (intMul_mem_Int he hdI) hbI,
        intMul_assoc ha hdI hfI,
        intAdd_assoc (intMul_mem_Int ha (intMul_mem_Int hdI hfI))
          (intMul_mem_Int (intMul_mem_Int hc hbI) hfI)
          (intMul_mem_Int he (intMul_mem_Int hbI hdI)),
        g₁, g₂]
  rw [ratAdd_ratOf ha hb hc hd, ratAdd_ratOf hc hd he hf,
      ratAdd_ratOf (intAdd_mem_Int (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI))
        (intMul_mem_intPositive hb hd) he hf,
      ratAdd_ratOf ha hb (intAdd_mem_Int (intMul_mem_Int hc hfI) (intMul_mem_Int he hdI))
        (intMul_mem_intPositive hd hf),
      intMul_assoc hbI hdI hfI, hn]

def ratMul (r s : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ r ∧ opair c d ∈ s ∧
        p ∈ ratOf (intMul a c) (intMul b d)) ratPairs.{u}

theorem ratOf_mul_congr {a b c d a' b' c' d' : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u})
    (ha' : a' ∈ Int.{u}) (hb' : b' ∈ intPositive.{u})
    (hc' : c' ∈ Int.{u}) (hd' : d' ∈ intPositive.{u})
    (h₁ : intMul a b' = intMul a' b) (h₂ : intMul c d' = intMul c' d) :
    ratOf (intMul a c) (intMul b d) = ratOf (intMul a' c') (intMul b' d') := by
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hb'I := intPositive_subset _ hb'
  have hd'I := intPositive_subset _ hd'
  refine (ratOf_eq_ratOf_iff (intMul_mem_Int ha hc) (intMul_mem_intPositive hb hd)
    (intMul_mem_Int ha' hc') (intMul_mem_intPositive hb' hd')).mpr ?_
  calc intMul (intMul a c) (intMul b' d')
      = intMul (intMul a b') (intMul c d') := intMul_mul_comm ha hc hb'I hd'I
    _ = intMul (intMul a' b) (intMul c' d) := by rw [h₁, h₂]
    _ = intMul (intMul a' c') (intMul b d) := intMul_mul_comm ha' hbI hc' hdI

theorem ratMul_ratOf {a b c d : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ratMul (ratOf a b) (ratOf c d) = ratOf (intMul a c) (intMul b d) := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', c', d', h₁, h₂, hmem⟩
    obtain ⟨_, ha', _, hb', he₁, r₁⟩ := (mem_ratOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    obtain ⟨_, hc', _, hd', he₂, r₂⟩ := (mem_ratOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective he₂
    rwa [← ratOf_mul_congr ha hb hc hd ha' hb' hc' hd' r₁ r₂] at hmem
  · intro hmem
    exact ⟨ratOf_subset _ _ p hmem, a, b, c, d,
      mem_cls_self ratRel_isEquivRel (opair_mem_prod ha hb),
      mem_cls_self ratRel_isEquivRel (opair_mem_prod hc hd), hmem⟩

theorem ratMul_mem_Rat {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratMul r s ∈ Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  rw [ratMul_ratOf ha hb hc hd]
  exact ratOf_mem_Rat (intMul_mem_Int ha hc) (intMul_mem_intPositive hb hd)

theorem ratMul_comm {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratMul r s = ratMul s r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  rw [ratMul_ratOf ha hb hc hd, ratMul_ratOf hc hd ha hb, intMul_comm ha hc,
      intMul_comm (intPositive_subset _ hb) (intPositive_subset _ hd)]

theorem ratMul_assoc {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) : ratMul (ratMul r s) t = ratMul r (ratMul s t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  rw [ratMul_ratOf ha hb hc hd, ratMul_ratOf hc hd he hf,
      ratMul_ratOf (intMul_mem_Int ha hc) (intMul_mem_intPositive hb hd) he hf,
      ratMul_ratOf ha hb (intMul_mem_Int hc he) (intMul_mem_intPositive hd hf),
      intMul_assoc ha hc he,
      intMul_assoc (intPositive_subset _ hb) (intPositive_subset _ hd)
        (intPositive_subset _ hf)]

/-- Cancelling a common positive factor, which keeps the distributive law
from turning into a six-factor rearrangement. -/
theorem ratOf_cancel {k a b : ZFSet.{u}} (hk : k ∈ intPositive.{u}) (ha : a ∈ Int.{u})
    (hb : b ∈ intPositive.{u}) :
    ratOf (intMul k a) (intMul k b) = ratOf a b := by
  have hkI := intPositive_subset _ hk
  have hbI := intPositive_subset _ hb
  refine (ratOf_eq_ratOf_iff (intMul_mem_Int hkI ha) (intMul_mem_intPositive hk hb)
    ha hb).mpr ?_
  rw [intMul_assoc hkI ha hbI, intMul_comm ha (intMul_mem_Int hkI hbI),
      intMul_assoc hkI hbI ha, intMul_comm hbI ha]

/-- Zero. -/
def ratZero : ZFSet.{u} := ratOf intZero.{u} intOne.{u}

theorem ratZero_mem_Rat : ratZero.{u} ∈ Rat.{u} :=
  ratOf_mem_Rat intZero_mem_Int one_mem_intPositive

@[simp] theorem ratAdd_zero {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratAdd r ratZero.{u} = r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  rw [ratZero, ratAdd_ratOf ha hb intZero_mem_Int one_mem_intPositive,
      intMul_one ha, intZero_mul hbI, intAdd_zero ha, intMul_one hbI]

theorem ratAdd_neg {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratAdd r (ratNeg r) = ratZero.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  have hbb := intMul_mem_intPositive hb hb
  rw [ratNeg_ratOf ha hb, ratAdd_ratOf ha hb (intNeg_mem_Int ha) hb,
      ← intAdd_mul ha (intNeg_mem_Int ha) hbI, intAdd_neg ha, intZero_mul hbI, ratZero]
  refine (ratOf_eq_ratOf_iff intZero_mem_Int hbb intZero_mem_Int one_mem_intPositive).mpr ?_
  rw [intZero_mul (intPositive_subset _ one_mem_intPositive), intZero_mul (intPositive_subset _ hbb)]

/-- One. -/
def ratOne : ZFSet.{u} := ratOf intOne.{u} intOne.{u}

theorem ratOne_mem_Rat : ratOne.{u} ∈ Rat.{u} :=
  ratOf_mem_Rat intOne_mem_Int one_mem_intPositive

@[simp] theorem ratMul_one {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratMul r ratOne.{u} = r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  rw [ratOne, ratMul_ratOf ha hb intOne_mem_Int one_mem_intPositive, intMul_one ha,
      intMul_one (intPositive_subset _ hb)]

theorem ratMul_add {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) :
    ratMul r (ratAdd s t) = ratAdd (ratMul r s) (ratMul r t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hfI := intPositive_subset _ hf
  -- both products pick up a factor of `b` that `ratOf_cancel` then removes
  have n : ∀ {x y : ZFSet.{u}}, x ∈ Int.{u} → y ∈ intPositive.{u} →
      intMul (intMul a x) (intMul b y) = intMul b (intMul a (intMul x y)) := by
    intro x y hx hy
    have hyI := intPositive_subset _ hy
    rw [intMul_mul_comm ha hx hbI hyI, intMul_comm ha hbI, intMul_assoc hbI ha
      (intMul_mem_Int hx hyI)]
  rw [ratAdd_ratOf hc hd he hf, ratMul_ratOf ha hb hc hd, ratMul_ratOf ha hb he hf,
      ratMul_ratOf ha hb (intAdd_mem_Int (intMul_mem_Int hc hfI) (intMul_mem_Int he hdI))
        (intMul_mem_intPositive hd hf),
      ratAdd_ratOf (intMul_mem_Int ha hc) (intMul_mem_intPositive hb hd)
        (intMul_mem_Int ha he) (intMul_mem_intPositive hb hf),
      n hc hf, n he hd,
      ← intMul_add hbI (intMul_mem_Int ha (intMul_mem_Int hc hfI))
        (intMul_mem_Int ha (intMul_mem_Int he hdI)),
      ← intMul_add ha (intMul_mem_Int hc hfI) (intMul_mem_Int he hdI),
      intMul_mul_comm hbI hdI hbI hfI, intMul_assoc hbI hbI (intMul_mem_Int hdI hfI),
      ratOf_cancel hb (intMul_mem_Int ha (intAdd_mem_Int (intMul_mem_Int hc hfI)
        (intMul_mem_Int he hdI))) (intMul_mem_intPositive hb (intMul_mem_intPositive hd hf))]

theorem ratAdd_mul {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) :
    ratMul (ratAdd r s) t = ratAdd (ratMul r t) (ratMul s t) := by
  rw [ratMul_comm (ratAdd_mem_Rat hr hs) ht, ratMul_add ht hr hs, ratMul_comm ht hr,
      ratMul_comm ht hs]

/-! ### The inverse

`ratInv` is the one operation whose class cannot be named by an expression in
the representatives: `(a/b)⁻¹` is `b/a` only when `a` is positive, and the
denominator has to stay positive. Stating the relation `a·x = b·y` instead
sidesteps the split at the definition, and `ratMul_inv` pays it once, where the
constructive trichotomy `intPositive_or_neg` supplies the two cases. -/

def ratInv (r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b, opair a b ∈ r ∧ ∃ x y, p = opair x y ∧ intMul a x = intMul b y)
    ratPairs.{u}

theorem ratInv_ratOf {a b x y : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hx : x ∈ Int.{u}) (hy : y ∈ intPositive.{u}) (ha0 : a ≠ intZero.{u})
    (h : intMul a x = intMul b y) : ratInv (ratOf a b) = ratOf x y := by
  have hbI := intPositive_subset _ hb
  have hyI := intPositive_subset _ hy
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨hp, a', b', h₁, x', y', rfl, E⟩
    -- `x'` and `y'` are known to be an integer and a positive one only because
    -- the pair was separated out of `ratPairs`
    have hx' := mem_prod_left hp
    have hy' := mem_prod_right hp
    have hy'I := intPositive_subset _ hy'
    obtain ⟨_, ha', _, hb', he₁, r₁⟩ := (mem_ratOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    have hb'I := intPositive_subset _ hb'
    refine (mem_ratOf_iff hx hy _).mpr ⟨x', hx', y', hy', rfl, ?_⟩
    refine intMul_left_cancel (intMul_mem_Int ha hb'I) (intMul_mem_Int hx hy'I)
      (intMul_mem_Int hx' hyI) (intMul_ne_zero ha hb'I ha0 (intPositive_ne_zero hb')) ?_
    calc intMul (intMul a b') (intMul x y')
        = intMul (intMul a x) (intMul b' y') := intMul_mul_comm ha hb'I hx hy'I
      _ = intMul (intMul b y) (intMul a' x') := by rw [h, E]
      _ = intMul (intMul a' x') (intMul b y) :=
            intMul_comm (intMul_mem_Int hbI hyI) (intMul_mem_Int ha' hx')
      _ = intMul (intMul a' b) (intMul x' y) := intMul_mul_comm ha' hx' hbI hyI
      _ = intMul (intMul a b') (intMul x' y) := by rw [r₁]
  · intro hmem
    obtain ⟨x'', hx'', y'', hy'', rfl, rel⟩ := (mem_ratOf_iff hx hy _).mp hmem
    have hy''I := intPositive_subset _ hy''
    refine ⟨opair_mem_prod hx'' hy'', a, b,
      mem_cls_self ratRel_isEquivRel (opair_mem_prod ha hb), x'', y'', rfl, ?_⟩
    refine intMul_left_cancel hyI (intMul_mem_Int ha hx'') (intMul_mem_Int hbI hy''I)
      (intPositive_ne_zero hy) ?_
    calc intMul y (intMul a x'')
        = intMul (intMul a x'') y := intMul_comm hyI (intMul_mem_Int ha hx'')
      _ = intMul a (intMul x'' y) := intMul_assoc ha hx'' hyI
      _ = intMul a (intMul x y'') := by rw [rel]
      _ = intMul (intMul a x) y'' := (intMul_assoc ha hx hy''I).symm
      _ = intMul (intMul b y) y'' := by rw [h]
      _ = intMul b (intMul y y'') := intMul_assoc hbI hyI hy''I
      _ = intMul b (intMul y'' y) := by rw [intMul_comm hyI hy''I]
      _ = intMul (intMul b y'') y := (intMul_assoc hbI hy''I hyI).symm
      _ = intMul y (intMul b y'') := intMul_comm (intMul_mem_Int hbI hy''I) hyI

theorem num_ne_zero {a b : ZFSet.{u}} (hb : b ∈ intPositive.{u})
    (h : ratOf a b ≠ ratZero.{u}) : a ≠ intZero.{u} := by
  intro he
  refine h ?_
  rw [he, ratZero]
  refine (ratOf_eq_ratOf_iff intZero_mem_Int hb intZero_mem_Int one_mem_intPositive).mpr ?_
  rw [intZero_mul (intPositive_subset _ hb), intZero_mul intOne_mem_Int]

/-- Every nonzero rational has an inverse. The sign of the numerator decides
which representative names it, and `intPositive_or_neg` supplies that split
without excluded middle. -/
theorem ratMul_inv {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) (h0 : r ≠ ratZero.{u}) :
    ratMul r (ratInv r) = ratOne.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  have ha0 := num_ne_zero hb h0
  rcases intPositive_or_neg ha ha0 with hpos | hneg
  · rw [ratInv_ratOf ha hb hbI hpos ha0 (intMul_comm ha hbI),
        ratMul_ratOf ha hb hbI hpos, ratOne]
    refine (ratOf_eq_ratOf_iff (intMul_mem_Int ha hbI) (intMul_mem_intPositive hb hpos)
      intOne_mem_Int one_mem_intPositive).mpr ?_
    rw [intMul_one (intMul_mem_Int ha hbI), intOne_mul (intMul_mem_Int hbI ha),
        intMul_comm hbI ha]
  · have hnb := intNeg_mem_Int hbI
    have hna := intNeg_mem_Int ha
    have key : intMul a (intNeg b) = intMul b (intNeg a) := by
      rw [intMul_neg ha hbI, intMul_neg hbI ha, intMul_comm ha hbI]
    rw [ratInv_ratOf ha hb hnb hneg ha0 key, ratMul_ratOf ha hb hnb hneg, ratOne]
    refine (ratOf_eq_ratOf_iff (intMul_mem_Int ha hnb) (intMul_mem_intPositive hb hneg)
      intOne_mem_Int one_mem_intPositive).mpr ?_
    rw [intMul_one (intMul_mem_Int ha hnb), intOne_mul (intMul_mem_Int hbI hna), key]

theorem ratInv_mem_Rat {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) (h0 : r ≠ ratZero.{u}) :
    ratInv r ∈ Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  have ha0 := num_ne_zero hb h0
  rcases intPositive_or_neg ha ha0 with hpos | hneg
  · rw [ratInv_ratOf ha hb hbI hpos ha0 (intMul_comm ha hbI)]
    exact ratOf_mem_Rat hbI hpos
  · have key : intMul a (intNeg b) = intMul b (intNeg a) := by
      rw [intMul_neg ha hbI, intMul_neg hbI ha, intMul_comm ha hbI]
    rw [ratInv_ratOf ha hb (intNeg_mem_Int hbI) hneg ha0 key]
    exact ratOf_mem_Rat (intNeg_mem_Int hbI) hneg

/-! ## Order

`a/b ≤ c/d` is `a·d ≤ c·b`, with no sign condition to check because both
denominators are positive. Well-definedness is `intMul_le_mul_right_iff` used
twice: once to multiply the hypothesis up by `b'·d'`, once to divide the goal
down by `b·d`. -/

/-- One direction of well-definedness; the `↔` in `ratLe_ratOf` is this applied
to each side. -/
private theorem ratLe_wd {a b c d a' b' c' d' : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u})
    (ha' : a' ∈ Int.{u}) (hb' : b' ∈ intPositive.{u})
    (hc' : c' ∈ Int.{u}) (hd' : d' ∈ intPositive.{u})
    (h₁ : intMul a b' = intMul a' b) (h₂ : intMul c d' = intMul c' d)
    (H : intLe (intMul a d) (intMul c b)) :
    intLe (intMul a' d') (intMul c' b') := by
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hb'I := intPositive_subset _ hb'
  have hd'I := intPositive_subset _ hd'
  refine (intMul_le_mul_right_iff (intMul_mem_Int ha' hd'I) (intMul_mem_Int hc' hb'I)
    (intMul_mem_intPositive hb hd)).mp ?_
  have key := (intMul_le_mul_right_iff (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI)
    (intMul_mem_intPositive hb' hd')).mpr H
  have e₁ : intMul (intMul a' d') (intMul b d)
      = intMul (intMul a d) (intMul b' d') :=
    calc intMul (intMul a' d') (intMul b d)
        = intMul (intMul a' b) (intMul d' d) := intMul_mul_comm ha' hd'I hbI hdI
      _ = intMul (intMul a b') (intMul d' d) := by rw [h₁]
      _ = intMul (intMul a b') (intMul d d') := by rw [intMul_comm hd'I hdI]
      _ = intMul (intMul a d) (intMul b' d') := intMul_mul_comm ha hb'I hdI hd'I
  have e₂ : intMul (intMul c' b') (intMul b d)
      = intMul (intMul c b) (intMul b' d') :=
    calc intMul (intMul c' b') (intMul b d)
        = intMul (intMul c' b') (intMul d b) := by rw [intMul_comm hbI hdI]
      _ = intMul (intMul c' d) (intMul b' b) := intMul_mul_comm hc' hb'I hdI hbI
      _ = intMul (intMul c d') (intMul b' b) := by rw [h₂]
      _ = intMul (intMul c d') (intMul b b') := by rw [intMul_comm hb'I hbI]
      _ = intMul (intMul c b) (intMul d' b') := intMul_mul_comm hc hd'I hbI hb'I
      _ = intMul (intMul c b) (intMul b' d') := by rw [intMul_comm hd'I hb'I]
  rw [e₁, e₂]
  exact key

/-- `r ≤ s` on ℚ. Stated over some pair of representatives; `ratLe_ratOf`
shows any pair decides it. -/
def ratLe (r s : ZFSet.{u}) : Prop :=
  ∃ a b c d, a ∈ Int.{u} ∧ b ∈ intPositive.{u} ∧ c ∈ Int.{u} ∧ d ∈ intPositive.{u} ∧
    r = ratOf a b ∧ s = ratOf c d ∧ intLe (intMul a d) (intMul c b)

theorem ratLe_ratOf {a b c d : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ratLe (ratOf a b) (ratOf c d) ↔ intLe (intMul a d) (intMul c b) := by
  refine ⟨?_, fun h => ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, h⟩⟩
  rintro ⟨a', b', c', d', ha', hb', hc', hd', e₁, e₂, h⟩
  exact ratLe_wd ha' hb' hc' hd' ha hb hc hd
    ((ratOf_eq_ratOf_iff ha' hb' ha hb).mp e₁.symm)
    ((ratOf_eq_ratOf_iff hc' hd' hc hd).mp e₂.symm) h

theorem ratLe_refl {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) : ratLe r r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  exact (ratLe_ratOf ha hb ha hb).mpr (intLe_refl (intMul_mem_Int ha (intPositive_subset _ hb)))

theorem ratLe_antisymm {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (h₁ : ratLe r s) (h₂ : ratLe s r) : r = s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  exact (ratOf_eq_ratOf_iff ha hb hc hd).mpr
    (intLe_antisymm (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI)
      ((ratLe_ratOf ha hb hc hd).mp h₁) ((ratLe_ratOf hc hd ha hb).mp h₂))

theorem ratLe_total {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratLe r s ∨ ratLe s r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  rcases intLe_total (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI) with h | h
  · exact Or.inl ((ratLe_ratOf ha hb hc hd).mpr h)
  · exact Or.inr ((ratLe_ratOf hc hd ha hb).mpr h)

/-- Transitivity is the step that cancels the denominators: the two
hypotheses are multiplied up to a common denominator `b·d·f` and `intLe_trans`
closes the chain, after which `d` divides back out. -/
theorem ratLe_trans {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) (h₁ : ratLe r s) (h₂ : ratLe s t) : ratLe r t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hfI := intPositive_subset _ hf
  have k₁ := (ratLe_ratOf ha hb hc hd).mp h₁
  have k₂ := (ratLe_ratOf hc hd he hf).mp h₂
  refine (ratLe_ratOf ha hb he hf).mpr ?_
  refine (intMul_le_mul_right_iff (intMul_mem_Int ha hfI) (intMul_mem_Int he hbI) hd).mp ?_
  have m₁ := (intMul_le_mul_right_iff (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI) hf).mpr k₁
  have m₂ := (intMul_le_mul_right_iff (intMul_mem_Int hc hfI) (intMul_mem_Int he hdI) hb).mpr k₂
  have e₁ : intMul (intMul a f) d = intMul (intMul a d) f := by
    rw [intMul_assoc ha hfI hdI, intMul_comm hfI hdI, ← intMul_assoc ha hdI hfI]
  have e₂ : intMul (intMul c b) f = intMul (intMul c f) b := by
    rw [intMul_assoc hc hbI hfI, intMul_comm hbI hfI, ← intMul_assoc hc hfI hbI]
  have e₃ : intMul (intMul e b) d = intMul (intMul e d) b := by
    rw [intMul_assoc he hbI hdI, intMul_comm hbI hdI, ← intMul_assoc he hdI hbI]
  rw [e₁, e₃]
  exact intLe_trans (intMul_mem_Int (intMul_mem_Int ha hdI) hfI)
    (intMul_mem_Int (intMul_mem_Int hc hbI) hfI)
    (intMul_mem_Int (intMul_mem_Int he hdI) hbI) m₁ (e₂ ▸ m₂)

/-! ## Strict order, density, no endpoints

ℚ is a dense linear order without endpoints -- the order type that characterises
it, and the setting the Dedekind cuts of the next construction live in.

Density is the mediant `(a+c)/(b+d)`, not the midpoint: it needs no division,
and both comparisons collapse to the hypothesis after one distribution and one
additive cancellation. Endpoint-freeness moves by `±1` at the same denominator,
where the shift is `b·b`, positive because `b` is. -/

def ratLt (r s : ZFSet.{u}) : Prop := ratLe r s ∧ r ≠ s

theorem ratLt_ratOf {a b c d : ZFSet.{u}}
    (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (hc : c ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ratLt (ratOf a b) (ratOf c d)
      ↔ intLe (intMul a d) (intMul c b) ∧ intMul a d ≠ intMul c b := by
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨(ratLe_ratOf ha hb hc hd).mp h,
      fun he => hne ((ratOf_eq_ratOf_iff ha hb hc hd).mpr he)⟩
  · rintro ⟨h, hne⟩
    exact ⟨(ratLe_ratOf ha hb hc hd).mpr h,
      fun he => hne ((ratOf_eq_ratOf_iff ha hb hc hd).mp he)⟩

theorem ratLt_irrefl {r : ZFSet.{u}} : ¬ ratLt r r := fun h => h.right rfl

/-- A positive rational is nonzero.

`ratLt_irrefl` needs no membership hypothesis, so neither does this. Written
inline as `ratNe_zero_of_pos h` at 113 sites across 16 files, about
half of them as an unnamed argument to `ratInv_mem_Rat`, where the `≠ ratZero`
conclusion is demanded by the callee and never appears in the text. -/
theorem ratNe_zero_of_pos {r : ZFSet.{u}} (h : ratLt ratZero.{u} r) :
    r ≠ ratZero.{u} :=
  fun he => ratLt_irrefl (he ▸ h)

/-- A negative rational is nonzero.

The mirror of `ratNe_zero_of_pos`. `he ▸ h` reaches `ratLt ratZero ratZero`
from either direction, so both are one `ratLt_irrefl` away; they need separate
statements only because the hypothesis types differ. -/
theorem ratNe_zero_of_neg {r : ZFSet.{u}} (h : ratLt r ratZero.{u}) :
    r ≠ ratZero.{u} :=
  fun he => ratLt_irrefl (he ▸ h)

theorem ratLt_trans {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) (h₁ : ratLt r s) (h₂ : ratLt s t) : ratLt r t :=
  ⟨ratLe_trans hr hs ht h₁.left h₂.left, fun he =>
    h₂.right (ratLe_antisymm hs ht h₂.left (he ▸ h₁.left))⟩

/-- Density, by the mediant. -/
theorem rat_dense {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (h : ratLt r s) : ∃ t, t ∈ Rat.{u} ∧ ratLt r t ∧ ratLt t s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  obtain ⟨hle, hne⟩ := (ratLt_ratOf ha hb hc hd).mp h
  have hbd : intAdd b d ∈ intPositive.{u} := intAdd_mem_intPositive hb hd
  have hac : intAdd a c ∈ Int.{u} := intAdd_mem_Int ha hc
  refine ⟨ratOf (intAdd a c) (intAdd b d), ratOf_mem_Rat hac hbd, ?_, ?_⟩
  · refine (ratLt_ratOf ha hb hac hbd).mpr ?_
    rw [intMul_add ha hbI hdI, intAdd_mul ha hc hbI]
    exact ⟨(intAdd_le_add_left_iff (intMul_mem_Int ha hbI) (intMul_mem_Int ha hdI)
        (intMul_mem_Int hc hbI)).mpr hle,
      fun he => hne (intAdd_left_cancel (intMul_mem_Int ha hbI)
        (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI) he)⟩
  · refine (ratLt_ratOf hac hbd hc hd).mpr ?_
    rw [intAdd_mul ha hc hdI, intMul_add hc hbI hdI]
    exact ⟨(intAdd_le_add_right_iff (intMul_mem_Int hc hdI) (intMul_mem_Int ha hdI)
        (intMul_mem_Int hc hbI)).mpr hle,
      fun he => hne (intAdd_right_cancel (intMul_mem_Int hc hdI)
        (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI) he)⟩

theorem rat_no_greatest {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLt r s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  have hab := intAdd_mem_Int ha hbI
  have hbb : intMul b b ∈ intPositive.{u} := intMul_mem_intPositive hb hb
  have hbbI := intPositive_subset _ hbb
  have hprod := intMul_mem_Int ha hbI
  refine ⟨ratOf (intAdd a b) b, ratOf_mem_Rat hab hb, ?_⟩
  refine (ratLt_ratOf ha hb hab hb).mpr ?_
  rw [intAdd_mul ha hbI hbI]
  constructor
  · have h := (intAdd_le_add_left_iff hprod intZero_mem_Int hbbI).mpr
      (intZero_le_of_intPositive hbb)
    rwa [intAdd_zero hprod] at h
  · intro he
    refine intPositive_ne_zero hbb (intAdd_left_cancel hprod hbbI intZero_mem_Int ?_)
    rw [intAdd_zero hprod]
    exact he.symm

theorem rat_no_least {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLt s r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  have hnb := intNeg_mem_Int hbI
  have hab := intAdd_mem_Int ha hnb
  have hbb : intMul b b ∈ intPositive.{u} := intMul_mem_intPositive hb hb
  have hbbI := intPositive_subset _ hbb
  have hprod := intMul_mem_Int ha hbI
  refine ⟨ratOf (intAdd a (intNeg b)) b, ratOf_mem_Rat hab hb, ?_⟩
  refine (ratLt_ratOf hab hb ha hb).mpr ?_
  rw [intAdd_mul ha hnb hbI, intNeg_mul hbI hbI]
  constructor
  · have h := (intAdd_le_add_left_iff hprod (intNeg_mem_Int hbbI) intZero_mem_Int).mpr
      ((intLe_neg_zero_iff hbbI).mpr (intZero_le_of_intPositive hbb))
    rwa [intAdd_zero hprod] at h
  · intro he
    refine intPositive_ne_zero hbb ((intNeg_eq_zero_iff hbbI).mp ?_)
    refine intAdd_left_cancel hprod (intNeg_mem_Int hbbI) intZero_mem_Int ?_
    rw [intAdd_zero hprod]
    exact he

/-! ### The order is compatible with the arithmetic

The two laws that make ℚ an ordered field: translation preserves and reflects
`≤`, and multiplication by a non-negative rational preserves it. Both reduce to
ℤ once the common denominator `f·f` is factored out. -/

theorem ratAdd_le_add_left_iff {t r s : ZFSet.{u}} (ht : t ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) : ratLe (ratAdd t r) (ratAdd t s) ↔ ratLe r s := by
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hfI := intPositive_subset _ hf
  have x₁ : intMul (intMul e b) (intMul f d) = intMul (intMul e f) (intMul b d) :=
    intMul_mul_comm he hbI hfI hdI
  have x₂ : intMul (intMul e d) (intMul f b) = intMul (intMul e f) (intMul b d) := by
    rw [intMul_mul_comm he hdI hfI hbI, intMul_comm hdI hbI]
  have y₁ : intMul (intMul a f) (intMul f d) = intMul (intMul a d) (intMul f f) := by
    rw [intMul_comm hfI hdI, intMul_mul_comm ha hfI hdI hfI]
  have y₂ : intMul (intMul c f) (intMul f b) = intMul (intMul c b) (intMul f f) := by
    rw [intMul_comm hfI hbI, intMul_mul_comm hc hfI hbI hfI]
  rw [ratAdd_ratOf he hf ha hb, ratAdd_ratOf he hf hc hd,
      ratLe_ratOf (intAdd_mem_Int (intMul_mem_Int he hbI) (intMul_mem_Int ha hfI))
        (intMul_mem_intPositive hf hb)
        (intAdd_mem_Int (intMul_mem_Int he hdI) (intMul_mem_Int hc hfI))
        (intMul_mem_intPositive hf hd),
      ratLe_ratOf ha hb hc hd,
      intAdd_mul (intMul_mem_Int he hbI) (intMul_mem_Int ha hfI) (intMul_mem_Int hfI hdI),
      intAdd_mul (intMul_mem_Int he hdI) (intMul_mem_Int hc hfI) (intMul_mem_Int hfI hbI),
      x₁, x₂, y₁, y₂,
      intAdd_le_add_left_iff
        (intMul_mem_Int (intMul_mem_Int he hfI) (intMul_mem_Int hbI hdI))
        (intMul_mem_Int (intMul_mem_Int ha hdI) (intMul_mem_Int hfI hfI))
        (intMul_mem_Int (intMul_mem_Int hc hbI) (intMul_mem_Int hfI hfI)),
      intMul_le_mul_right_iff (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI)
        (intMul_mem_intPositive hf hf)]

theorem ratMul_le_mul_right {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) (h : ratLe r s) (h0 : ratLe ratZero.{u} t) :
    ratLe (ratMul r t) (ratMul s t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Rat_iff t).mp ht
  have hbI := intPositive_subset _ hb
  have hdI := intPositive_subset _ hd
  have hfI := intPositive_subset _ hf
  rw [ratLe_ratOf ha hb hc hd] at h
  rw [ratZero, ratLe_ratOf intZero_mem_Int one_mem_intPositive he hf,
      intZero_mul hfI, intMul_one he] at h0
  have hef : intLe intZero.{u} (intMul e f) := by
    have hm := intMul_le_mul_right intZero_mem_Int he hfI
      (intZero_le_of_intPositive hf) h0
    rwa [intZero_mul hfI] at hm
  rw [ratMul_ratOf ha hb he hf, ratMul_ratOf hc hd he hf,
      ratLe_ratOf (intMul_mem_Int ha he) (intMul_mem_intPositive hb hf)
        (intMul_mem_Int hc he) (intMul_mem_intPositive hd hf),
      intMul_mul_comm ha he hdI hfI, intMul_mul_comm hc he hbI hfI]
  exact intMul_le_mul_right (intMul_mem_Int ha hdI) (intMul_mem_Int hc hbI)
    (intMul_mem_Int he hfI) hef h

@[simp] theorem ratMul_zero {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratMul r ratZero.{u} = ratZero.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI := intPositive_subset _ hb
  rw [ratZero, ratMul_ratOf ha hb intZero_mem_Int one_mem_intPositive,
      intMul_zero ha, intMul_one hbI]
  refine (ratOf_eq_ratOf_iff intZero_mem_Int hb intZero_mem_Int one_mem_intPositive).mpr ?_
  rw [intZero_mul intOne_mem_Int, intZero_mul hbI]

theorem ratZero_mul {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratMul ratZero.{u} r = ratZero.{u} := by
  rw [ratMul_comm ratZero_mem_Rat hr, ratMul_zero hr]

theorem ratOne_mul {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) : ratMul ratOne.{u} r = r := by
  rw [ratMul_comm ratOne_mem_Rat hr, ratMul_one hr]

theorem ratMul_left_cancel {t r s : ZFSet.{u}} (ht : t ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) (ht0 : t ≠ ratZero.{u}) (h : ratMul t r = ratMul t s) : r = s := by
  have hit := ratInv_mem_Rat ht ht0
  have key : ∀ {v : ZFSet.{u}}, v ∈ Rat.{u} → ratMul (ratInv t) (ratMul t v) = v := by
    intro v hv
    rw [← ratMul_assoc hit ht hv, ratMul_comm hit ht, ratMul_inv ht ht0, ratOne_mul hv]
  rw [← key hr, h, key hs]

theorem ratMul_lt_mul_right {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u})
    (ht : t ∈ Rat.{u}) (ht0 : t ≠ ratZero.{u}) (h0 : ratLe ratZero.{u} t)
    (h : ratLt r s) : ratLt (ratMul r t) (ratMul s t) :=
  ⟨ratMul_le_mul_right hr hs ht h.left h0, fun he => h.right
    (ratMul_left_cancel ht hr hs ht0
      (by rw [ratMul_comm ht hr, ratMul_comm ht hs]; exact he))⟩

theorem ratZero_add {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) : ratAdd ratZero.{u} r = r := by
  rw [ratAdd_comm ratZero_mem_Rat hr, ratAdd_zero hr]

theorem ratAdd_left_cancel {t r s : ZFSet.{u}} (ht : t ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) (h : ratAdd t r = ratAdd t s) : r = s := by
  have hnt := ratNeg_mem_Rat ht
  have key : ∀ {v : ZFSet.{u}}, v ∈ Rat.{u} → ratAdd (ratNeg t) (ratAdd t v) = v := by
    intro v hv
    rw [← ratAdd_assoc hnt ht hv, ratAdd_comm hnt ht, ratAdd_neg ht, ratZero_add hv]
  rw [← key hr, h, key hs]

/-- `q + (p - q) = p`: the step that turns "`p'` is below `p`" into a summand
below a given one, which is what downward closure of a sum of cuts needs. -/
theorem ratAdd_sub_cancel {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u}) :
    ratAdd q (ratAdd p (ratNeg q)) = p := by
  rw [ratAdd_comm hp (ratNeg_mem_Rat hq), ← ratAdd_assoc hq (ratNeg_mem_Rat hq) hp,
      ratAdd_neg hq, ratZero_add hp]

theorem ratAdd_lt_add_left_iff {t r s : ZFSet.{u}} (ht : t ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) : ratLt (ratAdd t r) (ratAdd t s) ↔ ratLt r s := by
  constructor
  · rintro ⟨hle, hne⟩
    exact ⟨(ratAdd_le_add_left_iff ht hr hs).mp hle, fun he => hne (by rw [he])⟩
  · rintro ⟨hle, hne⟩
    exact ⟨(ratAdd_le_add_left_iff ht hr hs).mpr hle,
      fun he => hne (ratAdd_left_cancel ht hr hs he)⟩

theorem ratAdd_lt_add {q q' r r' : ZFSet.{u}} (hq : q ∈ Rat.{u}) (hq' : q' ∈ Rat.{u})
    (hr : r ∈ Rat.{u}) (hr' : r' ∈ Rat.{u}) (h₁ : ratLt q q') (h₂ : ratLt r r') :
    ratLt (ratAdd q r) (ratAdd q' r') := by
  have s₁ : ratLt (ratAdd q r) (ratAdd q r') := (ratAdd_lt_add_left_iff hq hr hr').mpr h₂
  have s₂ : ratLt (ratAdd q r') (ratAdd q' r') := by
    rw [ratAdd_comm hq hr', ratAdd_comm hq' hr']
    exact (ratAdd_lt_add_left_iff hr' hq hq').mpr h₁
  exact ratLt_trans (ratAdd_mem_Rat hq hr) (ratAdd_mem_Rat hq hr')
    (ratAdd_mem_Rat hq' hr') s₁ s₂

@[simp] theorem ratNeg_zero : ratNeg ratZero.{u} = ratZero.{u} := by
  rw [ratZero, ratNeg_ratOf intZero_mem_Int one_mem_intPositive, intNeg_zero]

theorem ratNeg_injective {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (h : ratNeg a = ratNeg b) : a = b := by
  have hna := ratNeg_mem_Rat ha
  have h₁ : ratAdd (ratNeg a) a = ratZero.{u} := by
    rw [ratAdd_comm hna ha, ratAdd_neg ha]
  have h₂ : ratAdd (ratNeg a) b = ratZero.{u} := by
    rw [h, ratAdd_comm (ratNeg_mem_Rat hb) hb, ratAdd_neg hb]
  exact ratAdd_left_cancel hna ha hb (h₁.trans h₂.symm)

/-- Negation reverses the order: translation by `a + b` turns each side into the
other. -/
theorem ratNeg_le_neg_iff {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ratLe (ratNeg a) (ratNeg b) ↔ ratLe b a := by
  have hna := ratNeg_mem_Rat ha
  have hnb := ratNeg_mem_Rat hb
  have hab := ratAdd_mem_Rat ha hb
  have e₁ : ratAdd (ratAdd a b) (ratNeg a) = b := by
    rw [ratAdd_comm ha hb, ratAdd_assoc hb ha hna, ratAdd_neg ha, ratAdd_zero hb]
  have e₂ : ratAdd (ratAdd a b) (ratNeg b) = a := by
    rw [ratAdd_assoc ha hb hnb, ratAdd_neg hb, ratAdd_zero ha]
  rw [← ratAdd_le_add_left_iff hab hna hnb, e₁, e₂]

theorem ratNeg_lt_neg_iff {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ratLt (ratNeg a) (ratNeg b) ↔ ratLt b a := by
  constructor
  · rintro ⟨hle, hne⟩
    exact ⟨(ratNeg_le_neg_iff ha hb).mp hle, fun he => hne (by rw [he])⟩
  · rintro ⟨hle, hne⟩
    exact ⟨(ratNeg_le_neg_iff ha hb).mpr hle,
      fun he => hne (ratNeg_injective ha hb he).symm⟩

theorem ratAdd_le_add_right_iff {k r s : ZFSet.{u}} (hk : k ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) : ratLe (ratAdd r k) (ratAdd s k) ↔ ratLe r s := by
  rw [ratAdd_comm hr hk, ratAdd_comm hs hk]
  exact ratAdd_le_add_left_iff hk hr hs

theorem ratLt_of_lt_of_le {a b c : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hc : c ∈ Rat.{u}) (h₁ : ratLt a b) (h₂ : ratLe b c) : ratLt a c :=
  ⟨ratLe_trans ha hb hc h₁.left h₂,
   fun he => h₁.right (ratLe_antisymm ha hb h₁.left (he ▸ h₂))⟩

theorem ratAdd_lt_add_right_iff {k r s : ZFSet.{u}} (hk : k ∈ Rat.{u}) (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) : ratLt (ratAdd r k) (ratAdd s k) ↔ ratLt r s := by
  rw [ratAdd_comm hr hk, ratAdd_comm hs hk]
  exact ratAdd_lt_add_left_iff hk hr hs

theorem ratLt_of_le_of_lt {a b c : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hc : c ∈ Rat.{u}) (h₁ : ratLe a b) (h₂ : ratLt b c) : ratLt a c :=
  ⟨ratLe_trans ha hb hc h₁ h₂.left,
   fun he => h₂.right (ratLe_antisymm hb hc h₂.left (he ▸ h₁))⟩

theorem ratMul_neg {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratMul r (ratNeg s) = ratNeg (ratMul r s) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  rw [ratNeg_ratOf hc hd, ratMul_ratOf ha hb (intNeg_mem_Int hc) hd,
      ratMul_ratOf ha hb hc hd, ratNeg_ratOf (intMul_mem_Int ha hc)
        (intMul_mem_intPositive hb hd), intMul_neg ha hc]

/-- Multiplying by a non-positive rational reverses `≤`. -/
@[simp] theorem ratNeg_ratNeg {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratNeg (ratNeg r) = r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  rw [ratNeg_ratOf ha hb, ratNeg_ratOf (intNeg_mem_Int ha) hb, intNeg_intNeg ha]

theorem ratMul_le_mul_right_of_nonpos {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) (ht : t ∈ Rat.{u}) (h : ratLe r s)
    (h0 : ratLe t ratZero.{u}) : ratLe (ratMul s t) (ratMul r t) := by
  have hnt := ratNeg_mem_Rat ht
  have h0' : ratLe ratZero.{u} (ratNeg t) := by
    have hstep := (ratNeg_le_neg_iff ratZero_mem_Rat ht).mpr h0
    rwa [ratNeg_zero] at hstep
  have hm := ratMul_le_mul_right hr hs hnt h h0'
  rw [ratMul_neg hr ht, ratMul_neg hs ht] at hm
  exact (ratNeg_le_neg_iff (ratMul_mem_Rat hr ht) (ratMul_mem_Rat hs ht)).mp hm

/-- Strict monotonicity for a non-positive multiplier, which reverses. -/
theorem ratMul_lt_mul_right_of_nonpos {r s t : ZFSet.{u}} (hr : r ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) (ht : t ∈ Rat.{u}) (ht0 : t ≠ ratZero.{u})
    (h0 : ratLe t ratZero.{u}) (h : ratLt r s) : ratLt (ratMul s t) (ratMul r t) :=
  ⟨ratMul_le_mul_right_of_nonpos hr hs ht h.left h0, fun he => h.right
    (ratMul_left_cancel ht hr hs ht0
      (by rw [ratMul_comm ht hr, ratMul_comm ht hs]; exact he.symm))⟩

/-! ### Finding a rational below or above several at once

The product of two intervals is bounded by its four corner products, and every
statement about it therefore quantifies over four rationals at a time. These
give the witnesses, by case analysis on the total order -- constructive, because
ℚ's order is decidable, and needed because there is no `min` function to reach
for: defining one would need the decision as data. -/

theorem exists_lt_two {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ∃ t, t ∈ Rat.{u} ∧ ratLt t a ∧ ratLt t b := by
  rcases ratLe_total ha hb with h | h
  · obtain ⟨t, htQ, hlt⟩ := rat_no_least ha
    exact ⟨t, htQ, hlt, ratLt_of_lt_of_le htQ ha hb hlt h⟩
  · obtain ⟨t, htQ, hlt⟩ := rat_no_least hb
    exact ⟨t, htQ, ratLt_of_lt_of_le htQ hb ha hlt h, hlt⟩

theorem exists_gt_two {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ∃ t, t ∈ Rat.{u} ∧ ratLt a t ∧ ratLt b t := by
  rcases ratLe_total ha hb with h | h
  · obtain ⟨t, htQ, hlt⟩ := rat_no_greatest hb
    exact ⟨t, htQ, ratLt_of_le_of_lt ha hb htQ h hlt, hlt⟩
  · obtain ⟨t, htQ, hlt⟩ := rat_no_greatest ha
    exact ⟨t, htQ, hlt, ratLt_of_le_of_lt hb ha htQ h hlt⟩

/-- A rational strictly between `p` and two rationals both above it. -/
theorem exists_between_two {p a b : ZFSet.{u}} (hp : p ∈ Rat.{u}) (ha : a ∈ Rat.{u})
    (hb : b ∈ Rat.{u}) (h₁ : ratLt p a) (h₂ : ratLt p b) :
    ∃ t, t ∈ Rat.{u} ∧ ratLt p t ∧ ratLt t a ∧ ratLt t b := by
  rcases ratLe_total ha hb with h | h
  · obtain ⟨t, htQ, hpt, hta⟩ := rat_dense hp ha h₁
    exact ⟨t, htQ, hpt, hta, ratLt_of_lt_of_le htQ ha hb hta h⟩
  · obtain ⟨t, htQ, hpt, htb⟩ := rat_dense hp hb h₂
    exact ⟨t, htQ, hpt, ratLt_of_lt_of_le htQ hb ha htb h, htb⟩

/-- The same, below: a rational strictly between two rationals and `p`. -/
theorem exists_between_two' {p a b : ZFSet.{u}} (hp : p ∈ Rat.{u}) (ha : a ∈ Rat.{u})
    (hb : b ∈ Rat.{u}) (h₁ : ratLt a p) (h₂ : ratLt b p) :
    ∃ t, t ∈ Rat.{u} ∧ ratLt t p ∧ ratLt a t ∧ ratLt b t := by
  rcases ratLe_total ha hb with h | h
  · obtain ⟨t, htQ, hbt, htp⟩ := rat_dense hb hp h₂
    exact ⟨t, htQ, htp, ratLt_of_le_of_lt ha hb htQ h hbt, hbt⟩
  · obtain ⟨t, htQ, hat, htp⟩ := rat_dense ha hp h₁
    exact ⟨t, htQ, htp, hat, ratLt_of_le_of_lt hb ha htQ h hat⟩

/-! ### The corner lemma

Stated as a disjunction rather than with `min`/`max`, for the same reason. -/

theorem corner_le_mul {q q' r r' Q R : ZFSet.{u}} (hq : q ∈ Rat.{u}) (hq' : q' ∈ Rat.{u})
    (hr : r ∈ Rat.{u}) (hr' : r' ∈ Rat.{u}) (hQ : Q ∈ Rat.{u}) (hR : R ∈ Rat.{u})
    (hqQ : ratLe q Q) (hQq' : ratLe Q q') (hrR : ratLe r R) (hRr' : ratLe R r') :
    ratLe (ratMul q r) (ratMul Q R) ∨ ratLe (ratMul q r') (ratMul Q R) ∨
      ratLe (ratMul q' r) (ratMul Q R) ∨ ratLe (ratMul q' r') (ratMul Q R) := by
  rcases ratLe_total ratZero_mem_Rat hR with hR0 | hR0
  · -- `R ≥ 0`, so `q·R ≤ Q·R`; then compare `q·r` or `q·r'` with `q·R`
    have h₁ : ratLe (ratMul q R) (ratMul Q R) := ratMul_le_mul_right hq hQ hR hqQ hR0
    rcases ratLe_total ratZero_mem_Rat hq with hq0 | hq0
    · refine Or.inl (ratLe_trans (ratMul_mem_Rat hq hr) (ratMul_mem_Rat hq hR)
        (ratMul_mem_Rat hQ hR) ?_ h₁)
      rw [ratMul_comm hq hr, ratMul_comm hq hR]
      exact ratMul_le_mul_right hr hR hq hrR hq0
    · refine Or.inr (Or.inl (ratLe_trans (ratMul_mem_Rat hq hr') (ratMul_mem_Rat hq hR)
        (ratMul_mem_Rat hQ hR) ?_ h₁))
      rw [ratMul_comm hq hr', ratMul_comm hq hR]
      exact ratMul_le_mul_right_of_nonpos hR hr' hq hRr' hq0
  · -- `R ≤ 0`, so `q'·R ≤ Q·R`
    have h₁ : ratLe (ratMul q' R) (ratMul Q R) :=
      ratMul_le_mul_right_of_nonpos hQ hq' hR hQq' hR0
    rcases ratLe_total ratZero_mem_Rat hq' with hq'0 | hq'0
    · refine Or.inr (Or.inr (Or.inl (ratLe_trans (ratMul_mem_Rat hq' hr)
        (ratMul_mem_Rat hq' hR) (ratMul_mem_Rat hQ hR) ?_ h₁)))
      rw [ratMul_comm hq' hr, ratMul_comm hq' hR]
      exact ratMul_le_mul_right hr hR hq' hrR hq'0
    · refine Or.inr (Or.inr (Or.inr (ratLe_trans (ratMul_mem_Rat hq' hr')
        (ratMul_mem_Rat hq' hR) (ratMul_mem_Rat hQ hR) ?_ h₁)))
      rw [ratMul_comm hq' hr', ratMul_comm hq' hR]
      exact ratMul_le_mul_right_of_nonpos hR hr' hq' hRr' hq'0

theorem mul_le_corner {q q' r r' Q R : ZFSet.{u}} (hq : q ∈ Rat.{u}) (hq' : q' ∈ Rat.{u})
    (hr : r ∈ Rat.{u}) (hr' : r' ∈ Rat.{u}) (hQ : Q ∈ Rat.{u}) (hR : R ∈ Rat.{u})
    (hqQ : ratLe q Q) (hQq' : ratLe Q q') (hrR : ratLe r R) (hRr' : ratLe R r') :
    ratLe (ratMul Q R) (ratMul q r) ∨ ratLe (ratMul Q R) (ratMul q r') ∨
      ratLe (ratMul Q R) (ratMul q' r) ∨ ratLe (ratMul Q R) (ratMul q' r') := by
  rcases ratLe_total ratZero_mem_Rat hR with hR0 | hR0
  · have h₁ : ratLe (ratMul Q R) (ratMul q' R) := ratMul_le_mul_right hQ hq' hR hQq' hR0
    rcases ratLe_total ratZero_mem_Rat hq' with hq'0 | hq'0
    · refine Or.inr (Or.inr (Or.inr (ratLe_trans (ratMul_mem_Rat hQ hR)
        (ratMul_mem_Rat hq' hR) (ratMul_mem_Rat hq' hr') h₁ ?_)))
      rw [ratMul_comm hq' hR, ratMul_comm hq' hr']
      exact ratMul_le_mul_right hR hr' hq' hRr' hq'0
    · refine Or.inr (Or.inr (Or.inl (ratLe_trans (ratMul_mem_Rat hQ hR)
        (ratMul_mem_Rat hq' hR) (ratMul_mem_Rat hq' hr) h₁ ?_)))
      rw [ratMul_comm hq' hR, ratMul_comm hq' hr]
      exact ratMul_le_mul_right_of_nonpos hr hR hq' hrR hq'0
  · have h₁ : ratLe (ratMul Q R) (ratMul q R) :=
      ratMul_le_mul_right_of_nonpos hq hQ hR hqQ hR0
    rcases ratLe_total ratZero_mem_Rat hq with hq0 | hq0
    · refine Or.inr (Or.inl (ratLe_trans (ratMul_mem_Rat hQ hR) (ratMul_mem_Rat hq hR)
        (ratMul_mem_Rat hq hr') h₁ ?_))
      rw [ratMul_comm hq hR, ratMul_comm hq hr']
      exact ratMul_le_mul_right hR hr' hq hRr' hq0
    · refine Or.inl (ratLe_trans (ratMul_mem_Rat hQ hR) (ratMul_mem_Rat hq hR)
        (ratMul_mem_Rat hq hr) h₁ ?_)
      rw [ratMul_comm hq hR, ratMul_comm hq hr]
      exact ratMul_le_mul_right_of_nonpos hr hR hq hrR hq0

/-! ### ℚ is Archimedean

The ladder is `n/b` for `n : Nat`, which needs no iterated sum: `int_lt_intOfNat_mul`
supplies the numerator directly. `1/b` is then a step small enough to sweep past
any rational in finitely many moves, and no larger than any positive `a/b`. -/

@[simp] theorem ratOf_intZero {b : ZFSet.{u}} (hb : b ∈ intPositive.{u}) :
    ratOf intZero.{u} b = ratZero.{u} := by
  rw [ratZero]
  refine (ratOf_eq_ratOf_iff intZero_mem_Int hb intZero_mem_Int one_mem_intPositive).mpr ?_
  rw [intZero_mul intOne_mem_Int, intZero_mul (intPositive_subset _ hb)]

theorem ratOf_add_same_denom {a c b : ZFSet.{u}} (ha : a ∈ Int.{u}) (hc : c ∈ Int.{u})
    (hb : b ∈ intPositive.{u}) :
    ratAdd (ratOf a b) (ratOf c b) = ratOf (intAdd a c) b := by
  have hbI := intPositive_subset _ hb
  rw [ratAdd_ratOf ha hb hc hb, ← intAdd_mul ha hc hbI,
      intMul_comm (intAdd_mem_Int ha hc) hbI, ratOf_cancel hb (intAdd_mem_Int ha hc) hb]

/-- `1/b` is below every positive rational with denominator `b`. -/
theorem ratOf_one_le {a b : ZFSet.{u}} (ha : a ∈ intPositive.{u}) (hb : b ∈ intPositive.{u}) :
    ratLe (ratOf intOne.{u} b) (ratOf a b) := by
  have haI := intPositive_subset _ ha
  have hbI := intPositive_subset _ hb
  refine (ratLe_ratOf intOne_mem_Int hb haI hb).mpr ?_
  exact intMul_le_mul_right intOne_mem_Int haI hbI (intZero_le_of_intPositive hb)
    (intOne_le_of_intPositive ha)

theorem rat_archimedean {M b : ZFSet.{u}} (hM : M ∈ Rat.{u}) (hb : b ∈ intPositive.{u}) :
    ∃ n : Nat, ratLt M (ratOf (intOfNat.{u} n) b) := by
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff M).mp hM
  obtain ⟨n, hle, hne⟩ :=
    int_lt_intOfNat_mul (intMul_mem_Int hc (intPositive_subset _ hb)) hd
  exact ⟨n, (ratLt_ratOf hc hd (intOfNat_mem_Int n) hb).mpr ⟨hle, hne⟩⟩

theorem ratOf_intOfNat_succ {b : ZFSet.{u}} (hb : b ∈ intPositive.{u}) (n : Nat) :
    ratOf (intOfNat.{u} (n + 1)) b
      = ratAdd (ratOf (intOfNat.{u} n) b) (ratOf intOne.{u} b) := by
  rw [intOfNat_succ, ← ratOf_add_same_denom (intOfNat_mem_Int n) intOne_mem_Int hb]

/-- `1/b` is positive. -/
theorem ratOf_one_pos {b : ZFSet.{u}} (hb : b ∈ intPositive.{u}) :
    ratLt ratZero.{u} (ratOf intOne.{u} b) := by
  rw [ratZero]
  refine (ratLt_ratOf intZero_mem_Int one_mem_intPositive intOne_mem_Int hb).mpr ⟨?_, ?_⟩
  · rw [intZero_mul (intPositive_subset _ hb)]
    exact intZero_le_of_intPositive
      (intMul_mem_intPositive one_mem_intPositive one_mem_intPositive)
  · rw [intZero_mul (intPositive_subset _ hb), intMul_one intOne_mem_Int]
    exact fun he => intPositive_ne_zero one_mem_intPositive he.symm

theorem ratZero_lt_one : ratLt ratZero.{u} ratOne.{u} := ratOf_one_pos one_mem_intPositive

/-- A positive rational has a positive numerator. -/
theorem intPositive_num {a b : ZFSet.{u}} (ha : a ∈ Int.{u}) (hb : b ∈ intPositive.{u})
    (h : ratLt ratZero.{u} (ratOf a b)) : a ∈ intPositive.{u} := by
  obtain ⟨hle, hne⟩ := (ratLt_ratOf intZero_mem_Int one_mem_intPositive ha hb).mp
    (by rwa [ratZero] at h)
  rw [intZero_mul (intPositive_subset _ hb)] at hle hne
  refine intPositive_of_intZero_le ha ?_ ?_
  · rwa [intMul_one ha] at hle
  · intro he
    exact hne (by rw [he, intMul_one intZero_mem_Int])

/-- Equality on ℚ is decidable, inherited from ℤ and ultimately from `Nat`, so
trichotomy is constructive. It is the reals where comparability stops being
free. -/
theorem rat_eq_or_ne {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    r = s ∨ r ≠ s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Rat_iff s).mp hs
  rcases int_eq_or_ne (intMul_mem_Int ha (intPositive_subset _ hd))
      (intMul_mem_Int hc (intPositive_subset _ hb)) with h | h
  · exact Or.inl ((ratOf_eq_ratOf_iff ha hb hc hd).mpr h)
  · exact Or.inr fun he => h ((ratOf_eq_ratOf_iff ha hb hc hd).mp he)

theorem ratLt_trichotomy {r s : ZFSet.{u}} (hr : r ∈ Rat.{u}) (hs : s ∈ Rat.{u}) :
    ratLt r s ∨ r = s ∨ ratLt s r := by
  rcases rat_eq_or_ne hr hs with rfl | hne
  · exact Or.inr (Or.inl rfl)
  · rcases ratLe_total hr hs with h | h
    · exact Or.inl ⟨h, hne⟩
    · exact Or.inr (Or.inr ⟨h, fun he => hne he.symm⟩)

/-! ### Differences

Translating between `x - y ≤ d` and `x ≤ y + d`, which is how every bound on a
bracket width gets used. -/

theorem sub_add_cancel {x y : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u}) :
    ratAdd (ratAdd x (ratNeg y)) y = x := by
  rw [ratAdd_assoc hx (ratNeg_mem_Rat hy) hy, ratAdd_comm (ratNeg_mem_Rat hy) hy,
      ratAdd_neg hy, ratAdd_zero hx]

theorem sub_le_iff_le_add {x y d : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hd : d ∈ Rat.{u}) : ratLe (ratAdd x (ratNeg y)) d ↔ ratLe x (ratAdd y d) := by
  rw [← ratAdd_le_add_right_iff hy (ratAdd_mem_Rat hx (ratNeg_mem_Rat hy)) hd,
      sub_add_cancel hx hy, ratAdd_comm hd hy]

theorem neg_le_sub_iff_le_add {x y d : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hd : d ∈ Rat.{u}) : ratLe (ratNeg d) (ratAdd x (ratNeg y)) ↔ ratLe y (ratAdd x d) := by
  have hnd := ratNeg_mem_Rat hd
  have e₁ : ratAdd (ratAdd (ratNeg d) y) d = y := by
    rw [ratAdd_comm hnd hy, ratAdd_assoc hy hnd hd, ratAdd_comm hnd hd,
        ratAdd_neg hd, ratAdd_zero hy]
  rw [← ratAdd_le_add_right_iff hy hnd (ratAdd_mem_Rat hx (ratNeg_mem_Rat hy)),
      sub_add_cancel hx hy,
      ← ratAdd_le_add_right_iff hd (ratAdd_mem_Rat hnd hy) hx, e₁]

theorem sub_lt_iff_lt_add {x y d : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hd : d ∈ Rat.{u}) : ratLt (ratAdd x (ratNeg y)) d ↔ ratLt x (ratAdd y d) := by
  rw [← ratAdd_lt_add_right_iff hy (ratAdd_mem_Rat hx (ratNeg_mem_Rat hy)) hd,
      sub_add_cancel hx hy, ratAdd_comm hd hy]

/-- The two differences of a pair `a ≤ b` with `b < a + d` both lie in `[-d, d]`. -/
theorem diff_bounds {a b d : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hd : d ∈ Rat.{u}) (hab : ratLe a b) (hlt : ratLt b (ratAdd a d))
    (hd0 : ratLt ratZero.{u} d) :
    ratLe (ratNeg d) (ratAdd a (ratNeg b)) ∧ ratLe (ratAdd a (ratNeg b)) d ∧
      ratLe (ratNeg d) (ratAdd b (ratNeg a)) ∧ ratLe (ratAdd b (ratNeg a)) d := by
  have hnd := ratNeg_mem_Rat hd
  have hnd0 : ratLe (ratNeg d) ratZero.{u} := by
    have hstep := (ratNeg_le_neg_iff hd ratZero_mem_Rat).mpr hd0.left
    rwa [ratNeg_zero] at hstep
  have hab0 : ratLe (ratAdd a (ratNeg b)) ratZero.{u} :=
    (sub_le_iff_le_add ha hb ratZero_mem_Rat).mpr (by rwa [ratAdd_zero hb])
  have hba0 : ratLe ratZero.{u} (ratAdd b (ratNeg a)) := by
    have hstep := (neg_le_sub_iff_le_add hb ha ratZero_mem_Rat).mpr
      (by rwa [ratAdd_zero hb])
    rwa [ratNeg_zero] at hstep
  exact ⟨(neg_le_sub_iff_le_add ha hb hd).mpr hlt.left,
    ratLe_trans (ratAdd_mem_Rat ha (ratNeg_mem_Rat hb)) ratZero_mem_Rat hd hab0 hd0.left,
    ratLe_trans hnd ratZero_mem_Rat (ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)) hnd0 hba0,
    (sub_le_iff_le_add hb ha hd).mpr hlt.left⟩

/-- A difference with itself is `0`, hence within any positive bound. -/
theorem diff_self_bounds {a d : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hd : d ∈ Rat.{u})
    (hd0 : ratLt ratZero.{u} d) :
    ratLe (ratNeg d) (ratAdd a (ratNeg a)) ∧ ratLe (ratAdd a (ratNeg a)) d := by
  have hnd0 : ratLe (ratNeg d) ratZero.{u} := by
    have hstep := (ratNeg_le_neg_iff hd ratZero_mem_Rat).mpr hd0.left
    rwa [ratNeg_zero] at hstep
  rw [ratAdd_neg ha]
  exact ⟨hnd0, hd0.left⟩

/-! ### Bounds

`located` for a product needs the corners of a small box to be close together,
which is the one genuinely analytic estimate in the development. These are its
parts: the inverse of a positive is positive, and a product of a bounded factor
with a small one is small. Both are proved by splitting on signs, which is free
in a proof. -/

theorem ratInv_pos {x : ZFSet.{u}} (hx : x ∈ Rat.{u}) (h : ratLt ratZero.{u} x) :
    ratLt ratZero.{u} (ratInv x) := by
  have hx0 : x ≠ ratZero.{u} := fun he => h.right he.symm
  have hix := ratInv_mem_Rat hx hx0
  rcases ratLt_trichotomy ratZero_mem_Rat hix with hlt | he | hgt
  · exact hlt
  · exfalso
    have hone : ratMul x (ratInv x) = ratZero.{u} := by rw [← he, ratMul_zero hx]
    rw [ratMul_inv hx hx0] at hone
    exact ratLt_irrefl (hone ▸ ratZero_lt_one)
  · exfalso
    have hle : ratLe (ratMul x (ratInv x)) ratZero.{u} := by
      have hm := ratMul_le_mul_right hix ratZero_mem_Rat hx hgt.left h.left
      rwa [ratZero_mul hx, ratMul_comm hix hx] at hm
    rw [ratMul_inv hx hx0] at hle
    exact ratLt_irrefl (ratLt_of_lt_of_le ratZero_mem_Rat ratOne_mem_Rat
      ratZero_mem_Rat ratZero_lt_one hle)

/-- Given `ε > 0` and any non-negative `c`, a positive `D` with `c · D < ε`.
The witness is `ε · (c + 1)⁻¹`, and every locatedness estimate in the
development is an instance of this. -/
theorem exists_mul_lt {c ε : ZFSet.{u}} (hc : c ∈ Rat.{u}) (hεQ : ε ∈ Rat.{u})
    (hc0 : ratLe ratZero.{u} c) (hε0 : ratLt ratZero.{u} ε) :
    ∃ D, D ∈ Rat.{u} ∧ ratLt ratZero.{u} D ∧ ratLt (ratMul c D) ε := by
  have hMQ := ratAdd_mem_Rat hc ratOne_mem_Rat
  have hcM : ratLt c (ratAdd c ratOne.{u}) := by
    have hstep := (ratAdd_lt_add_left_iff hc ratZero_mem_Rat ratOne_mem_Rat).mpr
      ratZero_lt_one
    rwa [ratAdd_zero hc] at hstep
  have hM0 : ratLt ratZero.{u} (ratAdd c ratOne.{u}) :=
    ratLt_of_le_of_lt ratZero_mem_Rat hc hMQ hc0 hcM
  have hMne : ratAdd c ratOne.{u} ≠ ratZero.{u} := fun he => hM0.right he.symm
  have hinvQ := ratInv_mem_Rat hMQ hMne
  have hinv0 := ratInv_pos hMQ hM0
  have hinvne := fun he => hinv0.right (Eq.symm he)
  refine ⟨ratMul ε (ratInv (ratAdd c ratOne.{u})), ratMul_mem_Rat hεQ hinvQ, ?_, ?_⟩
  · have hstep := ratMul_lt_mul_right ratZero_mem_Rat hεQ hinvQ hinvne hinv0.left hε0
    rwa [ratZero_mul hinvQ] at hstep
  · have hone : ratLt (ratMul c (ratInv (ratAdd c ratOne.{u}))) ratOne.{u} := by
      have hstep := ratMul_lt_mul_right hc hMQ hinvQ hinvne hinv0.left hcM
      rwa [ratMul_inv hMQ hMne] at hstep
    have htwo := ratMul_lt_mul_right (ratMul_mem_Rat hc hinvQ) ratOne_mem_Rat hεQ
      (fun he => hε0.right he.symm) hε0.left hone
    rw [ratOne_mul hεQ] at htwo
    have hthree : ratMul c (ratMul ε (ratInv (ratAdd c ratOne.{u})))
        = ratMul (ratMul c (ratInv (ratAdd c ratOne.{u}))) ε := by
      rw [ratMul_comm hεQ hinvQ, ← ratMul_assoc hc hinvQ hεQ]
    rw [hthree]
    exact htwo

/-- A factor bounded by `K` times one bounded by `D` is bounded by `K · D`. -/
theorem mul_le_of_bounds {a e K D : ZFSet.{u}} (ha : a ∈ Rat.{u}) (he : e ∈ Rat.{u})
    (hK : K ∈ Rat.{u}) (hD : D ∈ Rat.{u})
    (h1 : ratLe (ratNeg K) a) (h2 : ratLe a K)
    (h3 : ratLe (ratNeg D) e) (h4 : ratLe e D)
    (hK0 : ratLe ratZero.{u} K) : ratLe (ratMul a e) (ratMul K D) := by
  have hnK := ratNeg_mem_Rat hK
  have hne := ratNeg_mem_Rat he
  rcases ratLe_total ratZero_mem_Rat he with he0 | he0
  · have s1 : ratLe (ratMul a e) (ratMul K e) := ratMul_le_mul_right ha hK he h2 he0
    have s2 : ratLe (ratMul K e) (ratMul K D) := by
      rw [ratMul_comm hK he, ratMul_comm hK hD]
      exact ratMul_le_mul_right he hD hK h4 hK0
    exact ratLe_trans (ratMul_mem_Rat ha he) (ratMul_mem_Rat hK he)
      (ratMul_mem_Rat hK hD) s1 s2
  · have s1 : ratLe (ratMul a e) (ratMul (ratNeg K) e) :=
      ratMul_le_mul_right_of_nonpos hnK ha he h1 he0
    have hrw : ratMul (ratNeg K) e = ratMul K (ratNeg e) := by
      rw [ratMul_comm hnK he, ratMul_neg he hK, ratMul_neg hK he, ratMul_comm he hK]
    have hne0 : ratLe (ratNeg e) D := by
      have hstep := (ratNeg_le_neg_iff he (ratNeg_mem_Rat hD)).mpr h3
      rwa [ratNeg_ratNeg hD] at hstep
    have s2 : ratLe (ratMul K (ratNeg e)) (ratMul K D) := by
      rw [ratMul_comm hK hne, ratMul_comm hK hD]
      exact ratMul_le_mul_right hne hD hK hne0 hK0
    rw [hrw] at s1
    exact ratLe_trans (ratMul_mem_Rat ha he) (ratMul_mem_Rat hK hne)
      (ratMul_mem_Rat hK hD) s1 s2

/-- Replacing one factor moves a product by at most `K · D`. The identity is
`a·b = a·b' + a·(b - b')`, which `ratAdd_sub_cancel` closes in one step. -/
theorem mul_shift_le {a b b' K D : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hb' : b' ∈ Rat.{u}) (hK : K ∈ Rat.{u}) (hD : D ∈ Rat.{u})
    (haK : ratLe (ratNeg K) a) (haK' : ratLe a K)
    (h1 : ratLe (ratNeg D) (ratAdd b (ratNeg b'))) (h2 : ratLe (ratAdd b (ratNeg b')) D)
    (hK0 : ratLe ratZero.{u} K) :
    ratLe (ratMul a b) (ratAdd (ratMul a b') (ratMul K D)) := by
  have hd := ratAdd_mem_Rat hb (ratNeg_mem_Rat hb')
  have hsplit : ratMul a b = ratAdd (ratMul a b') (ratMul a (ratAdd b (ratNeg b'))) := by
    rw [ratMul_add ha hb (ratNeg_mem_Rat hb'), ratMul_neg ha hb',
        ratAdd_sub_cancel (ratMul_mem_Rat ha hb) (ratMul_mem_Rat ha hb')]
  rw [hsplit]
  refine (ratAdd_le_add_left_iff (ratMul_mem_Rat ha hb') (ratMul_mem_Rat ha hd)
    (ratMul_mem_Rat hK hD)).mpr ?_
  exact mul_le_of_bounds ha hd hK hD haK haK' h1 h2 hK0

/-- Two corner products of the same small box differ by at most `2·K·D`. -/
theorem corner_close {a a' b b' K D : ZFSet.{u}} (ha : a ∈ Rat.{u}) (ha' : a' ∈ Rat.{u})
    (hb : b ∈ Rat.{u}) (hb' : b' ∈ Rat.{u}) (hK : K ∈ Rat.{u}) (hD : D ∈ Rat.{u})
    (haK : ratLe (ratNeg K) a) (haK' : ratLe a K)
    (hb'K : ratLe (ratNeg K) b') (hb'K' : ratLe b' K)
    (hbb : ratLe (ratNeg D) (ratAdd b (ratNeg b')))
    (hbb' : ratLe (ratAdd b (ratNeg b')) D)
    (haa : ratLe (ratNeg D) (ratAdd a (ratNeg a')))
    (haa' : ratLe (ratAdd a (ratNeg a')) D)
    (hK0 : ratLe ratZero.{u} K) :
    ratLe (ratMul a b) (ratAdd (ratMul a' b') (ratAdd (ratMul K D) (ratMul K D))) := by
  have hKD := ratMul_mem_Rat hK hD
  -- `a·b ≤ a·b' + K·D`
  have s1 := mul_shift_le ha hb hb' hK hD haK haK' hbb hbb' hK0
  -- `a·b' = b'·a ≤ b'·a' + K·D = a'·b' + K·D`
  have s2 : ratLe (ratMul a b') (ratAdd (ratMul a' b') (ratMul K D)) := by
    have hstep := mul_shift_le hb' ha ha' hK hD hb'K hb'K' haa haa' hK0
    rwa [ratMul_comm hb' ha, ratMul_comm hb' ha'] at hstep
  -- add the two
  refine ratLe_trans (ratMul_mem_Rat ha hb) (ratAdd_mem_Rat (ratMul_mem_Rat ha hb') hKD)
    (ratAdd_mem_Rat (ratMul_mem_Rat ha' hb') (ratAdd_mem_Rat hKD hKD)) s1 ?_
  have s4 : ratLe (ratAdd (ratMul a b') (ratMul K D))
      (ratAdd (ratAdd (ratMul a' b') (ratMul K D)) (ratMul K D)) :=
    (ratAdd_le_add_right_iff hKD (ratMul_mem_Rat ha hb')
      (ratAdd_mem_Rat (ratMul_mem_Rat ha' hb') hKD)).mpr s2
  rwa [ratAdd_assoc (ratMul_mem_Rat ha' hb') hKD hKD] at s4

/-! ## Bounds for the located reals

Two facts about rationals that the located reals need and nothing here does. -/

theorem ratLt_mul_of_corners {p q q' r r' x y : ZFSet.{u}} (hp : p ∈ Rat.{u})
    (hq : q ∈ Rat.{u}) (hq' : q' ∈ Rat.{u}) (hr : r ∈ Rat.{u}) (hr' : r' ∈ Rat.{u})
    (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hqx : ratLe q x) (hxq' : ratLe x q') (hry : ratLe r y) (hyr' : ratLe y r')
    (h₁ : ratLt p (ratMul q r)) (h₂ : ratLt p (ratMul q r'))
    (h₃ : ratLt p (ratMul q' r)) (h₄ : ratLt p (ratMul q' r')) :
    ratLt p (ratMul x y) := by
  -- below `a·y` for the endpoint `a` on the side `y`'s sign selects
  have side : ∀ a, a ∈ Rat.{u} → ratLt p (ratMul a r) → ratLt p (ratMul a r') →
      ratLt p (ratMul a y) := by
    intro a haQ hlo hhi
    rcases ratLe_total ratZero_mem_Rat haQ with ha0 | ha0
    · refine ratLt_of_lt_of_le hp (ratMul_mem_Rat haQ hr) (ratMul_mem_Rat haQ hy) hlo ?_
      have := ratMul_le_mul_right hr hy haQ hry ha0
      rwa [ratMul_comm hr haQ, ratMul_comm hy haQ] at this
    · refine ratLt_of_lt_of_le hp (ratMul_mem_Rat haQ hr') (ratMul_mem_Rat haQ hy) hhi ?_
      have := ratMul_le_mul_right_of_nonpos hy hr' haQ hyr' ha0
      rwa [ratMul_comm hr' haQ, ratMul_comm hy haQ] at this
  rcases ratLe_total ratZero_mem_Rat hy with hy0 | hy0
  · refine ratLt_of_lt_of_le hp (ratMul_mem_Rat hq hy) (ratMul_mem_Rat hx hy)
      (side q hq h₁ h₂) (ratMul_le_mul_right hq hx hy hqx hy0)
  · refine ratLt_of_lt_of_le hp (ratMul_mem_Rat hq' hy) (ratMul_mem_Rat hx hy)
      (side q' hq' h₃ h₄) (ratMul_le_mul_right_of_nonpos hx hq' hy hxq' hy0)

theorem exists_scale_below_one {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hpq : ratLt p q) (hq0 : ratLt ratZero.{u} q) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt r ratOne.{u} ∧ ratLt p (ratMul q r) := by
  have hne : q ≠ ratZero.{u} := ratNe_zero_of_pos hq0
  have hiQ := ratInv_mem_Rat hq hne
  have hi0 := ratInv_pos hq hq0
  have hone := ratMul_inv hq hne
  -- `p/q < 1`, because `p < q` and `q⁻¹ > 0`
  have hlt : ratLt (ratMul p (ratInv q)) ratOne.{u} := by
    have := ratMul_lt_mul_right hp hq hiQ
      (ratNe_zero_of_pos hi0) hi0.left hpq
    rwa [hone] at this
  obtain ⟨r, hrQ, hpr, hr1⟩ :=
    rat_dense (ratMul_mem_Rat hp hiQ) ratOne_mem_Rat hlt
  refine ⟨r, hrQ, hr1, ?_⟩
  -- `p = q·(p/q) < q·r`
  have hstep := ratMul_lt_mul_right (ratMul_mem_Rat hp hiQ) hrQ hq
    (ratNe_zero_of_pos hq0) hq0.left hpr
  rw [ratMul_comm (ratMul_mem_Rat hp hiQ) hq, ratMul_comm hrQ hq,
    ← ratMul_assoc hq hp hiQ, ratMul_comm hq hp, ratMul_assoc hp hq hiQ,
    hone, ratMul_one hp] at hstep
  exact hstep

/-- The inverse of a negative rational is negative: `q · q⁻¹ = 1 > 0`, so a
non-negative inverse would put the product at or below zero. -/
theorem ratInv_neg {q : ZFSet.{u}} (hq : q ∈ Rat.{u}) (hq0 : ratLt q ratZero.{u}) :
    ratLt (ratInv q) ratZero.{u} := by
  have hne : q ≠ ratZero.{u} := ratNe_zero_of_neg hq0
  have hiQ := ratInv_mem_Rat hq hne
  have hone := ratMul_inv hq hne
  rcases ratLe_total hiQ ratZero_mem_Rat with h0 | h0
  · refine ⟨h0, fun he => ?_⟩
    rw [he, ratMul_zero hq] at hone
    exact absurd hone.symm (ratNe_zero_of_pos ratZero_lt_one)
  · have := ratMul_le_mul_right_of_nonpos ratZero_mem_Rat hiQ hq h0 hq0.left
    rw [ratMul_comm hiQ hq, hone, ratZero_mul hq] at this
    exact absurd (ratLe_antisymm ratOne_mem_Rat ratZero_mem_Rat this ratZero_lt_one.left)
      (ratNe_zero_of_pos ratZero_lt_one)

/-- The mirror of `exists_scale_below_one`, for a negative bound: given
`p < q < 0`, a scale strictly above one that keeps `q` above `p`. Dividing by a
negative flips the inequality, so the non-positive monotonicity lemmas replace
the others throughout. -/
theorem exists_scale_above_one {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hpq : ratLt p q) (hq0 : ratLt q ratZero.{u}) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt ratOne.{u} r ∧ ratLt p (ratMul q r) := by
  have hne : q ≠ ratZero.{u} := ratNe_zero_of_neg hq0
  have hiQ := ratInv_mem_Rat hq hne
  have hone := ratMul_inv hq hne
  have hi0 := ratInv_neg hq hq0
  have hine : ratInv q ≠ ratZero.{u} := ratNe_zero_of_neg hi0
  -- `1 < p·q⁻¹`, because `p < q` and `q⁻¹ < 0`
  have hlt : ratLt ratOne.{u} (ratMul p (ratInv q)) := by
    have := ratMul_lt_mul_right_of_nonpos hp hq hiQ hine hi0.left hpq
    rwa [hone] at this
  obtain ⟨r, hrQ, h1r, hrp⟩ := rat_dense ratOne_mem_Rat (ratMul_mem_Rat hp hiQ) hlt
  refine ⟨r, hrQ, h1r, ?_⟩
  -- `q·r > q·(p·q⁻¹) = p`, the multiplier being negative
  have hstep := ratMul_lt_mul_right_of_nonpos hrQ (ratMul_mem_Rat hp hiQ) hq hne hq0.left hrp
  rwa [ratMul_comm (ratMul_mem_Rat hp hiQ) hq, ratMul_comm hrQ hq,
    ← ratMul_assoc hq hp hiQ, ratMul_comm hq hp, ratMul_assoc hp hq hiQ,
    hone, ratMul_one hp] at hstep

/-- For a negative `p`, any scale strictly between zero and one keeps `q` above
it, whichever sign `q` has: `q · r` lies between `q` and `0`. -/
theorem corner_above_of_neg {p q r : ZFSet.{u}} (hpQ : p ∈ Rat.{u})
    (hqQ : q ∈ Rat.{u}) (hrQ : r ∈ Rat.{u}) (hp0 : ratLt p ratZero.{u})
    (hr0 : ratLt ratZero.{u} r) (hr1 : ratLt r ratOne.{u}) (hpq : ratLt p q) :
    ratLt p (ratMul q r) := by
  rcases ratLe_total ratZero_mem_Rat hqQ with hq0 | hq0
  · -- `q ≥ 0`, so `q·r ≥ 0 > p`
    refine ratLt_of_lt_of_le hpQ ratZero_mem_Rat (ratMul_mem_Rat hqQ hrQ) hp0 ?_
    have := ratMul_le_mul_right ratZero_mem_Rat hqQ hrQ hq0 hr0.left
    rwa [ratZero_mul hrQ] at this
  · -- `q ≤ 0` and `r < 1`, so `q·r ≥ q·1 = q > p`
    refine ratLt_of_lt_of_le hpQ hqQ (ratMul_mem_Rat hqQ hrQ) hpq ?_
    have := ratMul_le_mul_right_of_nonpos hrQ ratOne_mem_Rat hqQ hr1.left hq0
    rwa [ratMul_comm hrQ hqQ, ratMul_comm ratOne_mem_Rat hqQ, ratMul_one hqQ] at this

/-- The mirror of `ratLt_mul_of_corners`: a point above all four corner
products is above every product from inside the two brackets. -/
theorem ratMul_lt_of_corners {p q q' r r' x y : ZFSet.{u}} (hp : p ∈ Rat.{u})
    (hq : q ∈ Rat.{u}) (hq' : q' ∈ Rat.{u}) (hr : r ∈ Rat.{u}) (hr' : r' ∈ Rat.{u})
    (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hqx : ratLe q x) (hxq' : ratLe x q') (hry : ratLe r y) (hyr' : ratLe y r')
    (h₁ : ratLt (ratMul q r) p) (h₂ : ratLt (ratMul q r') p)
    (h₃ : ratLt (ratMul q' r) p) (h₄ : ratLt (ratMul q' r') p) :
    ratLt (ratMul x y) p := by
  have side : ∀ a, a ∈ Rat.{u} → ratLt (ratMul a r) p → ratLt (ratMul a r') p →
      ratLt (ratMul a y) p := by
    intro a haQ hlo hhi
    rcases ratLe_total ratZero_mem_Rat haQ with ha0 | ha0
    · refine ratLt_of_le_of_lt (ratMul_mem_Rat haQ hy) (ratMul_mem_Rat haQ hr') hp ?_ hhi
      have := ratMul_le_mul_right hy hr' haQ hyr' ha0
      rwa [ratMul_comm hy haQ, ratMul_comm hr' haQ] at this
    · refine ratLt_of_le_of_lt (ratMul_mem_Rat haQ hy) (ratMul_mem_Rat haQ hr) hp ?_ hlo
      have := ratMul_le_mul_right_of_nonpos hr hy haQ hry ha0
      rwa [ratMul_comm hy haQ, ratMul_comm hr haQ] at this
  rcases ratLe_total ratZero_mem_Rat hy with hy0 | hy0
  · exact ratLt_of_le_of_lt (ratMul_mem_Rat hx hy) (ratMul_mem_Rat hq' hy) hp
      (ratMul_le_mul_right hx hq' hy hxq' hy0) (side q' hq' h₃ h₄)
  · exact ratLt_of_le_of_lt (ratMul_mem_Rat hx hy) (ratMul_mem_Rat hq hy) hp
      (ratMul_le_mul_right_of_nonpos hq hx hy hqx hy0) (side q hq h₁ h₂)

/-- A scale small enough to bring any fixed rational inside `(-e, e)`. Trichotomy
on `c`, and in each non-zero case the bound is `e/c` read with the sign that
makes it positive. This is the step towards zero that `x · 0 = 0` needs, as
`exists_scale_below` is the step towards one. -/
theorem exists_small_scale {c e : ZFSet.{u}} (hc : c ∈ Rat.{u}) (he : e ∈ Rat.{u})
    (he0 : ratLt ratZero.{u} e) :
    ∃ d, d ∈ Rat.{u} ∧ ratLt ratZero.{u} d ∧
      ratLt (ratMul c d) e ∧ ratLt (ratNeg e) (ratMul c d) := by
  have hnege : ratLt (ratNeg e) ratZero.{u} := by
    have := (ratNeg_lt_neg_iff he ratZero_mem_Rat).mpr he0
    rwa [ratNeg_zero] at this
  rcases ratLt_trichotomy hc ratZero_mem_Rat with hneg | rfl | hpos
  · -- `c < 0`: take `0 < d < (-e)/c`, so `c·d ∈ (-e, 0)`
    have hne : c ≠ ratZero.{u} := ratNe_zero_of_neg hneg
    have hbound : ratLt ratZero.{u} (ratMul (ratNeg e) (ratInv c)) := by
      have := ratMul_lt_mul_right_of_nonpos (ratNeg_mem_Rat he) ratZero_mem_Rat
        (ratInv_mem_Rat hc hne) (fun h => ratLt_irrefl (h ▸ ratInv_neg hc hneg))
        (ratInv_neg hc hneg).left
        hnege
      rwa [ratZero_mul (ratInv_mem_Rat hc hne)] at this
    obtain ⟨d, hdQ, h0d, hdb⟩ := rat_dense ratZero_mem_Rat
      (ratMul_mem_Rat (ratNeg_mem_Rat he) (ratInv_mem_Rat hc hne)) hbound
    refine ⟨d, hdQ, h0d, ?_, ?_⟩
    · exact ratLt_trans (ratMul_mem_Rat hc hdQ) ratZero_mem_Rat he
        (by
          have := ratMul_lt_mul_right_of_nonpos ratZero_mem_Rat hdQ hc hne hneg.left h0d
          rwa [ratMul_comm ratZero_mem_Rat hc, ratMul_zero hc, ratMul_comm hdQ hc] at this)
        he0
    · have := ratMul_lt_mul_right_of_nonpos hdQ
        (ratMul_mem_Rat (ratNeg_mem_Rat he) (ratInv_mem_Rat hc hne)) hc hne hneg.left hdb
      rw [ratMul_comm (ratMul_mem_Rat (ratNeg_mem_Rat he) (ratInv_mem_Rat hc hne)) hc,
        ← ratMul_assoc hc (ratNeg_mem_Rat he) (ratInv_mem_Rat hc hne),
        ratMul_comm hc (ratNeg_mem_Rat he), ratMul_assoc (ratNeg_mem_Rat he) hc
          (ratInv_mem_Rat hc hne), ratMul_inv hc hne, ratMul_one (ratNeg_mem_Rat he),
        ratMul_comm hdQ hc] at this
      exact this
  · -- `c = 0`: every scale works
    exact ⟨ratOne.{u}, ratOne_mem_Rat, ratZero_lt_one,
      by rw [ratZero_mul ratOne_mem_Rat]; exact he0,
      by rw [ratZero_mul ratOne_mem_Rat]; exact hnege⟩
  · -- `c > 0`: take `0 < d < e/c`, so `c·d ∈ (0, e)`
    have hne : c ≠ ratZero.{u} := ratNe_zero_of_pos hpos
    have hi0 := ratInv_pos hc hpos
    have hbound : ratLt ratZero.{u} (ratMul e (ratInv c)) := by
      have := ratMul_lt_mul_right ratZero_mem_Rat he (ratInv_mem_Rat hc hne)
        (ratNe_zero_of_pos hi0) hi0.left he0
      rwa [ratZero_mul (ratInv_mem_Rat hc hne)] at this
    obtain ⟨d, hdQ, h0d, hdb⟩ := rat_dense ratZero_mem_Rat
      (ratMul_mem_Rat he (ratInv_mem_Rat hc hne)) hbound
    refine ⟨d, hdQ, h0d, ?_, ?_⟩
    · have := ratMul_lt_mul_right hdQ (ratMul_mem_Rat he (ratInv_mem_Rat hc hne)) hc
        hne hpos.left hdb
      rw [ratMul_comm (ratMul_mem_Rat he (ratInv_mem_Rat hc hne)) hc,
        ← ratMul_assoc hc he (ratInv_mem_Rat hc hne), ratMul_comm hc he,
        ratMul_assoc he hc (ratInv_mem_Rat hc hne), ratMul_inv hc hne, ratMul_one he,
        ratMul_comm hdQ hc] at this
      exact this
    · refine ratLt_trans (ratNeg_mem_Rat he) ratZero_mem_Rat (ratMul_mem_Rat hc hdQ)
        hnege ?_
      have := ratMul_lt_mul_right ratZero_mem_Rat hdQ hc hne hpos.left h0d
      rwa [ratMul_comm ratZero_mem_Rat hc, ratMul_zero hc, ratMul_comm hdQ hc] at this

/-- Shrinking the scale keeps the bound. Needed because, unlike the unit law,
the two bracket ends do not order by absolute value -- `q ≤ w` says nothing
about `|q|` and `|w|` -- so the two scales must be found separately and the
smaller used. -/
theorem small_scale_mono {c d d' e : ZFSet.{u}} (hc : c ∈ Rat.{u}) (hd : d ∈ Rat.{u})
    (hd' : d' ∈ Rat.{u}) (he : e ∈ Rat.{u}) (he0 : ratLt ratZero.{u} e)
    (h0d' : ratLt ratZero.{u} d') (hle : ratLe d' d)
    (hhi : ratLt (ratMul c d) e) (hlo : ratLt (ratNeg e) (ratMul c d)) :
    ratLt (ratMul c d') e ∧ ratLt (ratNeg e) (ratMul c d') := by
  have hnege : ratLt (ratNeg e) ratZero.{u} := by
    have := (ratNeg_lt_neg_iff he ratZero_mem_Rat).mpr he0
    rwa [ratNeg_zero] at this
  rcases ratLt_trichotomy hc ratZero_mem_Rat with hneg | rfl | hpos
  · -- `c < 0`: shrinking `d` raises `c·d`, so the lower bound is what needs care
    have hneg0 : ratLt (ratMul c d') ratZero.{u} := by
      have := ratMul_lt_mul_right_of_nonpos ratZero_mem_Rat hd' hc
        (ratNe_zero_of_neg hneg) hneg.left h0d'
      rwa [ratMul_comm ratZero_mem_Rat hc, ratMul_zero hc, ratMul_comm hd' hc] at this
    refine ⟨ratLt_trans (ratMul_mem_Rat hc hd') ratZero_mem_Rat he hneg0 he0, ?_⟩
    refine ratLt_of_lt_of_le (ratNeg_mem_Rat he) (ratMul_mem_Rat hc hd)
      (ratMul_mem_Rat hc hd') hlo ?_
    have := ratMul_le_mul_right_of_nonpos hd' hd hc hle hneg.left
    rwa [ratMul_comm hd hc, ratMul_comm hd' hc] at this
  · rw [ratZero_mul hd']
    exact ⟨he0, hnege⟩
  · -- `c > 0`: shrinking `d` lowers `c·d`, so the upper bound is what needs care
    have hpos0 : ratLt ratZero.{u} (ratMul c d') := by
      have := ratMul_lt_mul_right ratZero_mem_Rat hd' hc
        (ratNe_zero_of_pos hpos) hpos.left h0d'
      rwa [ratMul_comm ratZero_mem_Rat hc, ratMul_zero hc, ratMul_comm hd' hc] at this
    refine ⟨?_, ratLt_trans (ratNeg_mem_Rat he) ratZero_mem_Rat (ratMul_mem_Rat hc hd')
      hnege hpos0⟩
    refine ratLt_of_le_of_lt (ratMul_mem_Rat hc hd') (ratMul_mem_Rat hc hd) he ?_ hhi
    have := ratMul_le_mul_right hd' hd hc hle hpos.left
    rwa [ratMul_comm hd' hc, ratMul_comm hd hc] at this

/-- Two coefficients at once: one `s'` below `s` keeping both products above `p`.
The two gaps give two steps and the smaller serves both, by `small_scale_mono`.
This is the form distributivity needs -- a bracket has two ends, and the
replacement of a bound by a member of the cut must work for both. -/
theorem exists_lt_of_mul_lt₂ {p c c' s : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hc : c ∈ Rat.{u})
    (hc' : c' ∈ Rat.{u}) (hs : s ∈ Rat.{u}) (h : ratLt p (ratMul c s))
    (h' : ratLt p (ratMul c' s)) :
    ∃ s', s' ∈ Rat.{u} ∧ ratLt s' s ∧ ratLt p (ratMul c s') ∧ ratLt p (ratMul c' s') := by
  have gap : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt p (ratMul b s) →
      ratLt ratZero.{u} (ratAdd (ratMul b s) (ratNeg p)) := by
    intro b hb hlt
    have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hp) hp (ratMul_mem_Rat hb hs)).mpr hlt
    rwa [ratAdd_neg hp] at this
  obtain ⟨d₁, hd₁Q, h0d₁, hhi₁, hlo₁⟩ :=
    exists_small_scale hc (ratAdd_mem_Rat (ratMul_mem_Rat hc hs) (ratNeg_mem_Rat hp))
      (gap hc h)
  obtain ⟨d₂, hd₂Q, h0d₂, hhi₂, hlo₂⟩ :=
    exists_small_scale hc' (ratAdd_mem_Rat (ratMul_mem_Rat hc' hs) (ratNeg_mem_Rat hp))
      (gap hc' h')
  obtain ⟨d, hdQ, h0d, hd₁, hd₂⟩ :
      ∃ d, d ∈ Rat.{u} ∧ ratLt ratZero.{u} d ∧
        ratLt (ratMul c d) (ratAdd (ratMul c s) (ratNeg p)) ∧
        ratLt (ratMul c' d) (ratAdd (ratMul c' s) (ratNeg p)) := by
    rcases ratLe_total hd₁Q hd₂Q with hle | hle
    · exact ⟨d₁, hd₁Q, h0d₁, hhi₁,
        (small_scale_mono hc' hd₂Q hd₁Q
          (ratAdd_mem_Rat (ratMul_mem_Rat hc' hs) (ratNeg_mem_Rat hp))
          (gap hc' h') h0d₁ hle hhi₂ hlo₂).left⟩
    · exact ⟨d₂, hd₂Q, h0d₂,
        (small_scale_mono hc hd₁Q hd₂Q
          (ratAdd_mem_Rat (ratMul_mem_Rat hc hs) (ratNeg_mem_Rat hp))
          (gap hc h) h0d₂ hle hhi₁ hlo₁).left, hhi₂⟩
  -- `s - d` is below `s`, and `b·(s-d) = b·s - b·d > b·s - (b·s - p) = p` for both
  have step : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} →
      ratLt (ratMul b d) (ratAdd (ratMul b s) (ratNeg p)) →
      ratLt p (ratMul b (ratAdd s (ratNeg d))) := by
    intro b hb hbd
    have hbs := ratMul_mem_Rat hb hs
    have hbd' := ratMul_mem_Rat hb hdQ
    rw [ratMul_add hb hs (ratNeg_mem_Rat hdQ), ratMul_neg hb hdQ]
    have h1 := (ratAdd_lt_add_right_iff hp hbd'
      (ratAdd_mem_Rat hbs (ratNeg_mem_Rat hp))).mpr hbd
    rw [ratAdd_assoc hbs (ratNeg_mem_Rat hp) hp, ratAdd_comm (ratNeg_mem_Rat hp) hp,
      ratAdd_neg hp, ratAdd_zero hbs] at h1
    refine (ratAdd_lt_add_right_iff hbd' hp (ratAdd_mem_Rat hbs (ratNeg_mem_Rat hbd'))).mp ?_
    rw [ratAdd_assoc hbs (ratNeg_mem_Rat hbd') hbd',
      ratAdd_comm (ratNeg_mem_Rat hbd') hbd', ratAdd_neg hbd', ratAdd_zero hbs,
      ratAdd_comm hp hbd']
    exact h1
  refine ⟨ratAdd s (ratNeg d), ratAdd_mem_Rat hs (ratNeg_mem_Rat hdQ), ?_,
    step hc hd₁, step hc' hd₂⟩
  have := (ratAdd_lt_add_left_iff hs (ratNeg_mem_Rat hdQ) ratZero_mem_Rat).mpr (by
    have := (ratNeg_lt_neg_iff hdQ ratZero_mem_Rat).mpr h0d
    rwa [ratNeg_zero] at this)
  rwa [ratAdd_zero hs] at this

/-- The corner schema for distributivity: if `p` is below `a + b`, and `a` is
below `e · f` while `b` is below `e · g`, then `p` is below `e · (f + g)`. All
four corners of the distributed product are this lemma, with `e` ranging over the
bracket's two ends and `f`, `g` over the two summands' matching ends. -/
theorem lt_mul_add_of_lt {p a b e f g : ZFSet.{u}} (hp : p ∈ Rat.{u}) (ha : a ∈ Rat.{u})
    (hb : b ∈ Rat.{u}) (he : e ∈ Rat.{u}) (hf : f ∈ Rat.{u}) (hg : g ∈ Rat.{u})
    (hab : ratLt p (ratAdd a b)) (haf : ratLt a (ratMul e f)) (hbg : ratLt b (ratMul e g)) :
    ratLt p (ratMul e (ratAdd f g)) := by
  rw [ratMul_add he hf hg]
  exact ratLt_trans hp (ratAdd_mem_Rat ha hb)
    (ratAdd_mem_Rat (ratMul_mem_Rat he hf) (ratMul_mem_Rat he hg)) hab
    (ratAdd_lt_add ha (ratMul_mem_Rat he hf) hb (ratMul_mem_Rat he hg) haf hbg)

/-- The mirror of `exists_lt_of_mul_lt₂`, growing the argument instead of
shrinking it. By negation: `p < c·s` is `p < (-c)·(-s)`, and a smaller `-s`
is a larger `s`. -/
theorem exists_gt_of_mul_lt₂ {p c c' s : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hc : c ∈ Rat.{u})
    (hc' : c' ∈ Rat.{u}) (hs : s ∈ Rat.{u}) (h : ratLt p (ratMul c s))
    (h' : ratLt p (ratMul c' s)) :
    ∃ s', s' ∈ Rat.{u} ∧ ratLt s s' ∧ ratLt p (ratMul c s') ∧ ratLt p (ratMul c' s') := by
  have flip : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt p (ratMul b s) →
      ratLt p (ratMul (ratNeg b) (ratNeg s)) := by
    intro b hb hlt
    rwa [ratMul_neg (ratNeg_mem_Rat hb) hs, ratMul_comm (ratNeg_mem_Rat hb) hs,
      ratMul_neg hs hb, ratNeg_ratNeg (ratMul_mem_Rat hs hb), ratMul_comm hs hb]
  obtain ⟨u, huQ, hus, hcu, hc'u⟩ := exists_lt_of_mul_lt₂ hp (ratNeg_mem_Rat hc)
    (ratNeg_mem_Rat hc') (ratNeg_mem_Rat hs) (flip hc h) (flip hc' h')
  have back : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt p (ratMul (ratNeg b) u) →
      ratLt p (ratMul b (ratNeg u)) := by
    intro b hb hlt
    rw [ratMul_neg hb huQ]
    rwa [ratMul_comm (ratNeg_mem_Rat hb) huQ, ratMul_neg huQ hb,
      ratMul_comm huQ hb] at hlt
  refine ⟨ratNeg u, ratNeg_mem_Rat huQ, ?_, back hc hcu, back hc' hc'u⟩
  have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hs) huQ).mpr hus
  rwa [ratNeg_ratNeg hs] at this

/-- The corner schema for the upper half. -/
theorem mul_add_lt_of_lt {p a b e f g : ZFSet.{u}} (hp : p ∈ Rat.{u}) (ha : a ∈ Rat.{u})
    (hb : b ∈ Rat.{u}) (he : e ∈ Rat.{u}) (hf : f ∈ Rat.{u}) (hg : g ∈ Rat.{u})
    (hab : ratLt (ratAdd a b) p) (haf : ratLt (ratMul e f) a) (hbg : ratLt (ratMul e g) b) :
    ratLt (ratMul e (ratAdd f g)) p := by
  rw [ratMul_add he hf hg]
  exact ratLt_trans (ratAdd_mem_Rat (ratMul_mem_Rat he hf) (ratMul_mem_Rat he hg))
    (ratAdd_mem_Rat ha hb) hp
    (ratAdd_lt_add (ratMul_mem_Rat he hf) ha (ratMul_mem_Rat he hg) hb haf hbg) hab

/-- Shrinking the argument while keeping both products below a bound, by
negation from `exists_gt_of_mul_lt₂`. -/
theorem exists_lt_of_lt_mul₂ {p c c' s : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hc : c ∈ Rat.{u})
    (hc' : c' ∈ Rat.{u}) (hs : s ∈ Rat.{u}) (h : ratLt (ratMul c s) p)
    (h' : ratLt (ratMul c' s) p) :
    ∃ s', s' ∈ Rat.{u} ∧ ratLt s' s ∧ ratLt (ratMul c s') p ∧ ratLt (ratMul c' s') p := by
  have fwd : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt (ratMul b s) p →
      ratLt (ratNeg p) (ratMul b (ratNeg s)) := by
    intro b hb hlt
    rw [ratMul_neg hb hs]
    exact (ratNeg_lt_neg_iff hp (ratMul_mem_Rat hb hs)).mpr hlt
  obtain ⟨u, huQ, hsu, hcu, hc'u⟩ := exists_gt_of_mul_lt₂ (ratNeg_mem_Rat hp) hc hc'
    (ratNeg_mem_Rat hs) (fwd hc h) (fwd hc' h')
  have back : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt (ratNeg p) (ratMul b u) →
      ratLt (ratMul b (ratNeg u)) p := by
    intro b hb hlt
    rw [ratMul_neg hb huQ]
    have := (ratNeg_lt_neg_iff (ratMul_mem_Rat hb huQ) (ratNeg_mem_Rat hp)).mpr hlt
    rwa [ratNeg_ratNeg hp] at this
  refine ⟨ratNeg u, ratNeg_mem_Rat huQ, ?_, back hc hcu, back hc' hc'u⟩
  have := (ratNeg_lt_neg_iff huQ (ratNeg_mem_Rat hs)).mpr hsu
  rwa [ratNeg_ratNeg hs] at this

/-- Growing the argument while keeping both products below a bound. -/
theorem exists_gt_of_lt_mul₂ {p c c' s : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hc : c ∈ Rat.{u})
    (hc' : c' ∈ Rat.{u}) (hs : s ∈ Rat.{u}) (h : ratLt (ratMul c s) p)
    (h' : ratLt (ratMul c' s) p) :
    ∃ s', s' ∈ Rat.{u} ∧ ratLt s s' ∧ ratLt (ratMul c s') p ∧ ratLt (ratMul c' s') p := by
  have fwd : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt (ratMul b s) p →
      ratLt (ratNeg p) (ratMul b (ratNeg s)) := by
    intro b hb hlt
    rw [ratMul_neg hb hs]
    exact (ratNeg_lt_neg_iff hp (ratMul_mem_Rat hb hs)).mpr hlt
  obtain ⟨u, huQ, hus, hcu, hc'u⟩ := exists_lt_of_mul_lt₂ (ratNeg_mem_Rat hp) hc hc'
    (ratNeg_mem_Rat hs) (fwd hc h) (fwd hc' h')
  have back : ∀ {b : ZFSet.{u}}, b ∈ Rat.{u} → ratLt (ratNeg p) (ratMul b u) →
      ratLt (ratMul b (ratNeg u)) p := by
    intro b hb hlt
    rw [ratMul_neg hb huQ]
    have := (ratNeg_lt_neg_iff (ratMul_mem_Rat hb huQ) (ratNeg_mem_Rat hp)).mpr hlt
    rwa [ratNeg_ratNeg hp] at this
  refine ⟨ratNeg u, ratNeg_mem_Rat huQ, ?_, back hc hcu, back hc' hc'u⟩
  have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hs) huQ).mpr hus
  rwa [ratNeg_ratNeg hs] at this

/-- The smaller of two rationals, as data plus the fact that it is one of them.
`ratLe_total` decides it, so this costs nothing. -/
theorem exists_min_pair {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLe s a ∧ ratLe s b ∧ (s = a ∨ s = b) := by
  rcases ratLe_total ha hb with h | h
  · exact ⟨a, ha, ratLe_refl ha, h, Or.inl rfl⟩
  · exact ⟨b, hb, h, ratLe_refl hb, Or.inr rfl⟩

theorem exists_max_pair {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLe a s ∧ ratLe b s ∧ (s = a ∨ s = b) := by
  rcases ratLe_total ha hb with h | h
  · exact ⟨b, hb, h, ratLe_refl hb, Or.inr rfl⟩
  · exact ⟨a, ha, ratLe_refl ha, h, Or.inl rfl⟩

/-- Transfer a property from four values to whichever of them was chosen. Paired
with `exists_min_four`, this reduces "the bound holds for the least" to a
single line rather than a four-way case split at each use. -/
theorem of_one_of_four {P : ZFSet.{u} → Prop} {w a b c d : ZFSet.{u}}
    (h : w = a ∨ w = b ∨ w = c ∨ w = d) (ha : P a) (hb : P b) (hc : P c) (hd : P d) : P w := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- The least of four, with the witness recorded so a bound proved for each of
the four transfers to it. -/
theorem exists_min_four {a b c d : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hc : c ∈ Rat.{u}) (hd : d ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLe s a ∧ ratLe s b ∧ ratLe s c ∧ ratLe s d ∧
      (s = a ∨ s = b ∨ s = c ∨ s = d) := by
  obtain ⟨u, huQ, hua, hub, hu⟩ := exists_min_pair ha hb
  obtain ⟨v, hvQ, hvc, hvd, hv⟩ := exists_min_pair hc hd
  obtain ⟨s, hsQ, hsu, hsv, hs⟩ := exists_min_pair huQ hvQ
  refine ⟨s, hsQ, ratLe_trans hsQ huQ ha hsu hua, ratLe_trans hsQ huQ hb hsu hub,
    ratLe_trans hsQ hvQ hc hsv hvc, ratLe_trans hsQ hvQ hd hsv hvd, ?_⟩
  rcases hs with rfl | rfl
  · rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_max_four {a b c d : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hc : c ∈ Rat.{u}) (hd : d ∈ Rat.{u}) :
    ∃ s, s ∈ Rat.{u} ∧ ratLe a s ∧ ratLe b s ∧ ratLe c s ∧ ratLe d s ∧
      (s = a ∨ s = b ∨ s = c ∨ s = d) := by
  obtain ⟨u, huQ, hau, hbu, hu⟩ := exists_max_pair ha hb
  obtain ⟨v, hvQ, hcv, hdv, hv⟩ := exists_max_pair hc hd
  obtain ⟨s, hsQ, hus, hvs, hs⟩ := exists_max_pair huQ hvQ
  refine ⟨s, hsQ, ratLe_trans ha huQ hsQ hau hus, ratLe_trans hb huQ hsQ hbu hus,
    ratLe_trans hc hvQ hsQ hcv hvs, ratLe_trans hd hvQ hsQ hdv hvs, ?_⟩
  rcases hs with rfl | rfl
  · rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## Scales for the unit law

Given `p < q`, a scale on each side of `1` that keeps `q · scale` above `p`.
Trichotomy on `q` -- a rational, so free -- splits into the three cases the two
`exists_scale_*_one` lemmas and `corner_above_of_neg` cover between them. -/

theorem exists_scale_below {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hpq : ratLt p q) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt ratZero.{u} r ∧ ratLt r ratOne.{u} ∧ ratLt p (ratMul q r) := by
  obtain ⟨r₀, hr₀Q, h0r₀, hr₀1⟩ := rat_dense ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  have neg : ratLt q ratZero.{u} ∨ q = ratZero.{u} →
      ∃ r, r ∈ Rat.{u} ∧ ratLt ratZero.{u} r ∧ ratLt r ratOne.{u} ∧ ratLt p (ratMul q r) := by
    intro h
    have hp0 : ratLt p ratZero.{u} := by
      rcases h with h | rfl
      · exact ratLt_trans hp hq ratZero_mem_Rat hpq h
      · exact hpq
    exact ⟨r₀, hr₀Q, h0r₀, hr₀1, corner_above_of_neg hp hq hr₀Q hp0 h0r₀ hr₀1 hpq⟩
  rcases ratLt_trichotomy hq ratZero_mem_Rat with h | h | h
  · exact neg (Or.inl h)
  · exact neg (Or.inr h)
  · obtain ⟨r, hrQ, hr1, hqr⟩ := exists_scale_below_one hp hq hpq h
    -- raising the scale only helps when `q > 0`, so take the larger of `r`, `r₀`
    rcases ratLe_total hrQ hr₀Q with hle | hle
    · refine ⟨r₀, hr₀Q, h0r₀, hr₀1, ratLt_of_lt_of_le hp (ratMul_mem_Rat hq hrQ)
        (ratMul_mem_Rat hq hr₀Q) hqr ?_⟩
      have := ratMul_le_mul_right hrQ hr₀Q hq hle h.left
      rwa [ratMul_comm hrQ hq, ratMul_comm hr₀Q hq] at this
    · exact ⟨r, hrQ, ratLt_of_lt_of_le ratZero_mem_Rat hr₀Q hrQ h0r₀ hle, hr1, hqr⟩

theorem exists_scale_above {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hpq : ratLt p q) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt ratOne.{u} r ∧ ratLt p (ratMul q r) := by
  have nonneg : ratLe ratZero.{u} q →
      ∃ r, r ∈ Rat.{u} ∧ ratLt ratOne.{u} r ∧ ratLt p (ratMul q r) := by
    intro h0q
    obtain ⟨r, hrQ, h1r⟩ := rat_no_greatest ratOne_mem_Rat
    refine ⟨r, hrQ, h1r, ratLt_of_lt_of_le hp hq (ratMul_mem_Rat hq hrQ) hpq ?_⟩
    have := ratMul_le_mul_right ratOne_mem_Rat hrQ hq h1r.left h0q
    rwa [ratMul_comm ratOne_mem_Rat hq, ratMul_comm hrQ hq, ratMul_one hq] at this
  rcases ratLt_trichotomy hq ratZero_mem_Rat with h | rfl | h
  · exact exists_scale_above_one hp hq hpq h
  · exact nonneg (ratLe_refl ratZero_mem_Rat)
  · exact nonneg h.left

/-- The upper-side mirrors, by negation rather than a second proof: `w < p` is
`-p < -w`, and `w · r < p` is `-p < (-w) · r`. -/
theorem exists_scale_below_upper {p w : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hw : w ∈ Rat.{u})
    (hwp : ratLt w p) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt ratZero.{u} r ∧ ratLt r ratOne.{u} ∧ ratLt (ratMul w r) p := by
  obtain ⟨r, hrQ, h0r, hr1, hlt⟩ := exists_scale_below (ratNeg_mem_Rat hp)
    (ratNeg_mem_Rat hw) ((ratNeg_lt_neg_iff hp hw).mpr hwp)
  refine ⟨r, hrQ, h0r, hr1, ?_⟩
  rw [ratMul_comm (ratNeg_mem_Rat hw) hrQ, ratMul_neg hrQ hw,
    ratMul_comm hrQ hw] at hlt
  exact (ratNeg_lt_neg_iff hp (ratMul_mem_Rat hw hrQ)).mp hlt

theorem exists_scale_above_upper {p w : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hw : w ∈ Rat.{u})
    (hwp : ratLt w p) :
    ∃ r, r ∈ Rat.{u} ∧ ratLt ratOne.{u} r ∧ ratLt (ratMul w r) p := by
  obtain ⟨r, hrQ, h1r, hlt⟩ := exists_scale_above (ratNeg_mem_Rat hp)
    (ratNeg_mem_Rat hw) ((ratNeg_lt_neg_iff hp hw).mpr hwp)
  refine ⟨r, hrQ, h1r, ?_⟩
  rw [ratMul_comm (ratNeg_mem_Rat hw) hrQ, ratMul_neg hrQ hw,
    ratMul_comm hrQ hw] at hlt
  exact (ratNeg_lt_neg_iff hp (ratMul_mem_Rat hw hrQ)).mp hlt

/-! ## Naturals as rationals

`ratNat p q` is `p/q`; the `intOfNat` arithmetic it rests on is in
`Integer.lean`. Transporting these facts is what lets every later inequality be
a `Nat` inequality. -/

/-- The rational `p/q`. -/
def ratNat (p q : Nat) : ZFSet.{u} := ratOf (intOfNat.{u} p) (intOfNat.{u} q)

theorem ratNat_mem_Rat {p q : Nat} (hq : 0 < q) : ratNat.{u} p q ∈ Rat.{u} :=
  ratOf_mem_Rat (intOfNat_mem_Int p) (intOfNat_mem_intPositive hq)

theorem ratNat_le_iff {p q r s : Nat} (hq : 0 < q) (hs : 0 < s) :
    ratLe (ratNat.{u} p q) (ratNat.{u} r s) ↔ p * s ≤ r * q := by
  rw [ratNat, ratNat, ratLe_ratOf (intOfNat_mem_Int p) (intOfNat_mem_intPositive hq)
    (intOfNat_mem_Int r) (intOfNat_mem_intPositive hs), intOfNat_mul, intOfNat_mul,
    intOfNat_le_iff]

theorem ratNat_eq_iff {p q r s : Nat} (hq : 0 < q) (hs : 0 < s) :
    ratNat.{u} p q = ratNat.{u} r s ↔ p * s = r * q := by
  rw [ratNat, ratNat, ratOf_eq_ratOf_iff (intOfNat_mem_Int p) (intOfNat_mem_intPositive hq)
    (intOfNat_mem_Int r) (intOfNat_mem_intPositive hs), intOfNat_mul, intOfNat_mul,
    intOfNat_eq_iff]

theorem ratNat_lt_iff {p q r s : Nat} (hq : 0 < q) (hs : 0 < s) :
    ratLt (ratNat.{u} p q) (ratNat.{u} r s) ↔ p * s < r * q := by
  rw [ratLt, ratNat_le_iff hq hs]
  constructor
  · rintro ⟨hle, hne⟩
    exact Nat.lt_of_le_of_ne hle (fun he => hne ((ratNat_eq_iff hq hs).mpr he))
  · intro h
    exact ⟨Nat.le_of_lt h, fun he => Nat.ne_of_lt h ((ratNat_eq_iff hq hs).mp he)⟩

/-- The width of `[p/q, (p+1)/q]`, as a rational in the same form. -/
theorem ratNat_width {p q : Nat} (hq : 0 < q) :
    ratAdd (ratNat.{u} (p + 1) q) (ratNeg (ratNat.{u} p q)) = ratNat.{u} 1 q := by
  have hqP : intOfNat.{u} q ∈ intPositive.{u} := intOfNat_mem_intPositive hq
  have hqI := intPositive_subset _ hqP
  rw [ratNat, ratNat, ratNat, ratNeg_ratOf (intOfNat_mem_Int p) hqP,
    ratAdd_ratOf (intOfNat_mem_Int (p + 1)) hqP (intNeg_mem_Int (intOfNat_mem_Int p)) hqP,
    ← intAdd_mul (intOfNat_mem_Int (p + 1)) (intNeg_mem_Int (intOfNat_mem_Int p)) hqI,
    intOfNat_sub (p + 1) p (by omega)]
  have h1 : (p + 1) - p = 1 := by omega
  rw [h1, ratOf_eq_ratOf_iff (intMul_mem_Int (intOfNat_mem_Int 1) hqI)
    (intMul_mem_intPositive hqP hqP) (intOfNat_mem_Int 1) hqP, intOfNat_mul,
    intOfNat_mul, intOfNat_mul, intOfNat_mul, intOfNat_eq_iff]
  rw [Nat.one_mul, Nat.one_mul]

theorem ratZero_eq_ratNat : ratZero.{u} = ratNat.{u} 0 1 := rfl

/-! ## The integers inside the rationals

`intToRat` names the map `a ↦ a/1`.  The pattern `ratOf c intOne` is written
out at twenty-two sites in `Field.lean` and `GeomTower.lean`; naming it buys
the two homomorphism laws once instead of re-deriving them from
`ratAdd_ratOf`/`ratMul_ratOf` at each use. -/

/-- The integers inside the rationals: `a` goes to the class of `a/1`. -/
def intToRat (a : ZFSet.{u}) : ZFSet.{u} := ratOf a intOne.{u}

theorem intToRat_mem_Rat {a : ZFSet.{u}} (ha : a ∈ Int.{u}) :
    intToRat a ∈ Rat.{u} :=
  ratOf_mem_Rat ha one_mem_intPositive

theorem intToRat_add {a c : ZFSet.{u}} (ha : a ∈ Int.{u}) (hc : c ∈ Int.{u}) :
    ratAdd (intToRat a) (intToRat c) = intToRat (intAdd a c) := by
  unfold intToRat
  rw [ratAdd_ratOf ha one_mem_intPositive hc one_mem_intPositive,
      intMul_one ha, intMul_one hc, intMul_one intOne_mem_Int]

theorem intToRat_mul {a c : ZFSet.{u}} (ha : a ∈ Int.{u}) (hc : c ∈ Int.{u}) :
    ratMul (intToRat a) (intToRat c) = intToRat (intMul a c) := by
  unfold intToRat
  rw [ratMul_ratOf ha one_mem_intPositive hc one_mem_intPositive,
      intMul_one intOne_mem_Int]

/-- One denominator cleared. A rational becomes an integer after
multiplication by a positive integer.

Stated as an EXISTENTIAL: naming the denominator as DATA would extract a
witness from `mem_Rat_iff` and cost `Classical.choice`; here every extraction
happens inside a proof, where it is free. -/
theorem exists_clear_denom {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ∃ n, n ∈ intPositive.{u} ∧ ∃ a, a ∈ Int.{u} ∧
      ratMul (intToRat n) r = intToRat a := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff r).mp hr
  have hbI : b ∈ Int.{u} := intPositive_subset _ hb
  refine ⟨b, hb, a, ha, ?_⟩
  unfold intToRat
  rw [ratMul_ratOf hbI one_mem_intPositive ha hb]
  refine (ratOf_eq_ratOf_iff (intMul_mem_Int hbI ha)
    (intMul_mem_intPositive one_mem_intPositive hb) ha one_mem_intPositive).mpr ?_
  rw [intMul_one (intMul_mem_Int hbI ha), intMul_comm intOne_mem_Int hbI,
      intMul_one hbI, intMul_comm hbI ha]

/-- A common denominator for finitely many rationals, by induction on the
bound.  Every extraction stays inside the proof, so the whole construction is
choice-free -- this is the statement `polyMap` needs in order to carry an
integer polynomial's factorisation back from `Q[x]`. -/
theorem exists_common_denom {T : Nat → ZFSet.{u}} :
    ∀ d : Nat, (∀ i : Nat, i < d → T i ∈ Rat.{u}) →
      ∃ n, n ∈ intPositive.{u} ∧
        ∀ i : Nat, i < d → ∃ a, a ∈ Int.{u} ∧
          ratMul (intToRat n) (T i) = intToRat a := by
  intro d
  induction d with
  | zero =>
      intro _
      exact ⟨intOne.{u}, one_mem_intPositive, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
      intro hmem
      obtain ⟨n, hn, hall⟩ := ih (fun i hi => hmem i (Nat.lt_succ_of_lt hi))
      obtain ⟨m, hm, c, hc, hmc⟩ := exists_clear_denom (hmem k (Nat.lt_succ_self k))
      refine ⟨intMul n m, intMul_mem_intPositive hn hm, ?_⟩
      intro i hi
      have hnI : n ∈ Int.{u} := intPositive_subset _ hn
      have hmI : m ∈ Int.{u} := intPositive_subset _ hm
      have hnR : intToRat n ∈ Rat.{u} := intToRat_mem_Rat hnI
      have hmR : intToRat m ∈ Rat.{u} := intToRat_mem_Rat hmI
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨a, ha, hai⟩ := hall i hik
        refine ⟨intMul m a, intMul_mem_Int hmI ha, ?_⟩
        rw [← intToRat_mul hmI ha, ← hai,
            ← ratMul_assoc hmR hnR (hmem i (Nat.lt_succ_of_lt hik)),
            ratMul_comm hmR hnR, intToRat_mul hnI hmI]
      · have hik' : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hik
        subst hik'
        refine ⟨intMul n c, intMul_mem_Int hnI hc, ?_⟩
        rw [← intToRat_mul hnI hc, ← hmc,
            ← ratMul_assoc hnR hmR (hmem i (Nat.lt_succ_self i)),
            intToRat_mul hnI hmI]

/-- The map `Z -> Q` is injective.  What makes the cleared polynomial
definable by SEPARATION rather than by choosing a numerator for each
coefficient: the graph `{(i,a) : N * F i = intToRat a}` is single-valued
because of this, so it is a function without any witness being named. -/
theorem intToRat_inj {a c : ZFSet.{u}} (ha : a ∈ Int.{u}) (hc : c ∈ Int.{u})
    (h : intToRat a = intToRat c) : a = c := by
  unfold intToRat at h
  have := (ratOf_eq_ratOf_iff ha one_mem_intPositive hc one_mem_intPositive).mp h
  rw [intMul_one ha, intMul_one hc] at this
  exact this

/-- The partial inverse of `intToRat`, as a definite description.

`theOnly` carves the numerator out of the class: `a/1` is the class holding
`opair a intOne`, and the cross-multiplication in `mem_ratOf_iff` forces that
element to be unique, so the integer is NAMED rather than chosen. A cleared
polynomial is therefore built by `polyOfSeq` with no witness selected. -/
def intOfRat (r : ZFSet.{u}) : ZFSet.{u} :=
  theOnly (fun x => opair x intOne.{u} ∈ r) Int.{u}

theorem intOfRat_intToRat {a : ZFSet.{u}} (ha : a ∈ Int.{u}) :
    intOfRat (intToRat a) = a := by
  refine theOnly_eq ha ?_ ?_
  · refine (mem_ratOf_iff ha one_mem_intPositive _).mpr
      ⟨a, ha, intOne.{u}, one_mem_intPositive, rfl, rfl⟩
  · intro b hb hmem
    obtain ⟨x, hx, y, hy, hpair, hcross⟩ :=
      (mem_ratOf_iff ha one_mem_intPositive _).mp hmem
    obtain ⟨rfl, rfl⟩ := opair_injective hpair
    rw [intMul_one ha, intMul_one hx] at hcross
    exact hcross.symm

/-- The description lands in `Int` whenever the rational really is an integer.
The hypothesis is existential, so the witness is taken inside this proof and
costs nothing. -/
theorem intOfRat_mem {r : ZFSet.{u}} (h : ∃ a, a ∈ Int.{u} ∧ r = intToRat a) :
    intOfRat r ∈ Int.{u} := by
  obtain ⟨a, ha, rfl⟩ := h
  rw [intOfRat_intToRat ha]
  exact ha

/-- The round trip, the other way.  This is the step the cleared polynomial
needs: its coefficients are `intOfRat` of something known to be an integer, and
mapping them back reproduces the rational. -/
theorem intToRat_intOfRat {r : ZFSet.{u}} (h : ∃ a, a ∈ Int.{u} ∧ r = intToRat a) :
    intToRat (intOfRat r) = r := by
  obtain ⟨a, ha, rfl⟩ := h
  rw [intOfRat_intToRat ha]

#print axioms ratRel_isEquivRel
#print axioms ratOf_eq_ratOf_iff
#print axioms ratNat_eq_iff
#print axioms ratNat_le_iff
#print axioms mem_Rat_iff
#print axioms ratAdd_ratOf
#print axioms intToRat
#print axioms intToRat_mem_Rat

#print axioms intToRat_add
#print axioms intToRat_mul
#print axioms exists_clear_denom
#print axioms exists_common_denom
#print axioms intToRat_inj
#print axioms intOfRat
#print axioms intOfRat_intToRat
#print axioms intOfRat_mem
#print axioms intToRat_intOfRat
#print axioms ratAdd_assoc
#print axioms ratAdd_neg
#print axioms ratMul_ratOf
#print axioms ratMul_assoc
#print axioms ratMul_add
#print axioms ratMul_inv
#print axioms ratAdd_le_add_left_iff
#print axioms ratMul_le_mul_right
#print axioms ratLe_ratOf
#print axioms ratLe_trans
#print axioms ratLe_antisymm
#print axioms ratLe_total
#print axioms rat_dense
#print axioms rat_no_greatest
#print axioms rat_no_least
#print axioms ratLt_trichotomy
#print axioms corner_le_mul
#print axioms mul_le_corner
#print axioms ratInv_pos
#print axioms mul_le_of_bounds
#print axioms mul_shift_le
#print axioms corner_close
#print axioms ratLt_mul_of_corners
#print axioms ratMul_lt_of_corners
#print axioms exists_scale_below_one
#print axioms exists_scale_above_one
#print axioms corner_above_of_neg
#print axioms exists_scale_below
#print axioms exists_scale_above
#print axioms exists_scale_below_upper
#print axioms exists_scale_above_upper
#print axioms ratInv_neg
#print axioms exists_small_scale
#print axioms small_scale_mono
#print axioms exists_lt_of_mul_lt₂
#print axioms lt_mul_add_of_lt
#print axioms exists_gt_of_mul_lt₂
#print axioms mul_add_lt_of_lt
#print axioms exists_lt_of_lt_mul₂
#print axioms exists_gt_of_lt_mul₂
#print axioms of_one_of_four
#print axioms exists_min_four
#print axioms exists_max_four
#print axioms ratMul_lt_mul_right_of_nonpos

/-! ### Powers -/

/-- `0/q` is zero. MOVED here from `Omniscience.lean`, which is downstream and
could not lend it to the Archimedean step below; the proof is that file's. -/
theorem ratNat_zero {q : Nat} (hq : 0 < q) : ratNat.{u} 0 q = ratZero.{u} := by
  rw [ratZero_eq_ratNat, ratNat_eq_iff hq (by omega)]
  omega

#print axioms ratNat_zero
def ratTwo : ZFSet.{u} := ratAdd ratOne.{u} ratOne.{u}

/-- Halfway between two rationals. -/
def ratMid (a b : ZFSet.{u}) : ZFSet.{u} :=
  ratMul (ratAdd a b) (ratInv ratTwo.{u})

def invWidth (n : ZFSet.{u}) : ZFSet.{u} := ratOf intOne.{u} (intOf (succ n) empty.{u})

theorem invWidth_mem_Rat {n : ZFSet.{u}} (hn : n ∈ omega.{u}) : invWidth n ∈ Rat.{u} :=
  ratOf_mem_Rat intOne_mem_Int (intOf_succ_pos hn)

theorem invWidth_pos {n : ZFSet.{u}} (hn : n ∈ omega.{u}) :
    ratLt ratZero.{u} (invWidth n) := ratOf_one_pos (intOf_succ_pos hn)

/-- The width at a numeral index, as a ratio of naturals. -/
theorem invWidth_ofNat (n : Nat) : invWidth (ofNat.{u} n) = ratNat.{u} 1 (n + 1) := by
  rw [invWidth, ratNat, ← ofNat_succ n]
  rfl

/-- Archimedes, in the form the widths need: some `1/(N+1)` is below any given
positive rational. -/
theorem exists_invWidth_lt {ε : ZFSet.{u}} (hεQ : ε ∈ Rat.{u})
    (hε : ratLt ratZero.{u} ε) : ∃ N, N ∈ omega.{u} ∧ ratLt (invWidth N) ε := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff ε).mp hεQ
  have haP := intPositive_num ha hb hε
  have haI := intPositive_subset _ haP
  have hbI := intPositive_subset _ hb
  -- a natural `n` with `b ≤ n` and `b ≠ n`
  obtain ⟨n, hle, hne⟩ := int_lt_intOfNat_mul hbI one_mem_intPositive
  rw [intMul_one (intOfNat_mem_Int n)] at hle hne
  refine ⟨ofNat.{u} n, ofNat_mem_omega n, ?_⟩
  have hdP := intOf_succ_pos (ofNat_mem_omega n)
  have hdI := intPositive_subset _ hdP
  have hnd : intLe (intOfNat.{u} n) (intOf (succ (ofNat.{u} n)) empty.{u}) := by
    rw [intOfNat, ← ofNat_succ, ← ofNat_zero, intLe_ofNat]
    omega
  have hda : intLe (intOf (succ (ofNat.{u} n)) empty.{u})
      (intMul a (intOf (succ (ofNat.{u} n)) empty.{u})) := by
    have hm := intMul_le_mul_right intOne_mem_Int haI hdI
      (intZero_le_of_intPositive hdP) (intOne_le_of_intPositive haP)
    rwa [intOne_mul hdI] at hm
  have hchain : intLe (intOfNat.{u} n) (intMul a (intOf (succ (ofNat.{u} n)) empty.{u})) :=
    intLe_trans (intOfNat_mem_Int n) hdI (intMul_mem_Int haI hdI) hnd hda
  refine (ratLt_ratOf intOne_mem_Int hdP ha hb).mpr ⟨?_, ?_⟩
  · rw [intOne_mul hbI]
    exact intLe_trans hbI (intOfNat_mem_Int n) (intMul_mem_Int haI hdI) hle hchain
  · rw [intOne_mul hbI]
    intro heq
    refine hne (intLe_antisymm hbI (intOfNat_mem_Int n) hle ?_)
    rw [heq]
    exact hchain

#print axioms ratTwo
#print axioms ratMid
#print axioms invWidth
#print axioms invWidth_mem_Rat
#print axioms invWidth_pos
#print axioms invWidth_ofNat
#print axioms exists_invWidth_lt

end NumberTheory

namespace ZFSet
export NumberTheory (Rat corner_above_of_neg corner_close corner_le_mul diff_bounds diff_self_bounds exists_between_two exists_between_two' exists_clear_denom exists_common_denom exists_gt_of_lt_mul₂ exists_gt_of_mul_lt₂ exists_gt_two exists_invWidth_lt exists_lt_of_lt_mul₂ exists_lt_of_mul_lt₂ exists_lt_two exists_max_four exists_max_pair exists_min_four exists_min_pair exists_mul_lt exists_scale_above exists_scale_above_one exists_scale_above_upper exists_scale_below exists_scale_below_one exists_scale_below_upper exists_small_scale intOfRat intOfRat_intToRat intOfRat_mem intPositive_num intToRat intToRat_add intToRat_inj intToRat_intOfRat intToRat_mem_Rat intToRat_mul invWidth invWidth_mem_Rat invWidth_ofNat invWidth_pos lt_mul_add_of_lt mem_Rat_iff mem_ratOf_iff mem_ratPairs_iff mem_ratRel_iff mul_add_lt_of_lt mul_le_corner mul_le_of_bounds mul_shift_le neg_le_sub_iff_le_add num_ne_zero of_one_of_four ratAdd ratAdd_assoc ratAdd_comm ratAdd_le_add_left_iff ratAdd_le_add_right_iff ratAdd_left_cancel ratAdd_lt_add ratAdd_lt_add_left_iff ratAdd_lt_add_right_iff ratAdd_mem_Rat ratAdd_mul ratAdd_neg ratAdd_ratOf ratAdd_sub_cancel ratAdd_zero ratInv ratInv_mem_Rat ratInv_neg ratInv_pos ratInv_ratOf ratLe ratLe_antisymm ratLe_ratOf ratLe_refl ratLe_total ratLe_trans ratLt ratLt_irrefl ratLt_mul_of_corners ratLt_of_le_of_lt ratLt_of_lt_of_le ratLt_ratOf ratLt_trans ratLt_trichotomy ratMid ratMul ratMul_add ratMul_assoc ratMul_comm ratMul_inv ratMul_le_mul_right ratMul_le_mul_right_of_nonpos ratMul_left_cancel ratMul_lt_mul_right ratMul_lt_mul_right_of_nonpos ratMul_lt_of_corners ratMul_mem_Rat ratMul_neg ratMul_one ratMul_ratOf ratMul_zero ratNat ratNat_eq_iff ratNat_le_iff ratNat_lt_iff ratNat_mem_Rat ratNat_width ratNat_zero ratNeg ratNeg_injective ratNeg_le_neg_iff ratNeg_lt_neg_iff ratNeg_mem_Rat ratNeg_ratNeg ratNeg_ratOf ratNeg_zero ratOf ratOf_add_congr ratOf_add_same_denom ratOf_cancel ratOf_eq_ratOf_iff ratOf_intOfNat_succ ratOf_intZero ratOf_mem_Rat ratOf_mul_congr ratOf_neg_congr ratOf_one_le ratOf_one_pos ratOf_subset ratOne ratOne_mem_Rat ratOne_mul ratPairs ratRel ratRel_isEquivRel ratTwo ratZero ratZero_add ratZero_eq_ratNat ratZero_lt_one ratZero_mem_Rat ratZero_mul rat_archimedean rat_dense rat_eq_or_ne rat_no_greatest rat_no_least small_scale_mono sub_add_cancel sub_le_iff_le_add sub_lt_iff_lt_add)
end ZFSet
