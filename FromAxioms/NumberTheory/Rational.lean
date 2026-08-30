/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The rationals.

`ℚ` is `ℤ × ℤ_{>0}` modulo `(a,b) ~ (c,d) ↔ a·d = c·b`.

Denominators are strictly positive, not merely nonzero. With arbitrary nonzero
denominators every rational has two representations of opposite sign, and the
order `a/b ≤ c/d ↔ a·d ≤ c·b` then needs a case split on the sign of `b·d`.
Restricting to positive denominators removes the case split, which is what makes
the order on ℚ -- and hence Dedekind cuts -- tractable.

Transitivity is where ℤ has to be a domain: from `a·d = c·b` and `c·f = e·d`
one reaches `d·(a·f) = d·(e·b)` by associativity and commutativity, and then
needs `intMul_left_cancel` to drop the `d`.
-/

import FromAxioms.NumberTheory.Integer

universe u

open SetTheory
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

/-- Cancelling a common positive factor. This is what keeps the distributive law
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

/-- Transitivity is where the denominators have to be cancelled: the two
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

#print axioms ratRel_isEquivRel
#print axioms ratOf_eq_ratOf_iff
#print axioms mem_Rat_iff
#print axioms ratAdd_ratOf
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
#print axioms corner_le_mul
#print axioms mul_le_corner
#print axioms ratMul_lt_mul_right_of_nonpos

end NumberTheory

namespace ZFSet
export NumberTheory (Rat corner_le_mul exists_between_two exists_between_two' exists_gt_two exists_lt_two mem_Rat_iff mem_ratOf_iff mem_ratPairs_iff mem_ratRel_iff mul_le_corner num_ne_zero ratAdd ratAdd_assoc ratAdd_comm ratAdd_le_add_left_iff ratAdd_le_add_right_iff ratAdd_left_cancel ratAdd_lt_add ratAdd_lt_add_left_iff ratAdd_lt_add_right_iff ratAdd_mem_Rat ratAdd_mul ratAdd_neg ratAdd_ratOf ratAdd_sub_cancel ratAdd_zero ratInv ratInv_mem_Rat ratInv_ratOf ratLe ratLe_antisymm ratLe_ratOf ratLe_refl ratLe_total ratLe_trans ratLt ratLt_irrefl ratLt_of_le_of_lt ratLt_of_lt_of_le ratLt_ratOf ratLt_trans ratMul ratMul_add ratMul_assoc ratMul_comm ratMul_inv ratMul_le_mul_right ratMul_le_mul_right_of_nonpos ratMul_left_cancel ratMul_lt_mul_right ratMul_lt_mul_right_of_nonpos ratMul_mem_Rat ratMul_neg ratMul_one ratMul_ratOf ratMul_zero ratNeg ratNeg_injective ratNeg_le_neg_iff ratNeg_lt_neg_iff ratNeg_mem_Rat ratNeg_ratNeg ratNeg_ratOf ratNeg_zero ratOf ratOf_add_congr ratOf_add_same_denom ratOf_cancel ratOf_eq_ratOf_iff ratOf_intOfNat_succ ratOf_intZero ratOf_mem_Rat ratOf_mul_congr ratOf_neg_congr ratOf_one_le ratOf_one_pos ratOf_subset ratOne ratOne_mem_Rat ratOne_mul ratPairs ratRel ratRel_isEquivRel ratZero ratZero_add ratZero_lt_one ratZero_mem_Rat ratZero_mul rat_archimedean rat_dense rat_no_greatest rat_no_least)
end ZFSet
