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

#print axioms ratRel_isEquivRel
#print axioms ratOf_eq_ratOf_iff
#print axioms mem_Rat_iff
#print axioms ratAdd_ratOf
#print axioms ratAdd_assoc
#print axioms ratAdd_neg
#print axioms ratMul_ratOf
#print axioms ratMul_assoc
end NumberTheory

namespace ZFSet
export NumberTheory (Rat mem_Rat_iff mem_ratOf_iff mem_ratPairs_iff mem_ratRel_iff ratAdd ratAdd_assoc ratAdd_comm ratAdd_mem_Rat ratAdd_neg ratAdd_ratOf ratAdd_zero ratMul ratMul_assoc ratMul_comm ratMul_mem_Rat ratMul_ratOf ratNeg ratNeg_mem_Rat ratNeg_ratOf ratOf ratOf_add_congr ratOf_cancel ratOf_eq_ratOf_iff ratOf_mem_Rat ratOf_mul_congr ratOf_neg_congr ratOf_subset ratOne ratPairs ratRel ratRel_isEquivRel ratZero ratZero_mem_Rat)
end ZFSet
