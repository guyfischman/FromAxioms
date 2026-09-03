/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Comparing sets by size.

    Equinumerous x y   some set function is a bijection x → y
    Dominates x y      some set function is an injection x → y

Both are relations between sets rather than objects of their own. Cardinals *as
objects* need either a well-ordering, which is choice, or Scott's trick, which
needs a least rank and so a comparison of ordinals -- and that comparison is
exactly what excluded middle buys here. The relations, by contrast,
cost nothing, and everything the comparison is used for is available from them.

The two constructions that make the relations work are an inverse and a
composite. Both are `graphOn` of a Lean-level function: composition of the
applications, and for the inverse the unique preimage, extracted by the
⋃-of-a-singleton trick rather than chosen.

Antisymmetry is Schröder--Bernstein, so it inherits `Bernstein.lean`'s
`SBDetachable` hypothesis and nothing more.

The finite product `prodFam C n` of a family nests left, exactly as `powSet`
does, so `equinumerous_powSet`'s induction transplants to count it.
-/

import FromAxioms.Constructive.Reverse
import FromAxioms.Core.NatSearch
import FromAxioms.NumberTheory.Arith
import FromAxioms.SetTheory.Relation

universe u

open Algebra Constructive NumberTheory
namespace SetTheory

/-! ## Identity, composite, inverse

`idOn` and `app_idOn` are `Relation.lean`'s, beside `graphOn` which is all they
mention. What stays here is their theory: injectivity and surjectivity are this
file's subject. -/

theorem graphOn_range {x y : ZFSet.{u}} {F : ZFSet.{u} → ZFSet.{u}} :
    range (graphOn x y F) ⊆ y := by
  intro v hv
  obtain ⟨w, hw⟩ := (mem_range_iff v _).mp hv
  exact mem_prod_right (graphOn_subset x y F _ hw)

theorem isInjection_idOn (x : ZFSet.{u}) : IsInjection (idOn x) x x :=
  ⟨graphOn_isFunction _ _ _, graphOn_domain (fun _ hm => hm), graphOn_range,
   fun a ha b hb he => by rwa [app_idOn ha, app_idOn hb] at he⟩

theorem isSurjection_idOn (x : ZFSet.{u}) : IsSurjection (idOn x) x x :=
  ⟨graphOn_isFunction _ _ _, graphOn_domain (fun _ hm => hm), graphOn_range,
   fun b hb => ⟨b, hb, app_idOn hb⟩⟩

/-- The composite, as the graph of the composed applications. -/
def compOn (g f x z : ZFSet.{u}) : ZFSet.{u} := graphOn x z (fun w => app g (app f w))

theorem app_compOn {g f x y z w : ZFSet.{u}} (hf : IsInjection f x y)
    (hg : IsInjection g y z) (hw : w ∈ x) :
    app (compOn g f x z) w = app g (app f w) := by
  refine app_graphOn (fun m hm => ?_) hw
  refine hg.right.right.left _ (app_mem_range hg.left ?_)
  rw [hg.right.left]
  exact hf.right.right.left _ (app_mem_range hf.left (by rw [hf.right.left]; exact hm))

theorem app_mem_of_isInjection {f x y w : ZFSet.{u}} (hf : IsInjection f x y)
    (hw : w ∈ x) : app f w ∈ y :=
  hf.right.right.left _ (app_mem_range hf.left (by rw [hf.right.left]; exact hw))

theorem isInjection_compOn {g f x y z : ZFSet.{u}} (hf : IsInjection f x y)
    (hg : IsInjection g y z) : IsInjection (compOn g f x z) x z := by
  refine ⟨graphOn_isFunction _ _ _,
    graphOn_domain (fun m hm => app_mem_of_isInjection hg (app_mem_of_isInjection hf hm)),
    graphOn_range, fun a ha b hb he => ?_⟩
  rw [app_compOn hf hg ha, app_compOn hf hg hb] at he
  exact isInjection_inj hf ha hb
    (hg.right.right.right _ (app_mem_of_isInjection hf ha) _
      (app_mem_of_isInjection hf hb) he)

/-- The unique preimage, extracted rather than chosen: `theOnly` at the
predicate sends `w` to `v`, over the domain. Naming it rather than writing the
separation out is what says the extraction is a definite description and not a
choice -- `Algebra.lean`'s docstring makes that argument once, for every site
that cites it. -/
def invApp (f v : ZFSet.{u}) : ZFSet.{u} := theOnly (fun w => app f w = v) (domain f)

theorem invApp_eq {f x y v w : ZFSet.{u}} (hf : IsInjection f x y) (hw : w ∈ x)
    (he : app f w = v) : invApp f v = w := by
  have hsing : sep (fun t => app f t = v) (domain f) = singleton w := by
    refine ext _ _ fun t => ⟨fun ht => ?_, fun ht => ?_⟩
    · obtain ⟨htd, hte⟩ := (mem_sep_iff _ _ _).mp ht
      rw [hf.right.left] at htd
      exact (mem_singleton_iff t w).mpr
        (isInjection_inj hf htd hw (hte.trans he.symm))
    · rw [(mem_singleton_iff t w).mp ht]
      exact (mem_sep_iff _ _ _).mpr ⟨by rw [hf.right.left]; exact hw, he⟩
  rw [invApp, theOnly, hsing, sUnion_singleton]

/-- The inverse of a bijection. -/
def invOn (f x y : ZFSet.{u}) : ZFSet.{u} := graphOn y x (invApp f)

theorem invApp_mem {f x y v : ZFSet.{u}} (hf : IsInjection f x y)
    (hs : IsSurjection f x y) (hv : v ∈ y) : invApp f v ∈ x := by
  obtain ⟨w, hw, he⟩ := isSurjection_onto hs hv
  rw [invApp_eq hf hw he]
  exact hw

theorem app_invOn {f x y v : ZFSet.{u}} (hf : IsInjection f x y)
    (hs : IsSurjection f x y) (hv : v ∈ y) : app (invOn f x y) v = invApp f v :=
  app_graphOn (fun _ hm => invApp_mem hf hs hm) hv

theorem isInjection_invOn {f x y : ZFSet.{u}} (hf : IsInjection f x y)
    (hs : IsSurjection f x y) : IsInjection (invOn f x y) y x := by
  refine ⟨graphOn_isFunction _ _ _,
    graphOn_domain (fun m hm => invApp_mem hf hs hm), graphOn_range,
    fun a ha b hb he => ?_⟩
  rw [app_invOn hf hs ha, app_invOn hf hs hb] at he
  obtain ⟨wa, hwa, hea⟩ := isSurjection_onto hs ha
  obtain ⟨wb, hwb, heb⟩ := isSurjection_onto hs hb
  rw [invApp_eq hf hwa hea, invApp_eq hf hwb heb] at he
  rw [← hea, ← heb, he]

theorem isSurjection_invOn {f x y : ZFSet.{u}} (hf : IsInjection f x y)
    (hs : IsSurjection f x y) : IsSurjection (invOn f x y) y x := by
  refine ⟨graphOn_isFunction _ _ _,
    graphOn_domain (fun m hm => invApp_mem hf hs hm), graphOn_range,
    fun w hw => ?_⟩
  refine ⟨app f w, app_mem_of_isInjection hf hw, ?_⟩
  rw [app_invOn hf hs (app_mem_of_isInjection hf hw), invApp_eq hf hw rfl]

/-! ## The relations -/

def Equinumerous (x y : ZFSet.{u}) : Prop :=
  ∃ f, IsInjection f x y ∧ IsSurjection f x y

def Dominates (x y : ZFSet.{u}) : Prop := ∃ f, IsInjection f x y

theorem equinumerous_refl (x : ZFSet.{u}) : Equinumerous x x :=
  ⟨idOn x, isInjection_idOn x, isSurjection_idOn x⟩

theorem equinumerous_symm {x y : ZFSet.{u}} (h : Equinumerous x y) : Equinumerous y x := by
  obtain ⟨f, hf, hs⟩ := h
  exact ⟨invOn f x y, isInjection_invOn hf hs, isSurjection_invOn hf hs⟩

theorem equinumerous_trans {x y z : ZFSet.{u}} (h₁ : Equinumerous x y)
    (h₂ : Equinumerous y z) : Equinumerous x z := by
  obtain ⟨f, hf, hsf⟩ := h₁
  obtain ⟨g, hg, hsg⟩ := h₂
  refine ⟨compOn g f x z, isInjection_compOn hf hg, ?_⟩
  refine ⟨graphOn_isFunction _ _ _,
    graphOn_domain (fun m hm => app_mem_of_isInjection hg (app_mem_of_isInjection hf hm)),
    graphOn_range, fun v hv => ?_⟩
  obtain ⟨t, ht, het⟩ := isSurjection_onto hsg hv
  obtain ⟨w, hw, hew⟩ := isSurjection_onto hsf ht
  refine ⟨w, hw, ?_⟩
  rw [app_compOn hf hg hw, hew, het]

theorem dominates_trans {x y z : ZFSet.{u}} (h₁ : Dominates x y) (h₂ : Dominates y z) :
    Dominates x z := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨compOn g f x z, isInjection_compOn hf hg⟩

theorem dominates_of_equinumerous {x y : ZFSet.{u}} (h : Equinumerous x y) :
    Dominates x y := by
  obtain ⟨f, hf, -⟩ := h
  exact ⟨f, hf⟩

/-- A counted set with a pointwise dichotomy decides the quantifier.

The hypothesis is `P a ∨ Q a` rather than `P a ∨ ¬ P a`, and that is the
load-bearing choice: a search whose negative branch delivers `¬ P a` delivers
nothing a caller can use, since the caller needs a VALUE. Taking the dichotomy
as the hypothesis makes the negative branch carry information by construction,
and every caller already holds it in that form.

This cannot go through `exists_lt_or_not`, which wants a decidable
predicate: `P a ∨ Q a` does not decide `P a`, because nothing says `Q` refutes
`P`. The induction over the enumeration needs no such hypothesis.

Moved here from `Integral.lean` when the ideal correspondence became a second
caller -- the trigger its own docstring named. It is about sets, not rings. -/
theorem exists_or_all_of_equinumerous {S : ZFSet.{u}} {n : Nat}
    {P Q : ZFSet.{u} → Prop}
    (hS : Equinumerous S (ofNat.{u} n))
    (hpt : ∀ a, a ∈ S → P a ∨ Q a) :
    (∃ a, a ∈ S ∧ P a) ∨ (∀ a, a ∈ S → Q a) := by
  obtain ⟨f, hf, hs⟩ := hS
  have hg : IsSurjection (invOn f S (ofNat.{u} n)) (ofNat.{u} n) S :=
    isSurjection_invOn hf hs
  have hmemS : ∀ k, k < n → app (invOn f S (ofNat.{u} n)) (ofNat.{u} k) ∈ S := by
    intro k hk
    exact app_mem_of_isSurjection hg ((mem_ofNat_iff _ n).mpr ⟨k, hk, rfl⟩)
  have aux : ∀ m : Nat, (∃ a, a ∈ S ∧ P a) ∨
      (∀ k, k < m → k < n → Q (app (invOn f S (ofNat.{u} n)) (ofNat.{u} k))) := by
    intro m
    induction m with
    | zero => exact Or.inr (fun k hk _ => absurd hk (Nat.not_lt_zero k))
    | succ m ih =>
      rcases ih with h | hq
      · exact Or.inl h
      · rcases Nat.lt_or_ge m n with hmn | hmn
        · rcases hpt _ (hmemS m hmn) with hP | hQ
          · exact Or.inl ⟨_, hmemS m hmn, hP⟩
          · refine Or.inr (fun k hk hkn => ?_)
            rcases Nat.lt_or_ge k m with hkm | hkm
            · exact hq k hkm hkn
            · have hkeq : k = m := by omega
              subst hkeq
              exact hQ
        · refine Or.inr (fun k hk hkn => ?_)
          rcases Nat.lt_or_ge k m with hkm | hkm
          · exact hq k hkm hkn
          · exact absurd hkn (by omega)
  rcases aux n with h | hq
  · exact Or.inl h
  · refine Or.inr (fun a ha => ?_)
    obtain ⟨m, hm, hma⟩ := hg.right.right.right a ha
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff m n).mp hm
    exact hma ▸ hq k hk hk

#print axioms exists_or_all_of_equinumerous

/-- Finite: in bijection with a numeral. The first finiteness notion in the
development, and it needs nothing new -- `Equinumerous` and `ofNat` were both
already here. -/
def IsFinite (x : ZFSet.{u}) : Prop := ∃ n : Nat, Equinumerous x (ofNat.{u} n)

theorem isFinite_ofNat (n : Nat) : IsFinite (ofNat.{u} n) :=
  ⟨n, equinumerous_refl _⟩

/-! ## Finite choice

Every family of inhabited sets indexed by a numeral has a choice function, and
this is a theorem, not an assumption: the hypothesis and the conclusion are
both `Prop`s, so eliminating the existential at each stage is ordinary
reasoning. The induction is on the numeral, and the function is built one pair
at a time.

This is the constructive content behind "finite choice is free", and what a
counting argument like Lagrange's needs, where the family is the cosets and a
representative has to be picked in each. -/

/-- Products respect equinumerosity, componentwise. -/
theorem equinumerous_prod {x y x' y' : ZFSet.{u}} (hx : Equinumerous x x')
    (hy : Equinumerous y y') : Equinumerous (prod x y) (prod x' y') := by
  obtain ⟨f, hf, hfs⟩ := hx
  obtain ⟨g, hg, hgs⟩ := hy
  have hmaps : ∀ p, p ∈ prod x y →
      opair (app f (fst p)) (app g (snd p)) ∈ prod x' y' := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p x y).mp hp
    rw [fst_opair, snd_opair]
    exact opair_mem_prod (app_mem_of_isInjection hf ha) (app_mem_of_isInjection hg hb)
  have happ : ∀ a, a ∈ x → ∀ b, b ∈ y →
      app (graphOn (prod x y) (prod x' y') (fun p => opair (app f (fst p)) (app g (snd p))))
        (opair a b) = opair (app f a) (app g b) := by
    intro a ha b hb
    rw [app_graphOn hmaps (opair_mem_prod ha hb), fst_opair, snd_opair]
  refine ⟨_, ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩⟩
  · intro p hp p' hp' he
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p x y).mp hp
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_prod_iff p' x y).mp hp'
    rw [happ a ha b hb, happ a' ha' b' hb'] at he
    obtain ⟨hfa, hgb⟩ := opair_injective he
    rw [isInjection_inj hf ha ha' hfa, isInjection_inj hg hb hb' hgb]
  · intro q hq
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_prod_iff q x' y').mp hq
    obtain ⟨a, ha, rfl⟩ := isSurjection_onto hfs ha'
    obtain ⟨b, hb, rfl⟩ := isSurjection_onto hgs hb'
    exact ⟨opair a b, opair_mem_prod ha hb, happ a ha b hb⟩

/-! ## What finiteness is not closed under

Lagrange has to assume that there are finitely many cosets rather than deriving
it: "every subset of a finite set is finite" implies excluded middle.
Deciding how many elements `{z ∈ {∅} | p}` has decides `p`.

What survives constructively is domination: a subset of a finite set is
subfinite, injected into a numeral, which is enough for bounds but not for a
count. -/

theorem dominates_ofNat_of_subset {x y : ZFSet.{u}} {n : Nat} (hsub : x ⊆ y)
    (hy : Equinumerous y (ofNat.{u} n)) : Dominates x (ofNat.{u} n) := by
  obtain ⟨f, hf, -⟩ := hy
  have hmaps : ∀ a, a ∈ x → app f a ∈ ofNat.{u} n := fun a ha =>
    app_mem_of_isInjection hf (hsub a ha)
  refine ⟨graphOn x (ofNat.{u} n) (app f), graphOn_isFunction _ _ _,
    graphOn_domain hmaps, graphOn_range, fun a ha b hb he => ?_⟩
  rw [app_graphOn hmaps ha, app_graphOn hmaps hb] at he
  exact isInjection_inj hf (hsub a ha) (hsub b hb) he

/-- The closure principle, named so the audit can measure it. -/
def SubsetFinite : Prop := ∀ x y : ZFSet.{u}, x ⊆ y → IsFinite y → IsFinite x

/-- Finiteness is not closed under subsets, constructively: the closure
principle implies excluded middle. -/
theorem em_of_subset_finite (h : SubsetFinite.{u}) : EM := by
  intro p
  -- `{z ∈ 1 | p}` is a subset of a one-element set
  have hsub : sep (fun _ => p) (ofNat.{u} 1) ⊆ ofNat.{u} 1 :=
    fun w hw => ((mem_sep_iff _ w _).mp hw).left
  obtain ⟨m, g, hg, hgs⟩ := h _ _ hsub (isFinite_ofNat 1)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- no elements, so `p` fails
    refine Or.inr fun hp => ?_
    have hmem : empty.{u} ∈ sep (fun _ => p) (ofNat.{u} 1) :=
      (mem_sep_iff _ _ _).mpr ⟨mem_succ_self empty.{u}, hp⟩
    have := app_mem_of_isInjection hg hmem
    rw [ofNat_zero] at this
    exact not_mem_empty _ this
  · -- an element, and its defining property is `p`
    obtain ⟨a, ha, -⟩ := isSurjection_onto hgs (by
      rcases (mem_ofNat_iff empty.{u} m).mpr ⟨0, hm, (ofNat_zero).symm⟩ with h'
      exact h')
    exact Or.inl ((mem_sep_iff _ a _).mp ha).right

/-! ## Bijection surgery

Two manipulations every counting argument needs: remove the point that maps to
the last numeral, and extend by a point. With them, and with equality on a
finite set being decidable, a detachable subset of a finite set is finite --
which is the constructive form of the closure that `em_of_subset_finite`
refutes in general. -/

/-- Equality on a finite set is decidable, because equality of numerals is. -/
theorem eq_or_ne_of_finite {y : ZFSet.{u}} {n : Nat} (hy : Equinumerous y (ofNat.{u} n))
    {a b : ZFSet.{u}} (ha : a ∈ y) (hb : b ∈ y) : a = b ∨ a ≠ b := by
  obtain ⟨f, hf, -⟩ := hy
  obtain ⟨i, -, hi⟩ := (mem_ofNat_iff _ n).mp (app_mem_of_isInjection hf ha)
  obtain ⟨j, -, hj⟩ := (mem_ofNat_iff _ n).mp (app_mem_of_isInjection hf hb)
  rcases Nat.decEq i j with hne | rfl
  · refine Or.inr fun he => hne ?_
    rw [he] at hi
    exact ofNat_injective (hi.symm.trans hj)
  · exact Or.inl (isInjection_inj hf ha hb (hi.trans hj.symm))

/-- A member can be stripped and put back. The decision separating `a` from the rest
of `x` comes from finiteness of an ambient `y`, not from `em`. -/
theorem sdiff_singleton_union {x y a : ZFSet.{u}} {n : Nat}
    (hy : Equinumerous y (ofNat.{u} n)) (hsub : ∀ w, w ∈ x → w ∈ y)
    (hay : a ∈ y) (hax : a ∈ x) : x = (x \ singleton a) ∪ singleton a := by
  refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · rcases eq_or_ne_of_finite hy (hsub w hw) hay with rfl | hne
    · exact (mem_union_iff _ _ _).mpr (Or.inr ((mem_singleton_iff _ _).mpr rfl))
    · exact (mem_union_iff _ _ _).mpr (Or.inl ((mem_sdiff_iff _ _ _).mpr
        ⟨hw, fun hmem => hne ((mem_singleton_iff _ _).mp hmem)⟩))
  · rcases (mem_union_iff _ _ _).mp hw with h | h
    · exact ((mem_sdiff_iff _ _ _).mp h).left
    · rw [(mem_singleton_iff _ _).mp h]
      exact hax

/-- Removing the point that maps to the last numeral. -/
theorem equinumerous_erase {y : ZFSet.{u}} {n : Nat} {f : ZFSet.{u}}
    (hf : IsInjection f y (ofNat.{u} (n + 1))) (hs : IsSurjection f y (ofNat.{u} (n + 1))) :
    Equinumerous (y \ singleton (invApp f (ofNat.{u} n))) (ofNat.{u} n) := by
  have hlast : ofNat.{u} n ∈ ofNat.{u} (n + 1) := by
    rw [ofNat_succ]
    exact mem_succ_self _
  have hb₀ : invApp f (ofNat.{u} n) ∈ y := invApp_mem hf hs hlast
  have hmaps : ∀ a, a ∈ y \ singleton (invApp f (ofNat.{u} n)) → app f a ∈ ofNat.{u} n := by
    intro a ha
    obtain ⟨hay, hane⟩ := (mem_sdiff_iff a y _).mp ha
    have hne : app f a ≠ ofNat.{u} n := by
      intro he
      exact hane ((mem_singleton_iff _ _).mpr (invApp_eq hf hay he).symm)
    have := app_mem_of_isInjection hf hay
    rw [ofNat_succ] at this
    rcases (mem_succ_iff _ _).mp this with he | h
    · exact absurd he hne
    · exact h
  have happ : ∀ a, a ∈ y \ singleton (invApp f (ofNat.{u} n)) →
      app (graphOn (y \ singleton (invApp f (ofNat.{u} n))) (ofNat.{u} n) (app f)) a
        = app f a := fun a ha => app_graphOn hmaps ha
  refine ⟨_, ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩⟩
  · intro a ha b hb he
    rw [happ a ha, happ b hb] at he
    exact hf.right.right.right a ((mem_sdiff_iff a y _).mp ha).left b
      ((mem_sdiff_iff b y _).mp hb).left he
  · intro k hk
    have hk' : k ∈ ofNat.{u} (n + 1) := by
      rw [ofNat_succ]
      exact (mem_succ_iff _ _).mpr (Or.inr hk)
    obtain ⟨a, hay, hak⟩ := isSurjection_onto hs hk'
    have hane : a ∉ singleton (invApp f (ofNat.{u} n)) := by
      intro hmem
      rw [(mem_singleton_iff _ _).mp hmem] at hak
      obtain ⟨c, hc, hcf⟩ := isSurjection_onto hs hlast
      rw [invApp_eq hf hc hcf, hcf] at hak
      rw [← hak] at hk
      exact not_mem_self _ hk
    refine ⟨a, (mem_sdiff_iff a y _).mpr ⟨hay, hane⟩, ?_⟩
    rw [happ a ((mem_sdiff_iff a y _).mpr ⟨hay, hane⟩)]
    exact hak

/-- Extending a bijection by a point outside the set. The new pair is adjoined
as a set, not chosen by a branch -- `w ∈ x` is not decidable. -/
theorem equinumerous_insert {x a₀ : ZFSet.{u}} {n : Nat}
    (hx : Equinumerous x (ofNat.{u} n)) (ha : a₀ ∉ x) :
    Equinumerous (x ∪ singleton a₀) (ofNat.{u} (n + 1)) := by
  obtain ⟨f, hf, hs⟩ := hx
  have hdomf := hf.right.left
  have hlast : ofNat.{u} n ∈ ofNat.{u} (n + 1) := by
    rw [ofNat_succ]
    exact mem_succ_self _
  have hfun : IsFunction (f ∪ singleton (opair a₀ (ofNat.{u} n))) := by
    constructor
    · intro z hz
      rcases (mem_union_iff z _ _).mp hz with h | h
      · exact hf.left.left z h
      · rw [(mem_singleton_iff z _).mp h]
        exact ⟨_, _, rfl⟩
    · intro w b b' hb hb'
      rcases (mem_union_iff _ _ _).mp hb with h | h <;>
        rcases (mem_union_iff _ _ _).mp hb' with h' | h'
      · exact hf.left.right w b b' h h'
      · obtain ⟨rfl, rfl⟩ := opair_injective ((mem_singleton_iff _ _).mp h')
        exact absurd (by rw [← hdomf]; exact (mem_domain_iff _ f).mpr ⟨b, h⟩) ha
      · obtain ⟨rfl, rfl⟩ := opair_injective ((mem_singleton_iff _ _).mp h)
        exact absurd (by rw [← hdomf]; exact (mem_domain_iff _ f).mpr ⟨b', h'⟩) ha
      · obtain ⟨-, rfl⟩ := opair_injective ((mem_singleton_iff _ _).mp h)
        obtain ⟨-, rfl⟩ := opair_injective ((mem_singleton_iff _ _).mp h')
        rfl
  have happX : ∀ w, w ∈ x → app (f ∪ singleton (opair a₀ (ofNat.{u} n))) w = app f w :=
    fun w hw => app_eq hfun ((mem_union_iff _ _ _).mpr
      (Or.inl (opair_app_mem hf.left (by rw [hdomf]; exact hw))))
  have happA : app (f ∪ singleton (opair a₀ (ofNat.{u} n))) a₀ = ofNat.{u} n :=
    app_eq hfun ((mem_union_iff _ _ _).mpr (Or.inr ((mem_singleton_iff _ _).mpr rfl)))
  have hdom : domain (f ∪ singleton (opair a₀ (ofNat.{u} n))) = x ∪ singleton a₀ := by
    refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨b, hb⟩ := (mem_domain_iff w _).mp hw
      rcases (mem_union_iff _ _ _).mp hb with h | h
      · exact (mem_union_iff _ _ _).mpr (Or.inl (by
          rw [← hdomf]; exact (mem_domain_iff w f).mpr ⟨b, h⟩))
      · obtain ⟨rfl, -⟩ := opair_injective ((mem_singleton_iff _ _).mp h)
        exact (mem_union_iff _ _ _).mpr (Or.inr ((mem_singleton_iff _ _).mpr rfl))
    · rcases (mem_union_iff _ _ _).mp hw with h | h
      · obtain ⟨b, hb⟩ := (mem_domain_iff w f).mp (by rw [hdomf]; exact h)
        exact (mem_domain_iff _ _).mpr ⟨b, (mem_union_iff _ _ _).mpr (Or.inl hb)⟩
      · rw [(mem_singleton_iff _ _).mp h]
        exact (mem_domain_iff _ _).mpr ⟨_, (mem_union_iff _ _ _).mpr
          (Or.inr ((mem_singleton_iff _ _).mpr rfl))⟩
  have hran : range (f ∪ singleton (opair a₀ (ofNat.{u} n))) ⊆ ofNat.{u} (n + 1) := by
    intro v hv
    obtain ⟨w, hw⟩ := (mem_range_iff v _).mp hv
    rcases (mem_union_iff _ _ _).mp hw with h | h
    · rw [ofNat_succ]
      exact (mem_succ_iff _ _).mpr (Or.inr (hf.right.right.left v
        ((mem_range_iff v f).mpr ⟨w, h⟩)))
    · obtain ⟨-, rfl⟩ := opair_injective ((mem_singleton_iff _ _).mp h)
      exact hlast
  refine ⟨_, ⟨hfun, hdom, hran, ?_⟩, ⟨hfun, hdom, hran, ?_⟩⟩
  · -- injective
    intro w hw w' hw' he
    rcases (mem_union_iff _ _ _).mp hw with h | h <;>
      rcases (mem_union_iff _ _ _).mp hw' with h' | h'
    · rw [happX w h, happX w' h'] at he
      exact isInjection_inj hf h h' he
    · rw [(mem_singleton_iff _ _).mp h'] at he ⊢
      rw [happX w h, happA] at he
      have hmem : app f w ∈ ofNat.{u} n := app_mem_of_isInjection hf h
      rw [he] at hmem
      exact absurd hmem (not_mem_self (ofNat.{u} n))
    · rw [(mem_singleton_iff _ _).mp h] at he ⊢
      rw [happX w' h', happA] at he
      have hmem : app f w' ∈ ofNat.{u} n := app_mem_of_isInjection hf h'
      rw [← he] at hmem
      exact absurd hmem (not_mem_self (ofNat.{u} n))
    · rw [(mem_singleton_iff _ _).mp h, (mem_singleton_iff _ _).mp h']
  · -- surjective
    intro k hk
    rw [ofNat_succ] at hk
    rcases (mem_succ_iff _ _).mp hk with rfl | h
    · exact ⟨a₀, (mem_union_iff _ _ _).mpr (Or.inr ((mem_singleton_iff _ _).mpr rfl)), happA⟩
    · obtain ⟨w, hw, hwk⟩ := isSurjection_onto hs h
      exact ⟨w, (mem_union_iff _ _ _).mpr (Or.inl hw), by rw [happX w hw]; exact hwk⟩

/-- A detachable subset of a finite set is finite. This is the constructive
form of the closure `em_of_subset_finite` refutes: the decision is a hypothesis
about the subset, not a principle about propositions. -/
theorem isFinite_of_detachable : ∀ n : Nat, ∀ x y : ZFSet.{u}, x ⊆ y →
    Equinumerous y (ofNat.{u} n) → (∀ a, a ∈ y → a ∈ x ∨ a ∉ x) → IsFinite x
  | 0, x, y, hsub, hy, _ => by
    -- `y` is empty, so `x` is
    have hxe : x = empty.{u} := by
      refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩
      obtain ⟨f, hf, -⟩ := hy
      have := app_mem_of_isInjection hf (hsub w hw)
      rw [ofNat_zero] at this
      exact absurd this (not_mem_empty _)
    rw [hxe]
    exact ⟨0, by rw [ofNat_zero]; exact equinumerous_refl _⟩
  | n + 1, x, y, hsub, hy, hdet => by
    obtain ⟨f, hf, hs⟩ := hy
    have hlast : ofNat.{u} n ∈ ofNat.{u} (n + 1) := by
      rw [ofNat_succ]
      exact mem_succ_self _
    have hb₀ : invApp f (ofNat.{u} n) ∈ y := invApp_mem hf hs hlast
    -- strip the last point from both sets
    have hy' := equinumerous_erase hf hs
    have hsub' : x \ singleton (invApp f (ofNat.{u} n))
        ⊆ y \ singleton (invApp f (ofNat.{u} n)) := by
      intro w hw
      obtain ⟨hwx, hwne⟩ := (mem_sdiff_iff w x _).mp hw
      exact (mem_sdiff_iff w y _).mpr ⟨hsub w hwx, hwne⟩
    have hdet' : ∀ a, a ∈ y \ singleton (invApp f (ofNat.{u} n)) →
        a ∈ x \ singleton (invApp f (ofNat.{u} n)) ∨
          a ∉ x \ singleton (invApp f (ofNat.{u} n)) := by
      intro a ha
      obtain ⟨hay, hane⟩ := (mem_sdiff_iff a y _).mp ha
      rcases hdet a hay with h | h
      · exact Or.inl ((mem_sdiff_iff a x _).mpr ⟨h, hane⟩)
      · exact Or.inr fun hmem => h ((mem_sdiff_iff a x _).mp hmem).left
    obtain ⟨m, hm⟩ := isFinite_of_detachable n _ _ hsub' hy' hdet'
    -- and decide whether the stripped point was in `x`
    rcases hdet _ hb₀ with hin | hout
    · -- it was: put it back
      refine ⟨m + 1, ?_⟩
      have hx : x = (x \ singleton (invApp f (ofNat.{u} n)))
          ∪ singleton (invApp f (ofNat.{u} n)) :=
        sdiff_singleton_union ⟨f, hf, hs⟩ hsub hb₀ hin
      rw [hx]
      exact equinumerous_insert hm (fun hmem => ((mem_sdiff_iff _ x _).mp hmem).right
        ((mem_singleton_iff _ _).mpr rfl))
    · -- it was not: the stripped set is `x` itself
      refine ⟨m, ?_⟩
      have hx : x \ singleton (invApp f (ofNat.{u} n)) = x := by
        refine ext _ _ fun w => ⟨fun hw => ((mem_sdiff_iff w x _).mp hw).left, fun hw => ?_⟩
        refine (mem_sdiff_iff w x _).mpr ⟨hw, fun hmem => ?_⟩
        rw [(mem_singleton_iff _ _).mp hmem] at hw
        exact hout hw
      rw [← hx]
      exact hm

/-- A bounded existential over a finite set is decidable, when the predicate
is. -/
theorem exists_or_not_of_finite {P : ZFSet.{u} → Prop} : ∀ n : Nat, ∀ y : ZFSet.{u},
    Equinumerous y (ofNat.{u} n) → (∀ a, a ∈ y → P a ∨ ¬ P a) →
      (∃ a, a ∈ y ∧ P a) ∨ ¬ ∃ a, a ∈ y ∧ P a :=
  fun _ _ hy hdet => by
    rcases exists_or_all_of_equinumerous hy hdet with h | h
    · exact Or.inl h
    · exact Or.inr (fun ⟨a, ha, hpa⟩ => h a ha hpa)

/-! ## Pigeonhole

An injection between numerals cannot decrease the index, so a set is
equinumerous to at most one numeral, so `IsFinite` is a statement about size
rather than about the existence of some bijection. -/

theorem dominates_ofNat_le : ∀ m n : Nat, Dominates (ofNat.{u} m) (ofNat.{u} n) → m ≤ n
  | 0, n, _ => by omega
  | m + 1, 0, ⟨f, hf⟩ => by
    exfalso
    have h0 : ofNat.{u} 0 ∈ ofNat.{u} (m + 1) :=
      (mem_ofNat_iff _ (m + 1)).mpr ⟨0, by omega, rfl⟩
    have := app_mem_of_isInjection hf h0
    rw [ofNat_zero] at this
    exact not_mem_empty _ this
  | m + 1, n + 1, ⟨f, hf⟩ => by
    have hlastm : ofNat.{u} m ∈ ofNat.{u} (m + 1) := by
      rw [ofNat_succ]
      exact mem_succ_self _
    have hsubm : ∀ w, w ∈ ofNat.{u} m → w ∈ ofNat.{u} (m + 1) := by
      intro w hw
      rw [ofNat_succ]
      exact (mem_succ_iff w _).mpr (Or.inr hw)
    -- the dodging map: use `f`, except send `f⁻¹` of the last point to `f (ofNat m)`
    have hmaps : ∀ w, w ∈ ofNat.{u} m →
        (∃ v, v ∈ ofNat.{u} n ∧
          ((app f w ≠ ofNat.{u} n ∧ v = app f w) ∨
           (app f w = ofNat.{u} n ∧ v = app f (ofNat.{u} m)))) := by
      intro w hw
      have hfw := app_mem_of_isInjection hf (hsubm w hw)
      rcases eq_or_ne_of_finite (equinumerous_refl (ofNat.{u} (n + 1))) hfw
        (by rw [ofNat_succ]; exact mem_succ_self _ : ofNat.{u} n ∈ ofNat.{u} (n + 1))
        with heq | hne
      · refine ⟨app f (ofNat.{u} m), ?_, Or.inr ⟨heq, rfl⟩⟩
        have hfm := app_mem_of_isInjection hf hlastm
        rw [ofNat_succ] at hfm
        rcases (mem_succ_iff _ _).mp hfm with he | h
        · exact absurd (isInjection_inj hf (hsubm w hw) hlastm
            (heq.trans he.symm)) (by
              intro hwm
              rw [hwm] at hw
              exact not_mem_self _ hw)
        · exact h
      · refine ⟨app f w, ?_, Or.inl ⟨hne, rfl⟩⟩
        rw [ofNat_succ] at hfw
        rcases (mem_succ_iff _ _).mp hfw with he | h
        · exact absurd he hne
        · exact h
    -- assemble the dodging map and recurse
    have hfun : IsFunction (sep (fun z => ∃ w, w ∈ ofNat.{u} m ∧ ∃ v, z = opair w v ∧
        ((app f w ≠ ofNat.{u} n ∧ v = app f w) ∨
         (app f w = ofNat.{u} n ∧ v = app f (ofNat.{u} m))))
        (prod (ofNat.{u} m) (ofNat.{u} n))) := by
      constructor
      · intro z hz
        obtain ⟨-, w, -, v, he, -⟩ := (mem_sep_iff _ z _).mp hz
        exact ⟨_, _, he⟩
      · intro w v v' hv hv'
        obtain ⟨-, a, -, b, he, hcase⟩ := (mem_sep_iff _ _ _).mp hv
        obtain ⟨-, a', -, b', he', hcase'⟩ := (mem_sep_iff _ _ _).mp hv'
        obtain ⟨rfl, rfl⟩ := opair_injective he
        obtain ⟨rfl, rfl⟩ := opair_injective he'
        rcases hcase with ⟨hne₁, rfl⟩ | ⟨hfa, rfl⟩ <;>
          rcases hcase' with ⟨hne', rfl⟩ | ⟨hfa', rfl⟩
        · rfl
        · exact absurd hfa' hne₁
        · exact absurd hfa hne'
        · rfl
    have happ : ∀ w, w ∈ ofNat.{u} m → ∃ v, v ∈ ofNat.{u} n ∧
        app (sep (fun z => ∃ w, w ∈ ofNat.{u} m ∧ ∃ v, z = opair w v ∧
          ((app f w ≠ ofNat.{u} n ∧ v = app f w) ∨
           (app f w = ofNat.{u} n ∧ v = app f (ofNat.{u} m))))
          (prod (ofNat.{u} m) (ofNat.{u} n))) w = v ∧
        ((app f w ≠ ofNat.{u} n ∧ v = app f w) ∨
         (app f w = ofNat.{u} n ∧ v = app f (ofNat.{u} m))) := by
      intro w hw
      obtain ⟨v, hv, hcase⟩ := hmaps w hw
      exact ⟨v, hv, app_eq hfun ((mem_sep_iff _ _ _).mpr
        ⟨opair_mem_prod hw hv, w, hw, v, rfl, hcase⟩), hcase⟩
    refine Nat.succ_le_succ (dominates_ofNat_le m n ⟨_, hfun, ?_, ?_, ?_⟩)
    · refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
      · obtain ⟨v, hv⟩ := (mem_domain_iff w _).mp hw
        exact mem_prod_left ((mem_sep_iff _ _ _).mp hv).left
      · obtain ⟨v, hv, hval, hcase⟩ := happ w hw
        exact (mem_domain_iff _ _).mpr ⟨v, (mem_sep_iff _ _ _).mpr
          ⟨opair_mem_prod hw hv, w, hw, v, rfl, hcase⟩⟩
    · intro v hv
      obtain ⟨w, hw⟩ := (mem_range_iff v _).mp hv
      exact mem_prod_right ((mem_sep_iff _ _ _).mp hw).left
    · intro a ha b hb he
      obtain ⟨va, -, hva, hca⟩ := happ a ha
      obtain ⟨vb, -, hvb, hcb⟩ := happ b hb
      rw [hva, hvb] at he
      subst he
      rcases hca with ⟨-, rfl⟩ | ⟨hfa, rfl⟩ <;> rcases hcb with ⟨hneb, hvb'⟩ | ⟨hfb, hvb'⟩
      · exact isInjection_inj hf (hsubm a ha) (hsubm b hb) hvb'
      · -- `a` is normal and `b` dodges, so `f a = f (ofNat m)` and `a = ofNat m`
        exact absurd (isInjection_inj hf (hsubm a ha) hlastm hvb')
          (by intro hae; rw [hae] at ha; exact not_mem_self _ ha)
      · exact absurd (isInjection_inj hf (hsubm b hb) hlastm hvb'.symm)
          (by intro hbe; rw [hbe] at hb; exact not_mem_self _ hb)
      · exact isInjection_inj hf (hsubm a ha) (hsubm b hb) (hfa.trans hfb.symm)

/-- A set is equinumerous to at most one numeral. -/
theorem card_unique {x : ZFSet.{u}} {m n : Nat} (hm : Equinumerous x (ofNat.{u} m))
    (hn : Equinumerous x (ofNat.{u} n)) : m = n := by
  have h₁ := dominates_ofNat_le m n (dominates_trans
    (dominates_of_equinumerous (equinumerous_symm hm)) (dominates_of_equinumerous hn))
  have h₂ := dominates_ofNat_le n m (dominates_trans
    (dominates_of_equinumerous (equinumerous_symm hn)) (dominates_of_equinumerous hm))
  omega

/-- Removing one point from a finite set drops the count by one -- for any
point, not just the one the bijection sends last. -/
theorem equinumerous_sdiff_singleton {x a : ZFSet.{u}} {n : Nat}
    (hx : Equinumerous x (ofNat.{u} (n + 1))) (ha : a ∈ x) :
    Equinumerous (x \ singleton a) (ofNat.{u} n) := by
  -- the smaller set is detachable, hence finite
  obtain ⟨m, hm⟩ := isFinite_of_detachable (n + 1) (x \ singleton a) x
    (fun w hw => ((mem_sdiff_iff w x _).mp hw).left) hx
    (fun w hw => by
      rcases eq_or_ne_of_finite hx hw ha with rfl | hne
      · exact Or.inr fun hmem => ((mem_sdiff_iff w x _).mp hmem).right
          ((mem_singleton_iff w w).mpr rfl)
      · exact Or.inl ((mem_sdiff_iff w x _).mpr ⟨hw,
          fun hmem => hne ((mem_singleton_iff w a).mp hmem)⟩))
  -- putting the point back recovers `x`, so `m + 1 = n + 1`
  have hback : (x \ singleton a) ∪ singleton a = x :=
    (sdiff_singleton_union hx (fun _ h => h) ha ha).symm
  have hcount : Equinumerous x (ofNat.{u} (m + 1)) := by
    rw [← hback]
    exact equinumerous_insert hm (fun hmem => ((mem_sdiff_iff a x _).mp hmem).right
      ((mem_singleton_iff a a).mpr rfl))
  have : m + 1 = n + 1 := card_unique hcount hx
  rw [show n = m by omega]
  exact hm

/-! ## Counting a product

`|x × y| = |x|·|y|`, via the bijection `⟨i, j⟩ ↦ i·n + j` on numerals. Both
halves are `Nat` arithmetic: injectivity is that `j` and `j'` below `n` cannot
absorb a difference of multiples of `n`, and surjectivity is division. -/

def pairNumeral (m n : Nat) : ZFSet.{u} :=
  sep (fun z => ∃ i : Nat, i < m ∧ ∃ j : Nat, j < n ∧
        z = opair (opair (ofNat.{u} i) (ofNat.{u} j)) (ofNat.{u} (i * n + j)))
    (prod (prod (ofNat.{u} m) (ofNat.{u} n)) (ofNat.{u} (m * n)))

theorem mem_pairNumeral_iff (m n : Nat) (z : ZFSet.{u}) :
    z ∈ pairNumeral.{u} m n ↔
      z ∈ prod (prod (ofNat.{u} m) (ofNat.{u} n)) (ofNat.{u} (m * n)) ∧
        ∃ i : Nat, i < m ∧ ∃ j : Nat, j < n ∧
          z = opair (opair (ofNat.{u} i) (ofNat.{u} j)) (ofNat.{u} (i * n + j)) :=
  mem_sep_iff _ _ _

private theorem opair_mem_pairNumeral {m n i j : Nat} (hi : i < m) (hj : j < n) :
    opair (opair (ofNat.{u} i) (ofNat.{u} j)) (ofNat.{u} (i * n + j))
      ∈ pairNumeral.{u} m n := by
  refine (mem_pairNumeral_iff m n _).mpr ⟨opair_mem_prod (opair_mem_prod
    ((mem_ofNat_iff _ m).mpr ⟨i, hi, rfl⟩) ((mem_ofNat_iff _ n).mpr ⟨j, hj, rfl⟩))
    ((mem_ofNat_iff _ (m * n)).mpr ⟨i * n + j, ?_, rfl⟩), i, hi, j, hj, rfl⟩
  -- `i·n + j < m·n` because `i+1 ≤ m` and `j < n`
  have hstep : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right n hi
  rw [Nat.add_mul, Nat.one_mul] at hstep
  omega

/-- The product of two numerals is counted by their product. -/
theorem equinumerous_prod_ofNat (m n : Nat) :
    Equinumerous (prod (ofNat.{u} m) (ofNat.{u} n)) (ofNat.{u} (m * n)) := by
  have hfun : IsFunction (pairNumeral.{u} m n) := by
    constructor
    · intro z hz
      obtain ⟨-, i, -, j, -, he⟩ := (mem_pairNumeral_iff m n z).mp hz
      exact ⟨_, _, he⟩
    · intro p v v' hv hv'
      obtain ⟨-, i, -, j, -, he⟩ := (mem_pairNumeral_iff m n _).mp hv
      obtain ⟨-, i', -, j', -, he'⟩ := (mem_pairNumeral_iff m n _).mp hv'
      obtain ⟨hp, rfl⟩ := opair_injective he
      obtain ⟨hp', rfl⟩ := opair_injective he'
      obtain ⟨hi, hj⟩ := opair_injective (hp.symm.trans hp')
      rw [ofNat_injective hi, ofNat_injective hj]
  have happ : ∀ i j : Nat, i < m → j < n →
      app (pairNumeral.{u} m n) (opair (ofNat.{u} i) (ofNat.{u} j))
        = ofNat.{u} (i * n + j) := fun i j hi hj =>
    app_eq hfun (opair_mem_pairNumeral hi hj)
  have hdom : domain (pairNumeral.{u} m n) = prod (ofNat.{u} m) (ofNat.{u} n) := by
    refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨v, hv⟩ := (mem_domain_iff p _).mp hp
      exact mem_prod_left ((mem_pairNumeral_iff m n _).mp hv).left
    · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
      obtain ⟨i, hi, rfl⟩ := (mem_ofNat_iff a m).mp ha
      obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff b n).mp hb
      exact (mem_domain_iff _ _).mpr ⟨_, opair_mem_pairNumeral hi hj⟩
  have hran : range (pairNumeral.{u} m n) ⊆ ofNat.{u} (m * n) := by
    intro v hv
    obtain ⟨p, hp⟩ := (mem_range_iff v _).mp hv
    exact mem_prod_right ((mem_pairNumeral_iff m n _).mp hp).left
  refine ⟨pairNumeral.{u} m n, ⟨hfun, hdom, hran, ?_⟩, ⟨hfun, hdom, hran, ?_⟩⟩
  · -- injective
    intro p hp p' hp' he
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_prod_iff p' _ _).mp hp'
    obtain ⟨i, hi, rfl⟩ := (mem_ofNat_iff a m).mp ha
    obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff b n).mp hb
    obtain ⟨i', hi', rfl⟩ := (mem_ofNat_iff a' m).mp ha'
    obtain ⟨j', hj', rfl⟩ := (mem_ofNat_iff b' n).mp hb'
    rw [happ i j hi hj, happ i' j' hi' hj'] at he
    have hnat := ofNat_injective he
    -- `j, j' < n`, so the multiples of `n` must agree
    have hij : i = i' := by
      rcases Nat.lt_or_ge i i' with h | h
      · have hstep : (i + 1) * n ≤ i' * n := Nat.mul_le_mul_right n h
        rw [Nat.add_mul, Nat.one_mul] at hstep
        omega
      · rcases Nat.eq_or_lt_of_le h with h' | h'
        · omega
        · have hstep : (i' + 1) * n ≤ i * n := Nat.mul_le_mul_right n h'
          rw [Nat.add_mul, Nat.one_mul] at hstep
          omega
    rw [hij] at hnat ⊢
    rw [(by omega : j = j')]
  · -- surjective: divide
    intro v hv
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff v (m * n)).mp hv
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · omega
      · exact h
    have hdivmod := Nat.div_add_mod k n
    have hdiv : k / n < m := by
      rcases Nat.lt_or_ge (k / n) m with h | h
      · exact h
      · exfalso
        have hstep : m * n ≤ n * (k / n) := by
          rw [Nat.mul_comm n (k / n)]
          exact Nat.mul_le_mul_right n h
        have hmod : k % n < n := Nat.mod_lt _ hn
        omega
    refine ⟨opair (ofNat.{u} (k / n)) (ofNat.{u} (k % n)), ?_, ?_⟩
    · exact opair_mem_prod ((mem_ofNat_iff _ m).mpr ⟨k / n, hdiv, rfl⟩)
        ((mem_ofNat_iff _ n).mpr ⟨k % n, Nat.mod_lt _ hn, rfl⟩)
    · rw [happ (k / n) (k % n) hdiv (Nat.mod_lt _ hn)]
      have hcomm : k / n * n = n * (k / n) := Nat.mul_comm _ _
      exact congrArg _ (by omega)

/-- Disjoint finite sets add. The proof removes one element of `T` at a time,
because building the bijection directly would need to decide `w ∈ S`. -/
theorem equinumerous_union_disjoint : ∀ m n : Nat, ∀ S T : ZFSet.{u},
    Equinumerous S (ofNat.{u} n) → Equinumerous T (ofNat.{u} m) →
    (∀ w, w ∈ S → w ∉ T) → Equinumerous (S ∪ T) (ofNat.{u} (n + m)) := by
  intro m
  induction m with
  | zero =>
    intro n S T hS hT _
    have hTe : T = empty.{u} := by
      refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩
      obtain ⟨f, hf, -⟩ := hT
      rw [ofNat_zero] at hf
      exact absurd (app_mem_of_isInjection hf hw) (not_mem_empty _)
    have hun : S ∪ T = S := by
      rw [hTe]
      exact ext _ _ fun w => ⟨fun hw => by
        rcases (mem_union_iff _ _ _).mp hw with h | h
        · exact h
        · exact absurd h (not_mem_empty w),
        fun hw => (mem_union_iff _ _ _).mpr (Or.inl hw)⟩
    rw [hun]
    exact hS
  | succ m ih =>
    intro n S T hS hT hdisj
    obtain ⟨f, hf, hs⟩ := hT
    have hlast : ofNat.{u} m ∈ ofNat.{u} (m + 1) := by
      rw [ofNat_succ]
      exact mem_succ_self _
    obtain ⟨a, haT, _⟩ := isSurjection_onto hs hlast
    have hT' : Equinumerous (T \ singleton a) (ofNat.{u} m) :=
      equinumerous_sdiff_singleton ⟨f, hf, hs⟩ haT
    have hdisj' : ∀ w, w ∈ S → w ∉ T \ singleton a :=
      fun w hw hmem => hdisj w hw ((mem_sdiff_iff _ _ _).mp hmem).left
    have hunion := ih n S (T \ singleton a) hS hT' hdisj'
    have hanot : a ∉ S ∪ (T \ singleton a) := by
      intro hmem
      rcases (mem_union_iff _ _ _).mp hmem with h | h
      · exact hdisj a h haT
      · exact ((mem_sdiff_iff _ _ _).mp h).right ((mem_singleton_iff _ _).mpr rfl)
    have hsplit : (S ∪ (T \ singleton a)) ∪ singleton a = S ∪ T := by
      refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
      · rcases (mem_union_iff _ _ _).mp hw with h | h
        · rcases (mem_union_iff _ _ _).mp h with h' | h'
          · exact (mem_union_iff _ _ _).mpr (Or.inl h')
          · exact (mem_union_iff _ _ _).mpr (Or.inr ((mem_sdiff_iff _ _ _).mp h').left)
        · rw [(mem_singleton_iff _ _).mp h]
          exact (mem_union_iff _ _ _).mpr (Or.inr haT)
      · rcases (mem_union_iff _ _ _).mp hw with h | h
        · exact (mem_union_iff _ _ _).mpr (Or.inl ((mem_union_iff _ _ _).mpr (Or.inl h)))
        · rcases eq_or_ne_of_finite ⟨f, hf, hs⟩ h haT with rfl | hne
          · exact (mem_union_iff _ _ _).mpr (Or.inr ((mem_singleton_iff _ _).mpr rfl))
          · exact (mem_union_iff _ _ _).mpr (Or.inl ((mem_union_iff _ _ _).mpr
              (Or.inr ((mem_sdiff_iff _ _ _).mpr ⟨h, fun hmem =>
                hne ((mem_singleton_iff _ _).mp hmem)⟩))))
    have hres := equinumerous_insert hunion hanot
    rw [hsplit, show n + m + 1 = n + (m + 1) by omega] at hres
    exact hres

/-- Membership in a finite subset is decidable, tested against the elements. -/
theorem mem_or_not_mem_of_subset {S T : ZFSet.{u}} {n m : Nat}
    (hT : Equinumerous T (ofNat.{u} m)) (hS : Equinumerous S (ofNat.{u} n))
    (hsub : S ⊆ T) {w : ZFSet.{u}} (hw : w ∈ T) : w ∈ S ∨ w ∉ S := by
  rcases exists_or_not_of_finite (P := fun a => a = w) n S hS
    (fun a ha => eq_or_ne_of_finite hT (hsub _ ha) hw) with ⟨a, ha, rfl⟩ | hno
  · exact Or.inl ha
  · exact Or.inr fun hmem => hno ⟨w, hmem, rfl⟩

/-! ## Sets named by a list

A duplicate-free list of length `n` names a set of size `n`. -/

def Distinct : List ZFSet.{u} → Prop
  | [] => True
  | a :: as => a ∉ as ∧ Distinct as

/-! ## Audit

Nothing classical: the inverse is extracted from a singleton rather than chosen,
and `em` appears only as a hypothesis, inherited from antisymmetry. -/

/-- A singleton is equinumerous with `1`. Adjoining the point to the empty
set, which `equinumerous_insert` does without deciding membership. -/
theorem equinumerous_singleton_one {a : ZFSet.{u}} :
    Equinumerous (singleton a) (ofNat.{u} 1) := by
  have h := equinumerous_insert (x := empty.{u}) (a₀ := a) (n := 0)
    (by rw [ofNat_zero]; exact equinumerous_refl _) (not_mem_empty a)
  rw [empty_union] at h
  exact h

#print axioms dominates_of_equinumerous
#print axioms equinumerous_symm
#print axioms equinumerous_trans
#print axioms dominates_trans
#print axioms isFinite_ofNat
#print axioms equinumerous_prod
#print axioms dominates_ofNat_le
#print axioms card_unique
#print axioms equinumerous_union_disjoint
#print axioms equinumerous_sdiff_singleton
#print axioms dominates_ofNat_of_subset
#print axioms em_of_subset_finite
#print axioms eq_or_ne_of_finite
#print axioms equinumerous_erase
#print axioms equinumerous_insert
#print axioms isFinite_of_detachable
#print axioms exists_or_not_of_finite
#print axioms equinumerous_prod_ofNat
#print axioms equinumerous_singleton_one

end SetTheory
namespace ZFSet
export SetTheory (Distinct Dominates Equinumerous IsFinite SubsetFinite app_compOn app_invOn app_mem_of_isInjection card_unique compOn dominates_ofNat_le dominates_ofNat_of_subset dominates_of_equinumerous dominates_trans em_of_subset_finite eq_or_ne_of_finite equinumerous_erase equinumerous_insert equinumerous_prod equinumerous_prod_ofNat equinumerous_refl equinumerous_sdiff_singleton equinumerous_singleton_one equinumerous_symm equinumerous_trans equinumerous_union_disjoint exists_or_all_of_equinumerous exists_or_not_of_finite graphOn_range invApp invApp_eq invApp_mem invOn isFinite_ofNat isFinite_of_detachable isInjection_compOn isInjection_idOn isInjection_invOn isSurjection_idOn isSurjection_invOn mem_or_not_mem_of_subset mem_pairNumeral_iff pairNumeral sdiff_singleton_union)
end ZFSet
