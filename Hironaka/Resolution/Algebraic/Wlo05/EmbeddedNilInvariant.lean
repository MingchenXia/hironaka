/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNil
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRound
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loop on a smooth `Y`: the invariant through the rounds

The empty succession for a smooth `Y` (`bed_eq_nil_of_smooth`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`; [Wlo05, 4.6]: at a smooth point of `Y` the
invariant is already terminal) is proved by induction on the number of remaining components, with
the invariant `Invariant T C` on the loop's state `(T, C)`:

* the boundary is empty; the ideal is the product of the members of `C`; every member of `C` is the
  reduced ideal of the closure of a generic point of the ideal's support; the members have pairwise
  disjoint supports; and the ideal is regular stalkwise (the stalk of the ambient at a point of the
  support modulo the ideal's stalk is a regular local ring — the smoothness of `Y`, read on the
  stalks, which survives the removal of components).

Given the CORE LEMMA — for such a triple with a nonempty ideal the first centre of the run of
`BMO_1` contains a generic point of the ideal's support (`Core`; proved in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`) — one round of the loop at stage `0` removes
at least one component and preserves the invariant (`invariant_isolated_of_cons`; the colon by the
absorbed components is the product of the remaining ones, `colon_prod_filter`), and the loop's
length is `0` (`length_bedAux_eq_zero_of_invariant`). The terminal round, on the unit ideal, is
empty (`length_bedAux_eq_zero_of_eq_top`). The initial state satisfies the invariant by
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilSmooth`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

/-- **The loop's invariant** on a state `(X, I, E, C)` — the boundary is empty, the ideal is the
product of the members of `C`, each member is the reduced ideal of the closure of a generic point
of the ideal's support, the members have pairwise disjoint supports, and the ideal is regular
stalkwise. Stated on the data `(I, E, C)` over the ambient `X` (not on the marked triple), so that a
round of the loop — whose isolated triple has the SAME ambient scheme only definitionally — is a
`change` away. -/
structure Invariant {X : Scheme.{u}} (I : X.IdealSheafData) (E : DivisorFamily X)
    (C : Finset X.IdealSheafData) : Prop where
  isEmpty : IsEmpty E.ι
  eq_prod : I = ∏ c ∈ C, c
  mem : ∀ c ∈ C, ∃ η ∈ I.support.genericPoints, c = IdealSheafData.vanishingIdeal (Closeds.closure
      {η})
  pairwise : (C : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support
  regular : ∀ x ∈ I.support, IsRegularLocalRing (X.presheaf.stalk x ⧸ I.stalkIdeal x)

variable {k : Type u} [Field k] [CharZero k]

/-- **The core lemma of the smooth case**, as a hypothesis — for a marked triple of mark `1` with
empty boundary whose ideal is regular stalkwise and not the unit ideal, the run of `BMO_1` starts
with a blow-up whose centre contains a generic point of the ideal's support (the maximal-contact
descent of the round of order `1` ends at a component of `Y` itself). -/
def Core (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (T : MarkedTriple k) (hm : T.m = 1), IsEmpty T.E.ι →
    (∀ x ∈ T.I.support, IsRegularLocalRing (T.X.left.presheaf.stalk x ⧸ T.I.stalkIdeal x)) →
    T.I ≠ ⊤ →
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      bmoOneRun T hm = BlowUpSequence.cons T.X.left D rest ∧
        ∃ η ∈ T.I.support.genericPoints, η ∈ D.support

namespace Invariant

variable {X : Scheme.{u}} {I : X.IdealSheafData} {E : DivisorFamily X}
  {C : Finset X.IdealSheafData}

/-- The members of `C` are radical: each is the vanishing ideal of its support. -/
theorem vanishingIdeal_support_eq (h : Invariant I E C) {c : X.IdealSheafData} (hc : c ∈ C) :
    IdealSheafData.vanishingIdeal c.support = c := by
  obtain ⟨η, -, rfl⟩ := h.mem c hc
  rw [Hironaka.Sequence.support_vanishingIdeal_eq]

/-- The support of the ideal is the union of the supports of the members. -/
theorem support_eq (h : Invariant I E C) : I.support = C.sup fun c => c.support := by
  rw [h.eq_prod, IdealSheafData.support_finset_prod_eq_sup]

/-- A point of the support lies in the support of some member. -/
theorem exists_mem_support (h : Invariant I E C) {x : X} (hx : x ∈ I.support) :
    ∃ c ∈ C, x ∈ c.support := by
  rw [h.support_eq, ← SetLike.mem_coe, Closeds.coe_finset_sup] at hx
  simpa using hx

/-- The component of a generic point of the support is a member of `C`. -/
theorem vanishingIdeal_closure_mem (h : Invariant I E C) {η : X}
    (hη : η ∈ I.support.genericPoints) :
    IdealSheafData.vanishingIdeal (Closeds.closure {η}) ∈ C := by
  obtain ⟨c, hc, hηc⟩ := h.exists_mem_support hη.1
  obtain ⟨η', hη', rfl⟩ := h.mem c hc
  rw [← SetLike.mem_coe, IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    ← specializes_iff_mem_closure] at hηc
  have : η' = η := hη.2 hη'.1 hηc
  subst this
  exact hc

/-- The ideal is not the unit ideal when `C` is nonempty. -/
theorem ne_top_of_nonempty (h : Invariant I E C) (hC : C.Nonempty) : I ≠ ⊤ := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨η, hη, -⟩ := h.mem c hc
  intro htop
  have : η ∈ I.support := hη.1
  rw [htop, IdealSheafData.support_top] at this
  exact this

/-- The ideal is the unit ideal when `C` is empty. -/
theorem eq_top_of_eq_empty (h : Invariant I E C) (hC : C = ∅) : I = ⊤ := by
  rw [h.eq_prod, hC, Finset.prod_empty, IdealSheafData.one_eq_top]

/-- A generic point of a member's support lies in the ideal's support. -/
theorem mem_support_of_mem (h : Invariant I E C) {c : X.IdealSheafData} (hc : c ∈ C) {x : X}
    (hx : x ∈ c.support) : x ∈ I.support := by
  rw [h.support_eq]
  exact Finset.le_sup (f := fun c : X.IdealSheafData => c.support) hc hx

end Invariant

/-! ### One round at stage `0` preserves the invariant -/

section Round

variable (T : MarkedTriple k) (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp)
  (hQ : ((BlowUpSequence.cons T.X.left D rest).take 0).IsOrderGeSeq
    (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
  (C : Finset T.X.left.IdealSheafData)

open Classical in
/-- The isolated ideal at stage `0` is the product of the remaining members — the colon of the
product over `C` by the reduced ideal of the absorbed members (`colon_prod_filter`). -/
theorem isolatedAt_cons_zero_I_eq_prod (h : Invariant T.I T.E C) :
    (isolatedAt T ((BlowUpSequence.cons T.X.left D rest).take 0) hQ (C.filter fun c => D ≤ c)).I =
      ∏ c ∈ C.filter (fun c => ¬ D ≤ c), c := by
  rw [isolatedAt_cons_zero_I, h.eq_prod]
  exact IdealSheafData.colon_prod_filter (fun c => c) C (fun c => D ≤ c)
    (fun c hc => h.vanishingIdeal_support_eq hc) h.pairwise

omit [CharZero k] in
/-- The product over a sub-finset is at least the product over the finset. -/
theorem prod_le_prod_filter (P : T.X.left.IdealSheafData → Prop) [DecidablePred P] :
    ∏ c ∈ C, c ≤ ∏ c ∈ C.filter P, c := by
  rw [← Finset.prod_filter_mul_prod_filter_not C P (fun c => c)]
  exact IdealSheafData.mul_le_self_left _ _

omit [CharZero k] in
/-- The stalk of a product of members with pairwise disjoint supports at a point of one member's
support is that member's stalk. -/
theorem stalkIdeal_prod_eq_of_mem (A : Finset T.X.left.IdealSheafData)
    (hdisj : (A : Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    {c : T.X.left.IdealSheafData} (hc : c ∈ A) {x : T.X.left} (hx : x ∈ c.support) :
    (∏ a ∈ A, a).stalkIdeal x = c.stalkIdeal x := by
  classical
  rw [IdealSheafData.stalkIdeal_finset_prod, Finset.prod_eq_single c]
  · intro b hb hbc
    rw [Ideal.one_eq_top]
    refine IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ fun hxb => ?_
    have hmem : x ∈ ((b.support ⊓ c.support : Closeds T.X.left) : Set T.X.left) := by
      rw [Closeds.coe_inf]
      exact ⟨hxb, hx⟩
    have hbot : x ∈ ((⊥ : Closeds T.X.left) : Set T.X.left) := (hdisj hb hc hbc).le_bot hmem
    rw [Closeds.coe_bot] at hbot
    exact hbot
  · exact fun habs => (habs hc).elim

omit [CharZero k] in
/-- **Removing members preserves the invariant** — the product over a sub-finset `F ⊆ C` with the
same boundary satisfies the invariant: its support is the union of the remaining members'
supports, a generic point of `I`'s support in it stays generic (the support shrinks), and the stalk
of the product at a point of a remaining member is the stalk of `I` there. -/
theorem invariant_prod_filter (h : Invariant T.I T.E C) (P : T.X.left.IdealSheafData → Prop)
    [DecidablePred P] :
    Invariant (∏ c ∈ C.filter P, c) T.E (C.filter P) := by
  have hsub : C.filter P ⊆ C := Finset.filter_subset P C
  have hpair₁ : ((C.filter P : Finset T.X.left.IdealSheafData) :
      Set T.X.left.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support :=
    h.pairwise.mono (Finset.coe_subset.mpr hsub)
  have hle : T.I ≤ ∏ c ∈ C.filter P, c := by
    rw [h.eq_prod]
    exact prod_le_prod_filter T C P
  have hsupp : (∏ c ∈ C.filter P, c).support ≤ T.I.support := IdealSheafData.support_antitone hle
  have hmemF : ∀ c ∈ C.filter P, ∀ x ∈ c.support, x ∈ (∏ c ∈ C.filter P, c).support := by
    intro c hc x hx
    rw [IdealSheafData.support_finset_prod_eq_sup]
    exact Finset.le_sup (f := fun c : T.X.left.IdealSheafData => c.support) hc hx
  refine ⟨h.isEmpty, rfl, ?_, hpair₁, ?_⟩
  · intro c hc
    obtain ⟨η, hη, rfl⟩ := h.mem c (hsub hc)
    refine ⟨η, ⟨hmemF _ hc η ?_, fun η' hη' hspec => hη.2 (hsupp hη') hspec⟩, rfl⟩
    rw [Hironaka.Sequence.support_vanishingIdeal_eq, ← SetLike.mem_coe, Closeds.coe_closure]
    exact subset_closure (Set.mem_singleton η)
  · intro x hx
    obtain ⟨c, hc, hxc⟩ : ∃ c ∈ C.filter P, x ∈ c.support := by
      rw [IdealSheafData.support_finset_prod_eq_sup, ← SetLike.mem_coe,
          Closeds.coe_finset_sup] at hx
      simpa using hx
    have hst : (∏ c ∈ C.filter P, c).stalkIdeal x = T.I.stalkIdeal x := by
      rw [stalkIdeal_prod_eq_of_mem T (C.filter P) hpair₁ hc hxc, h.eq_prod,
        stalkIdeal_prod_eq_of_mem T C h.pairwise (hsub hc) hxc]
    rw [hst]
    exact h.regular x (hsupp hx)

end Round

open Classical in
/-- **One round at stage `0` preserves the invariant** — for a run `S = cons X D rest` (the `subst`
form, for the run `bmoOneRun T hm` through `hrun`), the isolated triple with the remaining members
satisfies the invariant: the absorbed members are those contained in `D`
(`filter_centerContains_cons_zero`), the boundary is unchanged, the ideal is the product of the
remaining members (`isolatedAt_cons_zero_I_eq_prod`), and removing members preserves the invariant
(`invariant_prod_filter`). The isolated triple's ambient scheme is `T.X.left` definitionally, hence
the `change`. -/
theorem invariant_isolated_of_cons (T : MarkedTriple k) (S : BlowUpSequence T.X.left)
    (hQ : (S.take 0).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (C : Finset T.X.left.IdealSheafData)
    (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (hcons : S = BlowUpSequence.cons T.X.left D rest) (h : Invariant T.I T.E C) :
    Invariant (isolatedAt T (S.take 0) hQ (C.filter fun c => CenterContains S c 0)).I
      (isolatedAt T (S.take 0) hQ (C.filter fun c => CenterContains S c 0)).E
      (remainingAt (S.take 0) (C.filter fun c => ¬ CenterContains S c 0)) := by
  subst hcons
  rw [filter_centerContains_cons_zero, filter_not_centerContains_cons_zero]
  change Invariant (X := T.X.left) _ _ _
  rw [isolatedAt_cons_zero_I_eq_prod T D rest hQ C h, remainingAt_cons_zero,
    isolatedAt_cons_zero_E]
  exact invariant_prod_filter T C h _

/-! ### The loop is empty on a state satisfying the invariant -/

/-- **The loop has length `0` on every state satisfying the invariant**, given the core lemma — by
strong induction on the number of members: a round at stage `0` removes the absorbed components
(at least the one through the generic point the core lemma provides) and preserves the invariant;
the terminal round on the unit ideal is empty. -/
theorem length_bedAux_eq_zero_of_invariant (hcore : Core k) :
    ∀ (N : ℕ) (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData),
      C.card = N → Invariant T.I T.E C → (bedAux T hm C).length = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C hcard h
  by_cases hC : C = ∅
  · refine length_bedAux_eq_zero_of_eq_top T hm C ?_ (h.eq_top_of_eq_empty hC)
    rintro ⟨n, c, hc, -⟩
    rw [hC] at hc
    exact Finset.notMem_empty c hc
  · obtain ⟨D, rest, hrun, η, hη, hηD⟩ :=
      hcore T hm h.isEmpty h.regular (h.ne_top_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hC))
    have hc₀ := h.vanishingIdeal_closure_mem hη
    have h0 : HasAbsorptionAt T hm C 0 := hasAbsorptionAt_zero_of_mem_support T hm C hrun hηD hc₀
    rw [length_bedAux_of_hasAbsorptionAt_zero T hm C h0]
    have hlt : (remainingComponents T hm C 0).card < N := by
      have := card_remainingComponents_lt T hm C ⟨0, h0⟩
      rw [find_eq_zero_of_hasAbsorptionAt_zero T hm C h0, hcard] at this
      exact this
    have hinv : Invariant (isolatedTriple T hm C 0).I (isolatedTriple T hm C 0).E
        (remainingComponents T hm C 0) :=
      invariant_isolated_of_cons T (bmoOneRun T hm) _ C D rest hrun h
    exact ih _ hlt _ (isolatedTriple_m T hm C 0) _ rfl hinv

end Hironaka.Resolution
