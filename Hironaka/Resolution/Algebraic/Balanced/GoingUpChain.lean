/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The cosupport chain in the proof of the going-up theorem

The five cosupport lemmas that the proof of the going-up property of D-balanced ideals
[Kol07, Theorem 84], item 90 of Kollár's text, strings together on the hypersurface side of the
pushed-forward sequence. Throughout, `cosupp(A, c)` is the order-`≥ c` locus
`{x | (c : ℕ∞) ≤ A.ord x}` [Kol07, Definition 59].

* `cosupp_pow` ([Kol07, Definition 59, (3)]): on a smooth variety,
  `cosupp(A^s, cs) = cosupp(A, c)` for `s ≥ 1`. This is `ord_pow`, `ord_x (A^s) = s · ord_x A`, and
  the cancellation of `s ≠ 0, ⊤` in `ℕ∞`.
* `cosupp_markedTransformSeq_subset_of_le` ([Kol07, Definition 59, (1)]; the third displayed line
  of item 90): the marked transform along a sequence is monotone (`markedTransformSeq_mono`) and the
  cosupport is antitone (`ord_anti`), so `A ≤ A'` gives
  `cosupp Π_*^{-1}(A', c) ⊆ cosupp Π_*^{-1}(A, c)`.
* `cosupp_markedTransformSeq_pow` (the fourth displayed line of item 90): for a sequence of order
  `≥ c` for `(A, c)`, the power rule `Π_*^{-1}(A^s, cs) = (Π_*^{-1}(A, c))^s`
  (`markedTransformSeq_pow`, which needs the order hypothesis for the definedness of
  [Kol07, Definition 60] at every step) turns `cosupp_pow` on the (smooth) stage into
  `cosupp Π_*^{-1}(A^s, cs) = cosupp Π_*^{-1}(A, c)`.
* `ordAlongEq_map_of_cosupp_subset` (the opening of item 90): for a closed immersion `g : Y ↪ X`, an
  ideal sheaf `A` on `X` with `max-ord A ≤ m` and a centre `Z ⊆ Y` along which `J` has order `≥ m`,
  if `cosupp(J, m)` maps into `cosupp(A, m)` then `ord_{g_* Z} A = m`. Purely topological: a closed
  immersion is a closed embedding, so the support of `g_* Z = Z.map g` is the image of the support
  of `Z` and its generic points are the images of the generic points of `Z` (specialization is
  preserved by `g` and reflected by injectivity); there `J` has order `≥ m`, hence `A` has order
  `≥ m`, and `max-ord A ≤ m` closes the gap.
* `cosupp_markedTransformSeq_subset_iInter` (the second to fifth displayed lines of item 90): for
  `I` D-balanced [Kol07, Definition 83] and `T` a smooth blow-up sequence of order `≥ m` starting
  with `(S, I|_S, m)` on the smooth hypersurface `S`, at every stage `i` and for every `j < m`,
  `cosupp(J_i, m) ⊆ cosupp T_*^{-1}((D^j I)|_S, m − j)` with `J_i = T_*^{-1}(I|_S, m)`. The chain,
  read from the bottom of item 90 upwards, with the marks `m(m − j)` throughout:
  `cosupp(J_i, m) = cosupp(J_i^{m−j}, m(m−j))` (`cosupp_pow` on the stage `S_i`, smooth of relative
  dimension `n − 1`) `= cosupp T_*^{-1}((I|_S)^{m−j}, m(m−j))` (the power rule, equality under the
  order hypothesis on `T`) `= cosupp T_*^{-1}((I^{m−j})|_S, m(m−j))` (`comap_pow`)
  `⊆ cosupp T_*^{-1}(((D^j I)^m)|_S, m(m−j))` (D-balancedness `(D^j I)^m ⊆ I^{m−j}` restricted to
  `S`, monotonicity) `⊆ cosupp((T_*^{-1}((D^j I)|_S, m−j))^m, m(m−j))` (the unconditional power
  inclusion `pow_markedTransformSeq_le`, no order hypothesis on `(D^j I)|_S` needed)
  `= cosupp T_*^{-1}((D^j I)|_S, m−j)` (`cosupp_pow` again). Intersecting over `j < m` gives the
  inclusion `cosupp(J_i, m) ⊆ ⋂_{j<m} cosupp T_*^{-1}((D^j I)|_S, m − j)` that item 90 needs. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Monotonicity of the cosupport of the transform (any scheme) -/

/-- Line 3 of [Kol07, 90], from [Kol07, Definition 59, (1)]: the marked transform along a sequence
is monotone (`markedTransformSeq_mono`) and the cosupport is antitone (`ord_anti`), so at every
stage `A ≤ A'` gives `cosupp Π_*^{-1}(A', c) ⊆ cosupp Π_*^{-1}(A, c)`. -/
theorem cosupp_markedTransformSeq_subset_of_le (B : BlowUpSequence X) {A A' : X.IdealSheafData}
    (hAA' : A ≤ A') (c : ℕ) (i : Fin (B.length + 1)) :
    {x : B.stage i | (c : ℕ∞) ≤ (B.markedTransformSeq A' c i).ord x} ⊆
      {x | (c : ℕ∞) ≤ (B.markedTransformSeq A c i).ord x} := fun x hx =>
  le_trans hx (IdealSheafData.ord_anti (markedTransformSeq_mono B hAA' c i) x)

/-! ### The order along the pushed-forward centre (any schemes) -/

section PushedCentre

variable {Y : Scheme.{u}}

/-- The support of the pushforward of a centre along a closed immersion is the image of its
support (a closed immersion is a closed embedding, so the image is closed and Mathlib's
`support_map` needs no closure). -/
theorem coe_support_map_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (Z : Y.IdealSheafData) : ((Z.map g).support : Set X) = g '' Z.support := by
  rw [IdealSheafData.support_map, Closeds.coe_closure]
  exact ((Scheme.Hom.isClosedEmbedding g).isClosedMap _ Z.support.isClosed).closure_eq

/-- The generic points of the pushed-forward centre are the images of the generic points of the
centre: `g` preserves specialization (continuity) and, being injective, reflects equality. -/
theorem mem_genericPoints_support_map_iff (g : Y ⟶ X) [IsClosedImmersion g] (Z : Y.IdealSheafData)
    (η' : X) : η' ∈ (Z.map g).support.genericPoints ↔
      ∃ η ∈ Z.support.genericPoints, g η = η' := by
  have hinj : Function.Injective g := (Scheme.Hom.isClosedEmbedding g).injective
  have hmem : ∀ x, x ∈ (Z.map g).support ↔ x ∈ g '' (Z.support : Set Y) := fun x => by
    rw [← SetLike.mem_coe, coe_support_map_of_isClosedImmersion]
  constructor
  · rintro ⟨hη', hmax⟩
    obtain ⟨η, hη, rfl⟩ := (hmem _).mp hη'
    refine ⟨η, ⟨hη, fun η'' hη'' hspec => ?_⟩, rfl⟩
    exact hinj (hmax ((hmem _).mpr ⟨η'', hη'', rfl⟩) (hspec.map g.base.hom.continuous))
  · rintro ⟨η, ⟨hη, hmax⟩, rfl⟩
    refine ⟨(hmem _).mpr ⟨η, hη, rfl⟩, fun x hx hspec => ?_⟩
    obtain ⟨η'', hη'', rfl⟩ := (hmem _).mp hx
    rw [hmax hη'' ((Scheme.Hom.isClosedEmbedding g).isInducing.specializes_iff.mp hspec)]

/-- The opening of [Kol07, 90]: for a closed immersion `g : Y ↪ X`, an ideal sheaf `A` on `X` with
`max-ord A ≤ m`, and a centre `Z ⊆ Y` along which an ideal sheaf `J` on `Y` has order `≥ m`: if
`cosupp(J, m)` maps into `cosupp(A, m)`, then `ord_{g_* Z} A = m` — at a generic point `g η` of
`g_* Z`, `η` is a generic point of `Z`, so `m ≤ ord_η J` and hence
`m ≤ ord_{g η} A ≤ max-ord A ≤ m`. -/
theorem ordAlongEq_map_of_cosupp_subset (g : Y ⟶ X) [IsClosedImmersion g] (A : X.IdealSheafData)
    (J Z : Y.IdealSheafData) {m : ℕ} (hmax : A.maxOrd ≤ m)
    (hJ : J.LeOrdAlong Z.support (m : ℕ∞))
    (hsub : ∀ y : Y, (m : ℕ∞) ≤ J.ord y → (m : ℕ∞) ≤ A.ord (g y)) :
    A.OrdAlongEq (Z.map g).support (m : ℕ∞) := by
  intro η' hη'
  obtain ⟨η, hη, rfl⟩ := (mem_genericPoints_support_map_iff g Z η').mp hη'
  exact le_antisymm ((A.le_maxOrd _).trans hmax) (hsub η (hJ η hη))

end PushedCentre

/-! ### The chain on a smooth variety -/

section Chain

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n in
/-- Line 2 of [Kol07, 90], from [Kol07, Definition 59, (3)]: on a smooth variety,
`cosupp(A^s, cs) = cosupp(A, c)` for `s ≥ 1` — `ord_pow`, `ord_x (A^s) = s · ord_x A`, and
cancellation of `s` in `ℕ∞`. -/
theorem cosupp_pow (A : X.IdealSheafData) (c : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    {x : X | ((c * s : ℕ) : ℕ∞) ≤ (A ^ s).ord x} = {x | (c : ℕ∞) ≤ A.ord x} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [ord_pow f n A s hs x, Nat.cast_mul, mul_comm (c : ℕ∞) (s : ℕ∞)]
  exact ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hs))
    (ENat.natCast_ne_top s)

variable (B : BlowUpSequence X) (E : DivisorFamily X)

include n in
/-- Line 4 of [Kol07, 90], from [Kol07, Definition 59, (3)]: along a smooth blow-up sequence of
order `≥ c` for `(A, c)`, for `s ≥ 1` and at every stage,
`cosupp Π_*^{-1}(A^s, cs) = cosupp Π_*^{-1}(A, c)` — the power rule and `cosupp_pow` on the stage,
which is smooth of relative dimension `n`. -/
theorem cosupp_markedTransformSeq_pow {A : X.IdealSheafData} {c : ℕ}
    (h : B.IsOrderGeSeq f A c E) {s : ℕ} (hs : 1 ≤ s) (i : Fin (B.length + 1)) :
    {x : B.stage i | ((c * s : ℕ) : ℕ∞) ≤ (B.markedTransformSeq (A ^ s) (c * s) i).ord x} =
      {x | (c : ℕ∞) ≤ (B.markedTransformSeq A c i).ord x} := by
  have _ := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h.1 i
  rw [markedTransformSeq_pow f n B A E c s h i]
  exact cosupp_pow (B.stageMap i ≫ f) n _ c hs

variable (S I : X.IdealSheafData) (m : ℕ) (T : BlowUpSequence S.subscheme)

include n in
/-- Lines 2–5 of [Kol07, 90] with [Kol07, Definition 83]: for `I` D-balanced with respect to `m`,
`S` a smooth hypersurface and `T` a smooth blow-up sequence of order `≥ m` starting with
`(S, I|_S, m)`, at every stage `i` the cosupport of `J_i = T_*^{-1}(I|_S, m)` lies in every
`cosupp T_*^{-1}((D^j I)|_S, m − j)`, `j < m` — the chain of the module docstring, pointwise at
`y ∈ S_i`. -/
theorem cosupp_markedTransformSeq_subset_iInter (hI : I.IsDBalanced f m) (hS : IsSmoothDivisor S)
    {E' : DivisorFamily S.subscheme}
    (hT : T.IsOrderGeSeq (S.subschemeι ≫ f) (I.comap S.subschemeι) m E')
    (i : Fin (T.length + 1)) :
    {y : T.stage i | (m : ℕ∞) ≤ (T.markedTransformSeq (I.comap S.subschemeι) m i).ord y} ⊆
      ⋂ j < m, {y | ((m - j : ℕ) : ℕ∞) ≤ (T.markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j) i).ord y} := by
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro j hj
  -- the stage `S_i` is smooth of relative dimension `n − 1`
  have hsmS : SmoothOfRelativeDimension (n - 1) (S.subschemeι ≫ f) :=
    smoothOfRelativeDimension_of_isSmoothDivisor f n S hS
  have _ := IsSmooth.smoothOfRelativeDimension_stageMap (n := n - 1) hT.1 i
  have hmj : 1 ≤ m - j := Nat.sub_pos_of_lt hj
  have hm1 : 1 ≤ m := le_trans hmj (Nat.sub_le m j)
  set fi := T.stageMap i ≫ (S.subschemeι ≫ f) with hfi
  -- Step 1 (`cosupp_pow` on the stage): `m ≤ ord J_i ↔ m(m−j) ≤ ord J_i^{m−j}`.
  have h1 : ((m * (m - j) : ℕ) : ℕ∞) ≤
      ((T.markedTransformSeq (I.comap S.subschemeι) m i) ^ (m - j)).ord y := by
    have := cosupp_pow fi (n - 1) (T.markedTransformSeq (I.comap S.subschemeι) m i) m hmj
    exact (Set.ext_iff.mp this y).mpr hy
  -- Step 2 (the power rule, equality under the order hypothesis on `T`).
  rw [← markedTransformSeq_pow (S.subschemeι ≫ f) (n - 1) T (I.comap S.subschemeι) E' m (m - j)
    hT i] at h1
  -- Step 3 (D-balancedness restricted to `S`): `(D^j I)^m ≤ I^{m−j}`.
  have hle : ((I.derivativeIter f j) ^ m).comap S.subschemeι ≤
      (I.comap S.subschemeι) ^ (m - j) := by
    rw [← IdealSheafData.comap_pow]
    exact IdealSheafData.comap_mono S.subschemeι (hI j hj)
  have h3 : ((m * (m - j) : ℕ) : ℕ∞) ≤
      (T.markedTransformSeq (((I.derivativeIter f j) ^ m).comap S.subschemeι) (m * (m - j))
        i).ord y :=
    h1.trans (IdealSheafData.ord_anti (markedTransformSeq_mono T hle _ i) y)
  -- Step 4 (the unconditional power inclusion): `(T_*^{-1}((D^j I)|_S, m−j))^m ≤ T_*^{-1}(…)`.
  have h4 : (T.markedTransformSeq ((I.derivativeIter f j).comap S.subschemeι) (m - j) i) ^ m ≤
      T.markedTransformSeq (((I.derivativeIter f j) ^ m).comap S.subschemeι) (m * (m - j)) i := by
    have := pow_markedTransformSeq_le ((I.derivativeIter f j).comap S.subschemeι)
      (((I.derivativeIter f j).comap S.subschemeι) ^ m) (m - j) m T le_rfl i
    rwa [Nat.mul_comm (m - j) m, ← IdealSheafData.comap_pow] at this
  have h5 : ((m * (m - j) : ℕ) : ℕ∞) ≤
      ((T.markedTransformSeq ((I.derivativeIter f j).comap S.subschemeι) (m - j) i) ^ m).ord y :=
    h3.trans (IdealSheafData.ord_anti h4 y)
  -- Step 5 (`cosupp_pow` again, with the roles `c = m − j`, `s = m`).
  have h6 := cosupp_pow fi (n - 1)
    (T.markedTransformSeq ((I.derivativeIter f j).comap S.subschemeι) (m - j) i) (m - j) hm1
  rw [Nat.mul_comm (m - j) m] at h6
  exact (Set.ext_iff.mp h6 y).mp h5

end Chain

end Hironaka.Sequence
