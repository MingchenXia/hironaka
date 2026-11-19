/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
public import Hironaka.Scheme.Snc.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivAffine
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor
import Hironaka.Resolution.Algebraic.MaximalContact.Theorem97
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The blow-up sequence functor does not depend on the hypersurface of maximal contact

[Kol07, Theorem 103, Step 2.3] observes that Step 2.2 relies on a hypersurface of maximal contact
`H` that is not unique, and argues: for two such hypersurfaces `H, H'` with `H + E` and `H' + E`
simple normal crossing divisors, and `I` MC-invariant, Theorem 92 makes `(X, I, H + E)` and
`(X, I, H' + E)` étale equivalent, hence the two blow-up sequences `BD_{n,m,0}(X, I, H + E)` and
`BD_{n,m,0}(X, I, H' + E)` are étale equivalent, hence by Theorem 97 identical.

The three steps are three theorems of this library: Theorem 92 in the affine form
(`exists_etaleEquiv_isAffine`), the étale equivalence of the outputs of a functor commuting with
smooth morphisms (`etaleEquivSeq_of_functor`, the functoriality [Kol07, 34.1] without deleting
empty blow-ups, since the images of `ψ, ψ'` contain the cosupport), and Theorem 97
(`eq_of_etaleEquivSeq`). The affine `U` of the equivalence supplies the hypotheses that
`etaleEquivSeq_of_functor` places on `U` (the Lean form of [Kol07, 34.1]): quasi-compact and
separated over `k` (an affine scheme over an affine base), of finite type (étale over `X`, which
is of finite type over `k`), smooth of relative dimension `n` (étale over `X`, which is smooth of
relative dimension `n`). The class `Dom` of the
functor is assumed closed under pull-back along such étale maps whose image contains the cosupport
(`ClosedUnderEtalePullbackOverCosupp`), the domain half of "commutes with étale morphisms whose
image contains the cosupport";
`Hironaka/Resolution/Algebraic/BoundaryClearing/ClassEtalePullback.lean` proves it for the class of
triples of [Kol07, Lemma 102], and `Hironaka/Resolution/Algebraic/OrderReduction/Step22Indep.lean`
applies the theorem to the functor `BD_{n,m,j}` of that lemma.

Kollár's "hypersurface of maximal contact" is taken in the static form `IsMaximalContact`
(`𝒪_X(−H) ⊆ MC(I)`, the hypothesis of [Kol07, Theorem 80 (1)]), as in Theorem 92; smoothness of
`H, H'` is not a separate hypothesis, since it follows from `E + H` and `E + H'` being simple
normal crossing (the triple's `isSnc` field and `hsnc'`), which is all that Theorem 92 requires.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Hironaka Scheme AlgebraicGeometry Algebra

variable {k : Type u} [Field k]

/-- The class `Dom` of triples is **closed under étale pull-back over the `m`-cosupport**: for
every triple `T` of the class and every étale `h : Y ⟶ T.X.left` over `k` from a scheme `Y` carrying
the hypotheses `etaleEquivSeq_of_functor` places on its base (the Lean form of [Kol07, 34.1]) whose
image contains `cosupp(T.I, m)`, the pulled-back triple
(`Triple.pullback`) is in the class. This is the domain half of "commutes with étale morphisms
whose image contains the cosupport". -/
def ClosedUnderEtalePullbackOverCosupp [CharZero k] (Dom : Triple k → Prop) (m : ℕ) : Prop :=
  ∀ (T : Triple k), Dom T → ∀ {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k)))
    (h : Y ⟶ T.X.left) [h.IsOver (Spec (.of k))] [Etale h],
    {x | (m : ℕ∞) ≤ T.I.ord x} ⊆ Set.range h.base → Dom (T.pullback hY h)

/-- **Independence of the hypersurface of maximal contact** ([Kol07, Theorem 103, Step 2.3],
"By (97) this implies that these blow-up sequences are identical"): for a smooth blow-up sequence
functor `B` of order `m` commuting with smooth morphisms, whose class `Dom` is closed under
pull-back along étale morphisms over `k` (from schemes carrying the hypotheses that
`etaleEquivSeq_of_functor` places on its base, the Lean form of [Kol07, 34.1]) whose image
contains `cosupp(I, m)`, a triple `T = (X, I, E + H)` of the class and
`T' = (X, I, E + H')` in the class with `E + H'` simple normal crossing, if `m ≥ 1`, `I` is
MC-invariant and `H, H'` are hypersurfaces of maximal contact for `(I, m)`, then
`B(X, I, E + H) = B(X, I, E + H')`. Smoothness of `H, H'` follows from the simple normal crossings
of `E + H` and `E + H'` and is not a separate hypothesis. -/
theorem functor_independent_of_maximalContact [CharZero k] {m : ℕ} {Dom : Triple k → Prop}
    (B : OrderSeqAssignment k m Dom) (hB : B.CommutesWithSmooth)
    (hDom : ∀ (T : Triple k), Dom T → ∀ {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
      (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k)))
      (h : Y ⟶ T.X.left) [h.IsOver (Spec (.of k))] [Etale h],
      {x | (m : ℕ∞) ≤ T.I.ord x} ⊆ Set.range h.base → Dom (T.pullback hY h))
    (T : Triple k) (hT : Dom T) (E : DivisorFamily T.X.left) (H H' : T.X.left.IdealSheafData)
    (hE : T.E = E.append H) (hsnc' : (E.append H').IsSnc)
    (hT' : Dom { T with E := E.append H', isSnc := hsnc' }) (hm : 1 ≤ m)
    (hI : IsMCInvariant (T.X.left ↘ Spec (.of k)) T.I m)
    (hH : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (hH' : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H') :
    B.seq T hT = B.seq { T with E := E.append H', isSnc := hsnc' } hT' := by
  classical
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hHE : (E.append H).IsSnc := hE ▸ T.isSnc
  -- Theorem 92 with an affine `U`
  obtain ⟨Q, hQ⟩ :=
    exists_etaleEquiv_isAffine (T.X.left ↘ Spec (.of k)) n T.I hm hI E H H' hH hH' hHE hsnc'
  -- the hypotheses of `etaleEquivSeq_of_functor` on `U`
  let _ : Q.U.Over (Spec (.of k)) := ⟨Q.ψ ≫ (T.X.left ↘ Spec (.of k))⟩
  have : Q.ψ.IsOver (Spec (.of k)) := ⟨rfl⟩
  have := Q.isOver_ψ'
  have : LocallyOfFiniteType (Q.U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (Q.ψ ≫ (T.X.left ↘ Spec (.of k))))
  have : QuasiCompact (Q.U ↘ Spec (.of k)) := inferInstance
  have : IsSeparated (Q.U ↘ Spec (.of k)) := inferInstance
  have hU : ∃ n : ℕ, SmoothOfRelativeDimension n (Q.U ↘ Spec (.of k)) := by
    refine ⟨n, ?_⟩
    have h0 : SmoothOfRelativeDimension (0 + n) (Q.ψ ≫ (T.X.left ↘ Spec (.of k))) := inferInstance
    simpa using h0
  -- the pulled-back triples are in the class
  have hDU := hDom T hT hU Q.ψ Q.covers
  have hDU' := hDom { T with E := E.append H', isSnc := hsnc' } hT' hU Q.ψ' Q.covers'
  -- the outputs are étale equivalent …
  obtain ⟨e⟩ := etaleEquivSeq_of_functor B hB T hT E H H' hE hsnc' hT' Q hU hDU hDU'
  -- … hence equal (Theorem 97)
  exact eq_of_etaleEquivSeq (T.X.left ↘ Spec (.of k)) n hm (B.isOrderSeq T hT)
    (B.isOrderSeq _ hT') e

/-- `functor_independent_of_maximalContact` with the closure hypothesis by name
(`ClosedUnderEtalePullbackOverCosupp`). -/
theorem functor_independent_of_maximalContact_of_closed [CharZero k] {m : ℕ}
    {Dom : Triple k → Prop} (B : OrderSeqAssignment k m Dom) (hB : B.CommutesWithSmooth)
    (hDom : ClosedUnderEtalePullbackOverCosupp Dom m) (T : Triple k) (hT : Dom T)
    (E : DivisorFamily T.X.left) (H H' : T.X.left.IdealSheafData) (hE : T.E = E.append H)
    (hsnc' : (E.append H').IsSnc) (hT' : Dom { T with E := E.append H', isSnc := hsnc' })
    (hm : 1 ≤ m) (hI : IsMCInvariant (T.X.left ↘ Spec (.of k)) T.I m)
    (hH : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (hH' : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H') :
    B.seq T hT = B.seq { T with E := E.append H', isSnc := hsnc' } hT' :=
  functor_independent_of_maximalContact B hB hDom T hT E H H' hE hsnc' hT' hm hI hH hH'

end AlgebraicGeometry.Scheme.IdealSheafData
