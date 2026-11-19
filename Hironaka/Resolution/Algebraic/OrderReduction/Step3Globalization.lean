/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.GlobalizeDescent
public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.Kol07.MaximalContactGlobalization
import Hironaka.Resolution.Algebraic.MaximalContact.PullbackSmooth
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
public import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Indep
import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 3 of order reduction: the local class, the local functor and the globalised functor

Step 3 of the proof of [Kol07, Theorem 103] removes the assumption of a global hypersurface of
maximal contact: `X` is covered by open subsets `X^(j)` on each of which a smooth hypersurface of
maximal contact `H^(j)` exists, the disjoint union `H^* = ∐ H^(j) ⊂ ∐ X^(j) = X^*` is a smooth
hypersurface of maximal contact for the pulled-back data, Step 2 defines `BO_{n,m}` on
`(X^*, g^* I, g^{-1} E)` for the coproduct `g : X^* → X` of the inclusions, and the value descends
to `BO_{n,m}(X, I, E)` by the argument of [Kol07, Proposition 37]. The descent is
[Kol07, Theorem 105] for the class `M` of coproducts of open immersions, formalised as
`OrderSeqAssignment.globalize` in `Hironaka/Resolution/Algebraic/Kol07/GlobalizeDescent.lean`. This
module supplies its inputs.

* `BO.localClass n m` is the class of local triples `LT` of Theorem 105: the members of
  `BOClass n m` (`1 ≤ m`, `dim X ≤ n`, `max-ord I ≤ m`) admitting a global smooth hypersurface of
  maximal contact (`HasMaximalContact`). The class of global triples `GT` is `BOClass n m` itself.
  Kollár states Theorem 103 for `dim X = n`; the class here has `dim X ≤ n`, so the results on
  hypersurfaces of maximal contact for triples of exact dimension
  (`Hironaka/Resolution/Algebraic/MaximalContact/`) are applied at each triple's own dimension.
* The class lemmas: stability under open-immersion coproducts, closure under finite disjoint
  unions (`closedUnderSigma_hasDimLE`: a triple is equidimensional, so every nonempty piece of a
  disjoint union has the union's relative dimension, at most `n`), the local covers
  (`exists_isPullbackOf_localClass`), hence hypotheses (2)(i)–(ii) of Theorem 105 as
  `globalizationData_localClass`, and the closure of local covers under fibre products
  (`localCoversFibreClosed_localClass`), which the descent uses for the fibre product
  `X' ×_X X'` of Kollár's proof.
* `BO.localFunctor n m bd` is Step 2's functor on the local class: the value at `T` is the
  maximal-contact case `maxContactCase` for a chosen hypersurface of maximal contact
  (`Classical.choose`); it does not depend on the choice (`localFunctor_seq`, by
  `maxContactCase_indep`), and it commutes with smooth surjections by
  `maxContactCase_pullback_of_surjective`, after the chosen hypersurface on the pulled-back triple
  is exchanged for the pulled-back one, which is hypothesis (3) of Theorem 105.
* `BO.functor n m bd` is the unique extension of Theorem 105: `OrderSeqAssignment.globalize` on
  these inputs, a smooth blow-up sequence functor of order `m` on `BOClass n m`. On the local class
  it is `maxContactCase` for any hypersurface of maximal contact (`functor_seq_localClass`).

Clauses (1)–(2) of Theorem 103 for `BO.functor` are proved in
`Hironaka/Resolution/Algebraic/OrderReduction/Step3Clauses.lean`, and the data `BOData n m` are
assembled in `Hironaka/Resolution/Algebraic/OrderReduction/Step3Data.lean`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.BlowUpSequence Hironaka.Sequence Hironaka.Snc Scheme.IdealSheafData

namespace Hironaka.BO

section Classes

variable {k : Type u} [Field k]

/-- The **local triples** `LT_{n,m}` of Step 3 of the proof of [Kol07, Theorem 103] (the class
`LT` of [Kol07, Theorem 105 (2)]): the members of `BOClass n m` admitting a global smooth
hypersurface of maximal contact (`HasMaximalContact`). -/
def localClass (n m : ℕ) (T : Triple k) : Prop :=
  Triple.BOClass n m T ∧ T.HasMaximalContact m

variable {T T' : Triple k} {g : T'.X.left ⟶ T.X.left}

/-- A smooth morphism from an empty scheme has every relative dimension: the defining condition is
a statement about points. -/
theorem smoothOfRelativeDimension_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] (n : ℕ) :
    SmoothOfRelativeDimension n f :=
  ⟨fun x => isEmptyElim x⟩

/-- `dim X ≤ n` is stable under open-immersion coproducts (`Triple.HasDim.isPullbackOf` at the
triple's own dimension). -/
theorem hasDimLE_isPullbackOf {n : ℕ} (hT : T.HasDimLE n) (hg : openImmersionCoprods g)
    (hT' : T'.IsPullbackOf T g) : T'.HasDimLE n := by
  obtain ⟨n', hn', hd⟩ := hT
  exact ⟨n', hn', Triple.HasDim.isPullbackOf hd hg hT'⟩

/-- `max-ord I ≤ m` is stable under open-immersion coproducts (`maxOrd_comap_le_of_smooth`). -/
theorem maxOrd_le_of_isPullbackOf {m : ℕ} (hT : T.I.maxOrd ≤ (m : ℕ∞))
    (hg : openImmersionCoprods g) (hT' : T'.IsPullbackOf T g) : T'.I.maxOrd ≤ (m : ℕ∞) := by
  have := openImmersionCoprods.smooth hg
  rw [hT'.2.1]
  exact (maxOrd_comap_le_of_smooth g T.I).trans hT

/-- The class `BOClass n m` is stable under open-immersion coproducts. -/
theorem boClass_isPullbackOf {n m : ℕ} (hT : Triple.BOClass n m T) (hg : openImmersionCoprods g)
    (hT' : T'.IsPullbackOf T g) : Triple.BOClass n m T' :=
  ⟨hT.1, hasDimLE_isPullbackOf hT.2.1 hg hT', maxOrd_le_of_isPullbackOf hT.2.2 hg hT'⟩

/-- The local class is stable under open-immersion coproducts ([Kol07, Theorem 105 (2)];
`HasMaximalContact.isPullbackOf`). -/
theorem localClass_isPullbackOf {n m : ℕ} (hT : localClass n m T) (hg : openImmersionCoprods g)
    (hT' : T'.IsPullbackOf T g) : localClass n m T' :=
  ⟨boClass_isPullbackOf hT.1 hg hT', hT.2.isPullbackOf hg hT'⟩

/-- `dim X ≤ n` is closed under finite disjoint unions (Step 3 of the proof of
[Kol07, Theorem 103]): a triple is equidimensional (`Triple.smoothOfRelativeDimension`), every
nonempty piece of a disjoint union is an open of it and so has the union's relative dimension `d`
(`HasDim.isPullbackOf`), and the relative dimension of a smooth morphism with nonempty source is
unique (`SmoothOfRelativeDimension.eq_of_nonempty`), so `d` is the piece's dimension, at most `n`;
if every piece is empty so is the union, and every relative dimension holds. -/
theorem closedUnderSigma_hasDimLE (n : ℕ) :
    Triple.ClosedUnderSigma (fun T : Triple k => T.HasDimLE n) := by
  intro σ _ _ Ts T ι h hD
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  by_cases hne : Nonempty T.X.left
  · obtain ⟨x⟩ := hne
    obtain ⟨i, y, -⟩ := exists_eq_of_isColimit_cofan ι h.1 x
    obtain ⟨n', hn', hdi⟩ := hD i
    have : IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι h.1 i
    have hpb : (Ts i).IsPullbackOf T (ι i) := ⟨h.2.1 i, h.2.2.1 i, h.2.2.2 i⟩
    have hdd : (Ts i).HasDim d :=
      Triple.HasDim.isPullbackOf (hd : T.HasDim d) (openImmersionCoprods_of_isOpenImmersion (ι i))
        hpb
    have : Nonempty (Ts i).X.left := ⟨y⟩
    have hdn : d = n' :=
      SmoothOfRelativeDimension.eq_of_nonempty ((Ts i).X.left ↘ Spec (.of k)) (hn :=
        hdd) (hm := hdi)
    exact ⟨d, hdn ▸ hn', hd⟩
  · have : IsEmpty T.X.left := not_nonempty_iff.mp hne
    exact ⟨n, le_rfl, smoothOfRelativeDimension_of_isEmpty _ n⟩

/-- The class `BOClass n m` is closed under finite disjoint unions ([Kol07, Theorem 105 (2)(ii)];
`Triple.closedUnderSigma_maxOrd_le` for the order). -/
theorem closedUnderSigma_boClass (n m : ℕ) :
    Triple.ClosedUnderSigma (Triple.BOClass (k := k) n m) := by
  change Triple.ClosedUnderSigma
    (fun T : Triple k => 1 ≤ m ∧ T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞))
  refine Triple.ClosedUnderSigma.and (D₁ := fun _ : Triple k => 1 ≤ m)
    (D₂ := fun T : Triple k => T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞)) ?_ ?_
  · intro σ _ _ Ts T ι _ hD
    exact hD (Classical.arbitrary σ)
  · exact Triple.ClosedUnderSigma.and (D₁ := fun T : Triple k => T.HasDimLE n)
      (D₂ := fun T : Triple k => T.I.maxOrd ≤ (m : ℕ∞)) (closedUnderSigma_hasDimLE n)
      (Triple.closedUnderSigma_maxOrd_le m)

/-- The local class is closed under finite disjoint unions ([Kol07, Theorem 105 (2)(ii)]; Step 3
of the proof of [Kol07, Theorem 103]: "`H^* := ∐ H^(j) ⊂ ∐ X^(j) =: X^*` is a smooth hypersurface
of maximal contact"), by `Triple.closedUnderSigma_hasMaximalContact`. -/
theorem closedUnderSigma_localClass (n m : ℕ) :
    Triple.ClosedUnderSigma (localClass (k := k) n m) :=
  Triple.ClosedUnderSigma.and (D₁ := Triple.BOClass n m)
    (D₂ := fun T : Triple k => T.HasMaximalContact m) (closedUnderSigma_boClass n m)
    (Triple.closedUnderSigma_hasMaximalContact m)

/-- Every point of a triple of `BOClass n m` has an open neighbourhood, an open-immersion
coproduct into the triple, carrying a local triple (Step 3 of the proof of [Kol07, Theorem 103],
by [Kol07, Theorem 80 (2)]; `Triple.exists_isPullbackOf_maximalContactClass` at the triple's own
dimension). -/
theorem exists_isPullbackOf_localClass [CharZero k] (n m : ℕ) (T : Triple k)
    (hT : Triple.BOClass n m T) (x : T.X.left) :
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left), openImmersionCoprods g ∧ x ∈ Set.range g ∧
      T'.IsPullbackOf T g ∧ localClass n m T' := by
  obtain ⟨n', hn', hd⟩ := hT.2.1
  obtain ⟨T', g, hg, hx, hpb, ⟨hd', hmax'⟩, hmc⟩ :=
    Triple.exists_isPullbackOf_maximalContactClass n' m T ⟨hd, hT.2.2⟩ x
  exact ⟨T', g, hg, hx, hpb, ⟨hT.1, ⟨n', hn', hd'⟩, hmax'⟩, hmc⟩

/-- Hypotheses (2)(i)–(ii) of [Kol07, Theorem 105] for `M` the coproducts of open immersions,
`GT = BOClass n m` and `LT = localClass n m`: the instance that Step 3 of the proof of
[Kol07, Theorem 103] feeds to Theorem 105. -/
theorem globalizationData_localClass [CharZero k] (n m : ℕ) :
    Triple.GlobalizationData openImmersionCoprods (Triple.BOClass (k := k) n m)
      (localClass n m) where
  exists_isPullbackOf := exists_isPullbackOf_localClass n m
  closedUnderSigma := closedUnderSigma_localClass n m

/-- The fibre triple of two local covers is in the local class (the triple over `X'' = X' ×_X X'`
in the proof of [Kol07, Theorem 105] is again a local triple): the projection is a base change of
an open-immersion coproduct (`isStableUnderBaseChange_openImmersionCoprods`) and the class is
stable along it. -/
theorem localCoversFibreClosed_localClass (n m : ℕ) :
    Triple.LocalCoversFibreClosed openImmersionCoprods (Triple.BOClass (k := k) n m)
      (localClass n m) := by
  intro T T₁ T₂ g₁ g₂ hc₁ hc₂ T₁₂ p₁ p₂ sq hpb
  have hp₁ : openImmersionCoprods p₁ :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq.flip hc₂.2.2.1
  exact localClass_isPullbackOf hc₁.2.1 hp₁ hpb

end Classes

section Functor

variable {k : Type u} [Field k] [CharZero k] (n m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j)

/-- **Step 2's functor on the local triples** (Step 3 of the proof of [Kol07, Theorem 103]: "by the
previous step `BO_{n,m}` is defined on `(X^*, g^* I, g^{-1} E)`"): the value at `T` is
`maxContactCase` for a chosen smooth hypersurface of maximal contact (`Classical.choose` on
`HasMaximalContact`); the two functor fields are `isOrderSeq_maxContactCase` and
`noEmptyCenters_maxContactCase`. The value does not depend on the choice (`localFunctor_seq`, by
`maxContactCase_indep`). -/
noncomputable def localFunctor : OrderSeqAssignment k m (localClass n m) where
  seq T hT :=
    maxContactCase T hT.1 (Classical.choose_spec hT.2).1 (Classical.choose_spec hT.2).2 bd
  isOrderSeq T hT := isOrderSeq_maxContactCase T hT.1 _ _ bd
  noEmptyCenters T hT := noEmptyCenters_maxContactCase T hT.1 _ _ bd

/-- The local functor's value is `maxContactCase` for any smooth hypersurface of maximal contact
([Kol07, 104, Step 2.3], through `maxContactCase_indep`). -/
theorem localFunctor_seq (T : Triple k) (hT : localClass n m T) {H : T.X.left.IdealSheafData}
    (hH : IsSmoothDivisor H) (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec
        (.of k)) T.I m H) :
    (localFunctor n m bd).seq T hT = maxContactCase T hT.1 hH hle bd :=
  maxContactCase_indep T hT.1 (Classical.choose_spec hT.2).1 (Classical.choose_spec hT.2).2 hH hle
    bd

/-- The local functor commutes with smooth surjections (hypothesis (3) of [Kol07, Theorem 105],
from [Kol07, 104, Step 2.3] as `maxContactCase_pullback_of_surjective`): on the pulled-back triple
the chosen hypersurface is exchanged for the pulled-back one (`localFunctor_seq` with
`isSmoothDivisor_comap_of_smooth` and `isMaximalContact_comap_of_smooth`). -/
theorem localFunctor_commutesWithSmoothSurjections :
    (localFunctor (k := k) n m bd).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hpb hT hT'
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hH' : IsSmoothDivisor ((Classical.choose hT.2).comap h) :=
    isSmoothDivisor_comap_of_smooth (T.X.left ↘ Spec (.of k)) h (Classical.choose_spec hT.2).1
  have hle' : Scheme.IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of k)) T'.I m
      ((Classical.choose hT.2).comap h) := by
    have := Scheme.IdealSheafData.isMaximalContact_comap_of_smooth (T.X.left ↘ Spec (.of k)) d h
      (Classical.choose_spec hT.2).2
    rwa [hpb.1, ← hpb.2.1] at this
  rw [localFunctor_seq n m bd T' hT' hH' hle']
  exact maxContactCase_pullback_of_surjective T hT.1 (Classical.choose_spec hT.2).1
    (Classical.choose_spec hT.2).2 bd hT'.1 h hs hpb hH' hle'

/-- Hypothesis (3) of [Kol07, Theorem 105] for `M` the coproducts of open immersions
(`CommutesWithSmoothSurjections.commutesWithSurjectionsIn`). -/
theorem localFunctor_commutesWithSurjectionsIn :
    (localFunctor (k := k) n m bd).CommutesWithSurjectionsIn openImmersionCoprods :=
  (localFunctor_commutesWithSmoothSurjections n m bd).commutesWithSurjectionsIn
    isGlobalizationClass_openImmersionCoprods

/-- **The order-reduction functor `BO_{n,m}`** (Step 3 of the proof of [Kol07, Theorem 103]: "we
argue as in (37) to prove that `BO_{n,m}(X^*, g^* I, g^{-1} E)` descends to give
`BO_{n,m}(X, I, E)`"; [Kol07, Theorem 105]): the unique extension of the local functor to the
class `BOClass n m` commuting with surjective open-immersion coproducts,
`OrderSeqAssignment.globalize` on the instances above. -/
noncomputable def functor : OrderSeqAssignment k m (Triple.BOClass n m) :=
  OrderSeqAssignment.globalize (globalizationData_localClass n m)
    (localCoversFibreClosed_localClass n m) (localFunctor n m bd)
    (localFunctor_commutesWithSurjectionsIn n m bd)

/-- On a triple with a smooth hypersurface of maximal contact `H`, `BO_{n,m}` is Step 2's
`maxContactCase` for `H` (the extension property of [Kol07, Theorem 105]: the extension agrees with
the functor on the local triples; `globalize_seq_of_mem`). -/
theorem functor_seq_localClass (T : Triple k) (hT : Triple.BOClass n m T)
    {H : T.X.left.IdealSheafData}
    (hH : IsSmoothDivisor H) (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec
        (.of k)) T.I m H) :
    (functor n m bd).seq T hT = maxContactCase T hT hH hle bd :=
  (OrderSeqAssignment.globalize_seq_of_mem (globalizationData_localClass n m)
    (localCoversFibreClosed_localClass n m) (localFunctor n m bd)
    (localFunctor_commutesWithSurjectionsIn n m bd) (hL := ⟨hT, H, hH, hle⟩) hT).trans
    (localFunctor_seq n m bd T ⟨hT, H, hH, hle⟩ hH hle)

end Functor

end Hironaka.BO
