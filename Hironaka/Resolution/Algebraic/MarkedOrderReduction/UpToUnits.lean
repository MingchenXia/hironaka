/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step2Separation
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.LoopFunctorial
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialExtendsByEmpty
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Pull-back of a marked triple up to unit boundary members

The second clause of [Kol07, 34.1] and the convention [Kol07, 32]: along an arbitrary smooth
`h : Y → X` the rounds of Steps 1 and 2 of the proof of [Kol07, Theorem 107] whose parameters
exceed those of `Y` pull back to empty blow-ups, which are deleted; their exceptional divisors
survive as unit members of the boundary of the pulled-back data. The invariant of the loops is
therefore not the exact pull-back relation `T'.IsPullbackOf T h` but its version **up to unit
members**: `T'` has the structure morphism, the ideal and the mark of the pull-back of `T`, and its
boundary is the pull-back boundary with unit-ideal members deleted (`IsTopErasure`; the fourth
conjunct of the skipped-round lemma `pullback_eraseEmpty_eq_nil_of_maxOrd_lt` of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SkippedRound.lean` produces exactly this). This
module collects the bookkeeping of that relation.

* The split of [Kol07, Definition–Lemma 110] ignores unit members
  (`DivisorFamily.monomial_of_extendsByEmpty` in
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/MonomialExtendsByEmpty.lean`: a unit member
  has no irreducible components, so its factor in the monomial ideal is `1`), hence so do `M(I)`,
  `N(I)` and the round parameters (`nonmonomialPart_of_extendsByEmpty`, `roundOrder_fullPullback`,
  `sepOrder_fullPullback`).
* The **full pull-back** `fullPullback T' T h`, the boundary restored to `h^{-1} E`, is an exact
  pull-back (`fullPullback_isPullbackOf`), and its round triple is the round triple of `T'` with
  unit members appended (`nonmonomialTriple_fullPullback`), the shape in which the indifference of
  the input functors and the second clause of [Kol07, 34.1] for [Kol07, Theorem 103] apply.
* The relation passes to the marked triples induced at the end of the erased pull-back of a
  sequence of order `≥ m`, along `eraseEmptyLastHom ≫ pullbackLastHom`
  (`IsPullbackOfUpToUnits.induced_eraseEmpty`): the ideal by the transport of the induced triple
  along the last-stage lift and the erasure identity `markedTransformSeq_eraseEmpty_last`
  (`Hironaka/Resolution/Algebraic/Kol07/EraseEmptyInduced.lean`), the boundary by
  `eraseEmbeds_eraseEmpty` composed with `exists_isTopErasure_totalTransformSeq`.

These facts drive the functoriality of the loops for an arbitrary smooth morphism
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothLoop.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.BMO

variable {X : Scheme.{u}}

/-- The monomial part ignores unit members ([Kol07, Definition–Lemma 110] with the convention
[Kol07, 32]). -/
theorem monomialPart_of_extendsByEmpty (I : X.IdealSheafData) {E' E : DivisorFamily X}
    (hext : ExtendsByEmpty E' E) : monomialPart I E = monomialPart I E' :=
  DivisorFamily.monomial_of_extendsByEmpty hext _

/-- The nonmonomial part ignores unit members. -/
theorem nonmonomialPart_of_extendsByEmpty (I : X.IdealSheafData) {E' E : DivisorFamily X}
    (hext : ExtendsByEmpty E' E) : nonmonomialPart I E = nonmonomialPart I E' := by
  unfold nonmonomialPart
  rw [monomialPart_of_extendsByEmpty I hext]

end Hironaka.BMO

namespace Hironaka.MarkedTriple

open Scheme IdealSheafData

variable {k : Type u} [Field k]

/-- **`T'` is the pull-back of `T` along `h` up to unit boundary members** (the second clause of
[Kol07, 34.1] with the convention [Kol07, 32]): the structure morphism, the ideal and the mark of
`T'` are those of the pull-back, and its boundary is the pull-back boundary `h^{-1} E` with
unit-ideal members deleted (`IsTopErasure`). The exact pull-back is the case of no deletion; the
data after a skipped round are the case of the deleted exceptional divisors. -/
def IsPullbackOfUpToUnits (T' T : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) : Prop :=
  h ≫ (T.X.left ↘ Spec (.of k)) = T'.X.left ↘ Spec (.of k) ∧ T'.I = T.I.comap h ∧ T'.m = T.m ∧
    ∃ e : T'.E.ι ↪o (T.E.comap h).ι, IsTopErasure T'.E (T.E.comap h) e

/-- An exact pull-back is a pull-back up to unit members (no deletion). -/
theorem IsPullbackOf.upToUnits {T T' : MarkedTriple k} {h : T'.X.left ⟶ T.X.left}
    (hp : T'.IsPullbackOf T h) : T'.IsPullbackOfUpToUnits T h := by
  obtain ⟨⟨hover, hI, hE⟩, hm⟩ := hp
  refine ⟨hover, hI, hm, ?_⟩
  rw [hE]
  exact ⟨_, IsTopErasure.refl _⟩

/-- Deleting unit members of the boundary is a pull-back up to unit members along the identity (the
shape of `IndifferentToEmptyMembers`). -/
theorem isPullbackOfUpToUnits_id (T : MarkedTriple k) (E' : DivisorFamily T.X.left)
    (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι) (hmem : ∀ i, T.E.component (e i) = E'.component i)
    (htop : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) :
    ({ T with E := E', isSnc := hsnc' } : MarkedTriple k).IsPullbackOfUpToUnits T (𝟙 T.X.left) := by
  refine ⟨Category.id_comp _, (Scheme.IdealSheafData.comap_id _).symm, rfl, ?_⟩
  rw [DivisorFamily.comap_id]
  exact ⟨e, hmem, htop⟩

/-- Two triples differing only in the ideal are equal when the ideals are. -/
theorem Triple_mk_I_congr (T₀ : Triple k) {J₁ J₂ : T₀.X.left.IdealSheafData} (e : J₁ = J₂)
    (h₁ : IsNonzeroEverywhere J₁) (h₂ : IsNonzeroEverywhere J₂) :
    ({ T₀ with I := J₁, isNonzeroEverywhere := h₁ } : Triple k) =
      { T₀ with I := J₂, isNonzeroEverywhere := h₂ } := by
  subst e
  rfl

variable [CharZero k]

/-- **The full pull-back**: `T'` with its boundary restored to the whole pull-back boundary
`h^{-1} E`, which has normal crossings by `isSnc_comap_of_smooth`. -/
noncomputable def fullPullback (T' T : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h] :
    MarkedTriple k :=
  { T' with
    E := T.E.comap h
    isSnc := by
      have := T.smooth
      exact isSnc_comap_of_smooth (T.X.left ↘ Spec (.of k)) h T.isSnc }

variable {T T' : MarkedTriple k} {h : T'.X.left ⟶ T.X.left} [Smooth h]

/-- The full pull-back of a pull-back up to unit members is an exact pull-back. -/
theorem fullPullback_isPullbackOf (hp : T'.IsPullbackOfUpToUnits T h) :
    (fullPullback T' T h).IsPullbackOf T h :=
  ⟨⟨hp.1, hp.2.1, rfl⟩, hp.2.2.1⟩

/-- The full pull-back is in the class when `T'` is (the class does not see the boundary). -/
theorem fullPullback_bmoClass {n m : ℕ} (hT' : BMOClass n m T') :
    BMOClass n m (fullPullback T' T h) :=
  ⟨hT'.1, hT'.2.1, hT'.2.2⟩

/-- The boundary of `T'` is the boundary of its full pull-back with unit members deleted. -/
theorem isTopErasure_fullPullback (hp : T'.IsPullbackOfUpToUnits T h) :
    ∃ e : T'.E.ι ↪o (fullPullback T' T h).E.ι, IsTopErasure T'.E (fullPullback T' T h).E e :=
  hp.2.2.2

/-- The nonmonomial part of the full pull-back is that of `T'`: unit members are ignored. -/
theorem nonmonomialPart_fullPullback (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.nonmonomialPart (fullPullback T' T h).I (fullPullback T' T h).E =
      Hironaka.BMO.nonmonomialPart T'.I T'.E := by
  obtain ⟨e, he⟩ := hp.2.2.2
  exact Hironaka.BMO.nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty

/-- The nonmonomial part of `T'` is the inverse image of that of `T`, through the full pull-back
and `nonmonomialPart_comap`. -/
theorem nonmonomialPart_eq_comap_of_upToUnits (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.nonmonomialPart T'.I T'.E = (Hironaka.BMO.nonmonomialPart T.I T.E).comap h := by
  have : @Smooth (fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  rw [← nonmonomialPart_fullPullback hp]
  exact Hironaka.BMO.nonmonomialPart_comap (T' := (fullPullback T' T h).toTriple) T.toTriple h
    (fullPullback_isPullbackOf hp).1

/-- The round parameter of Step 1 for the full pull-back is that of `T'`. -/
theorem roundOrder_fullPullback (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.roundOrder (fullPullback T' T h) = Hironaka.BMO.roundOrder T' := by
  obtain ⟨e, he⟩ := hp.2.2.2
  change (Hironaka.BMO.nonmonomialPart T'.I (T.E.comap h)).maxOrd.toNat =
    (Hironaka.BMO.nonmonomialPart T'.I T'.E).maxOrd.toNat
  rw [Hironaka.BMO.nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty]

/-- The separation parameter of Step 2 for the full pull-back is that of `T'`. -/
theorem sepOrder_fullPullback (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.sepOrder (fullPullback T' T h) = Hironaka.BMO.sepOrder T' := by
  obtain ⟨e, he⟩ := hp.2.2.2
  change ((Hironaka.BMO.nonmonomialPart T'.I (T.E.comap h)).maxOrdAlong
      {x | (T'.m : ℕ∞) ≤ T'.I.ord x}).toNat =
    ((Hironaka.BMO.nonmonomialPart T'.I T'.E).maxOrdAlong {x | (T'.m : ℕ∞) ≤ T'.I.ord x}).toNat
  rw [Hironaka.BMO.nonmonomialPart_of_extendsByEmpty T'.I he.extendsByEmpty]

/-- The round triple `(Y, N(I'), E')` of `T'` is the round triple of its full pull-back with the
unit members deleted (the ideal `N(I', h^{-1} E) = N(I', E')`): the shape in which
`IndifferentToEmptyMembers` applies to the input functor. -/
theorem nonmonomialTriple_fullPullback (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.nonmonomialTriple T' =
      { T'.toTriple with
        I := Hironaka.BMO.nonmonomialPart (fullPullback T' T h).I (fullPullback T' T h).E
        isNonzeroEverywhere :=
          Hironaka.BMO.isNonzeroEverywhere_nonmonomialPart (fullPullback T' T h).toTriple } :=
  Triple_mk_I_congr T'.toTriple (nonmonomialPart_fullPullback hp).symm _ _

/-- The round parameter of Step 1 does not grow under a smooth pull-back (the second clause of
[Kol07, 34.1]): the order at a point is the order at its image. -/
theorem IsPullbackOfUpToUnits.roundOrder_le (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.roundOrder T' ≤ Hironaka.BMO.roundOrder T := by
  have h1 : (Hironaka.BMO.roundOrder T' : ℕ∞) ≤ Hironaka.BMO.roundOrder T := by
    rw [Hironaka.BMO.coe_roundOrder T', Hironaka.BMO.coe_roundOrder T,
      nonmonomialPart_eq_comap_of_upToUnits hp]
    exact Hironaka.BO.maxOrd_comap_le_of_smooth h _
  exact_mod_cast h1

/-- The separation parameter of Step 2 does not grow under a smooth pull-back (the second clause
of [Kol07, 34.1]). -/
theorem IsPullbackOfUpToUnits.sepOrder_le (hp : T'.IsPullbackOfUpToUnits T h) :
    Hironaka.BMO.sepOrder T' ≤ Hironaka.BMO.sepOrder T := by
  have h1 : (Hironaka.BMO.sepOrder T' : ℕ∞) ≤ Hironaka.BMO.sepOrder T := by
    rw [Hironaka.BMO.coe_sepOrder T', Hironaka.BMO.coe_sepOrder T,
      nonmonomialPart_eq_comap_of_upToUnits hp, maxOrdAlong_le_iff]
    intro y hy
    rw [ord_comap_of_smooth]
    refine le_maxOrdAlong (I := Hironaka.BMO.nonmonomialPart T.I T.E) ?_
    change (T.m : ℕ∞) ≤ T.I.ord (h y)
    have hy' : (T'.m : ℕ∞) ≤ T'.I.ord y := hy
    rwa [hp.2.2.1, hp.2.1, ord_comap_of_smooth] at hy'
  exact_mod_cast h1

end Hironaka.MarkedTriple

namespace Hironaka.MarkedTriple

open Scheme

variable {k : Type u} [Field k] [CharZero k]

/-- **The relation up to unit members passes to the induced marked triples at the end of the
erased pull-back** of a smooth blow-up sequence of order `≥ m` (the second clause of
[Kol07, 34.1] with [Kol07, Definition 66]), along the last-stage isomorphism followed by the
last-stage lift: the ideal by the transport of the induced triple along the last-stage lift
(`isPullbackOf_induced_last` on the full pull-back) and the erasure identity
(`markedTransformSeq_eraseEmpty_last`), the boundary by `eraseEmbeds_eraseEmpty` composed with the
transport of the deletion along the sequence (`exists_isTopErasure_totalTransformSeq`). -/
theorem IsPullbackOfUpToUnits.induced_eraseEmpty {T T' : MarkedTriple k} {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hp : T'.IsPullbackOfUpToUnits T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hP' : (S.pullback h).eraseEmpty.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E) :
    (T'.induced (S.pullback h).eraseEmpty hP' (Fin.last _)).IsPullbackOfUpToUnits
      (T.induced S hS (Fin.last _)) ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) := by
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  have hpf : (fullPullback T' T h).IsPullbackOf T h := fullPullback_isPullbackOf hp
  have : @Smooth (fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  obtain ⟨e, he⟩ := hp.2.2.2
  have hPf : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m (T.E.comap h) :=
    hpf.isOrderGeSeq_pullback hS
  have hP : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E :=
    he.extendsByEmpty.isOrderGeSeq hPf
  obtain ⟨⟨-, hI₁, hE₁⟩, -⟩ :=
    isPullbackOf_induced_last (T' := fullPullback T' T h) h hpf hS hPf
  have hI₁' : (S.pullback h).markedTransformSeq T'.I T'.m (Fin.last _) =
      (S.markedTransformSeq T.I T.m (Fin.last _)).comap (S.pullbackLastHom h) := hI₁
  have hE₁' : (S.pullback h).totalTransformSeq (T.E.comap h) (Fin.last _) =
      (S.totalTransformSeq T.E (Fin.last _)).comap (S.pullbackLastHom h) := hE₁
  refine ⟨?_, ?_, hp.2.2.1, ?_⟩
  · have h1 := pullbackLastHom_comp_composite S h
    have h2 := eraseEmptyLastHom_comp_composite (S.pullback h)
    change ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) ≫
        (S.composite ≫ (T.X.left ↘ Spec (.of k))) =
      (S.pullback h).eraseEmpty.composite ≫ (T'.X.left ↘ Spec (.of k))
    calc ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) ≫
          (S.composite ≫ (T.X.left ↘ Spec (.of k)))
        = (S.pullback h).eraseEmptyLastHom ≫
            ((S.pullbackLastHom h ≫ S.composite) ≫ (T.X.left ↘ Spec (.of k))) := by
          simp only [Category.assoc]
      _ = (S.pullback h).eraseEmptyLastHom ≫
            (((S.pullback h).composite ≫ h) ≫ (T.X.left ↘ Spec (.of k))) := by rw [h1]
      _ = ((S.pullback h).eraseEmptyLastHom ≫ (S.pullback h).composite) ≫
            (h ≫ (T.X.left ↘ Spec (.of k))) := by simp only [Category.assoc]
      _ = (S.pullback h).eraseEmpty.composite ≫ (T'.X.left ↘ Spec (.of k)) := by rw [h2, hp.1]
  · exact (markedTransformSeq_eraseEmpty_last (S.pullback h) (T'.X.left ↘ Spec (.of k)) n' T'.I T'.m
      T'.E hP).trans ((congrArg (fun J : (S.pullback h).last.IdealSheafData =>
        J.comap (S.pullback h).eraseEmptyLastHom) hI₁').trans
        (Scheme.IdealSheafData.comap_comp _ _ _).symm)
  · have hB : (S.totalTransformSeq T.E (Fin.last _)).comap
        ((S.pullback h).eraseEmptyLastHom ≫ S.pullbackLastHom h) =
        ((S.pullback h).totalTransformSeq (T.E.comap h) (Fin.last _)).comap
          (S.pullback h).eraseEmptyLastHom :=
      (DivisorFamily.comap_comp _ _ _).trans
        (congrArg (fun F : DivisorFamily (S.pullback h).last =>
          F.comap (S.pullback h).eraseEmptyLastHom) hE₁'.symm)
    obtain ⟨e₁, hc, ht, -⟩ := eraseEmbeds_eraseEmpty (S.pullback h) T'.E
    obtain ⟨e₂, he₂, -⟩ :=
      exists_isTopErasure_totalTransformSeq (S.pullback h) T'.E (T.E.comap h) e he
    have hof : ∀ {F : DivisorFamily (S.pullback h).eraseEmpty.last},
        F = ((S.pullback h).totalTransformSeq (T.E.comap h) (Fin.last _)).comap
          (S.pullback h).eraseEmptyLastHom →
        ∃ e' : ((S.pullback h).eraseEmpty.totalTransformSeq T'.E (Fin.last _)).ι ↪o F.ι,
          IsTopErasure ((S.pullback h).eraseEmpty.totalTransformSeq T'.E (Fin.last _)) F e' := by
      rintro _ rfl
      exact ⟨e₁.trans e₂, IsTopErasure.trans ⟨hc, ht⟩ (he₂.comap (S.pullback h).eraseEmptyLastHom)⟩
    exact hof hB

/-- Transport of the relation up to unit members of the last induced marked triple along an
equality of sequences: the `eqToHom` of the last-stage identification is absorbed. -/
theorem isPullbackOfUpToUnits_induced_of_eq_seq {T' : MarkedTriple k}
    {S S' : BlowUpSequence T'.X.left} (e : S = S')
    {hS : S.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E}
    {hS' : S'.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E} {R : MarkedTriple k}
    {q : S'.last ⟶ R.X.left} (hq : (T'.induced S' hS' (Fin.last _)).IsPullbackOfUpToUnits R q) :
    (T'.induced S hS (Fin.last _)).IsPullbackOfUpToUnits R
      (eqToHom (congrArg BlowUpSequence.last e) ≫ q) := by
  subst e
  exact hq

end Hironaka.MarkedTriple
