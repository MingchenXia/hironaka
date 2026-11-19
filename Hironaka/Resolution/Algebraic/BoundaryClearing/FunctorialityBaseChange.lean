/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityPullback
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.IdealSheaf.Derivative.BaseChange
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of `BD_{n,m,j}` under change of fields

Clause (2) of [Kol07, Lemma 102], the change-of-fields part, which Kollár settles in one sentence:
"change of the base field commutes with restrictions". This module proves it for the construction
of `Restriction.lean` and `Output.lean`, for a general base-change square `T'.IsBaseChangeOf T σ p`
(`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`: a cartesian square over `Spec σ`,
`I' = p^*I`, `E' = p^{-1}E`; [Kol07, 34.2]), following the smooth case of
`FunctorialityPullback.lean` line by line with the flat `p` in place of the smooth `h`.

*Orders under a change of fields.* No pointwise comparison of orders along `p` is available for a
transcendental extension; what is needed is only the order at a GENERIC POINT of a member of `E'`,
where it equals the order at its image (`ord_comap_eq_of_mem_genericPoints_baseChange`): the
member is a smooth divisor on both sides (`smooth_component` of `Restriction.lean`,
`smooth_subschemeι_comap_comp_of_isPullback`), so its stalk ideal at a generic point is the maximal
ideal on both sides and `ord_comap_of_flat_of_stalkIdeal_eq`
(`Hironaka/Scheme/BlowUpSequence/BaseChangeOrder.lean`) applies. With this the two membership
transports for `Z_{-1}` are as in the smooth case (flatness lifts generalisations, generic points of
components map to generic points, the maximality clause of `genericPoints` identifies the image):
`Zminus1_baseChange`, `centerS_baseChange`.

*The restricted pair.* The restriction `restrictionMap` of `p` to the `j`-th members and the induced
morphism `restrictedMapBaseChange` of the blown-up hypersurfaces are the smooth module's
constructions (they use only `E' = p^{-1}E`); the restriction is flat as a base change of `p`. The
two restricted marked triples form a BASE-CHANGE pair: the cartesian square over `Spec σ` is the
vertical paste of the blow-up square (`isPullback_blowUpMap`), the restriction square
(`isPullback_restrictionMap`) and the triples' square, transported to the identified centres
(`isPullback_restrictedMapBaseChange`); the ideal and family clauses are the flat transports
`markedTransform_comap_blowUpMap_of_pow_dvd`, `totalTransform_comap_of_flat` through the `eqToHom`
of the centres
(`isBaseChangeOf_restrictedTriple`).

*The output and the functor.* `rawSeq` transports by the flat form
`pullback_pushforward_of_isPullback_of_flat` (`Hironaka/Scheme/BlowUpSequence/Pushforward.lean`) and
`B`'s own clause on the restricted pair, an EXACT equality (34.2 deletes no blow-ups):
`rawSeq_baseChange`. The functor's values differ from the outputs by `eraseEmpty`, which commutes
with the pull-back along the flat SURJECTION `p` (`IsBaseChangeOf.surjective`,
`eraseEmpty_pullback_of_flat_surjective`): `functor_commutesWithBaseChange`. The class transports
are [Kol07, Definition 83] under the derivative's compatibility with the base-change square
(`isDBalanced_comap_of_isPullback_specMap`) and `maxOrd_comap_of_isPullback_specMap`
(`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`) with the base-change stability of
the relative dimension (`domain_baseChange`).

Used by `AssemblyZero.lean`.
-/

@[expose] public section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme
  IdealSheafData Scheme.IdealSheafData

namespace Hironaka.BD

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L]
  {T : Triple k} {T' : Triple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left}

omit [CharZero L] in
/-- Along a change of fields, the order at a generic point of the `j`-th member of `T'` is the order
at its image, a generic point of the `j`-th member of `T`. -/
theorem ord_comap_eq_of_mem_genericPoints_baseChange (hbc : T'.IsBaseChangeOf T σ p) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι) {η' : T'.X.left}
    (hη' : η' ∈ (T'.E.component (pos T' hj')).support.genericPoints) :
    (T.I.comap p).ord η' = T.I.ord (p η') := by
  have hflat : Flat p := flat_of_isPullback_specMap hbc.1
  have hE := component_eq_comap_component hbc.2.2 hj hj'
  have hη'c : η' ∈ ((T.E.component (pos T hj)).comap p).support.genericPoints := by
    rw [← hE]; exact hη'
  have hη := mem_genericPoints_support_of_flat p _ hη'c
  have hsm : Smooth ((T.E.component (pos T hj)).subschemeι ≫ (T.X.left ↘ Spec (.of k))) :=
    smooth_component T _
  have hsm' : Smooth (((T.E.component (pos T hj)).comap p).subschemeι ≫
    (T'.X.left ↘ Spec (.of L))) :=
    smooth_subschemeι_comap_comp_of_isPullback hbc.1 _
  have h1 : (T.E.component (pos T hj)).stalkIdeal (p η') =
      IsLocalRing.maximalIdeal (T.X.left.presheaf.stalk (p η')) :=
    stalkIdeal_eq_maximalIdeal_of_mem_genericPoints (T.X.left ↘ Spec (.of k)) _ hη
  have h2 : ((T.E.component (pos T hj)).comap p).stalkIdeal η' =
      IsLocalRing.maximalIdeal (T'.X.left.presheaf.stalk η') :=
    stalkIdeal_eq_maximalIdeal_of_mem_genericPoints (T'.X.left ↘ Spec (.of L)) _ hη'c
  exact ord_comap_of_flat_of_stalkIdeal_eq p _ h1 h2 T.I

omit [CharZero L] in
/-- Direction 1 (base change): a point of `Z_{-1}(T')` lies over a point of `Z_{-1}(T)`. -/
theorem map_mem_support_Zminus1_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) (m : ℕ) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι) {y : T'.X.left}
    (hy : y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support) :
    p y ∈ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support := by
  have hflat : Flat p := flat_of_isPullback_specMap hbc.1
  obtain ⟨η, hη, hord, hspec⟩ :=
    (mem_support_Zminus1_iff T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) y).mp hy
  refine (mem_support_Zminus1_iff T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) (p y)).mpr
    ⟨p η, ?_, ?_, hspec.map p.continuous⟩
  · have hη' : η ∈ ((T.E.nth ⟨j, hj⟩).comap p).support.genericPoints := by
      rw [← nth_eq_comap_nth hbc.2.2 hj hj']; exact hη
    exact mem_genericPoints_support_of_flat p _ hη'
  · rw [hbc.2.1, ord_comap_eq_of_mem_genericPoints_baseChange hbc hj hj' hη] at hord
    exact hord

omit [CharZero L] in
/-- Direction 2 (base change): a point over `Z_{-1}(T)` lies in `Z_{-1}(T')`. -/
theorem mem_support_Zminus1_of_map_mem_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) (m : ℕ)
    {j : ℕ} (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι) {y : T'.X.left}
    (hy : p y ∈ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support) :
    y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support := by
  have hflat : Flat p := flat_of_isPullback_specMap hbc.1
  obtain ⟨η, hη, hord, hspec⟩ :=
    (mem_support_Zminus1_iff T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) (p y)).mp hy
  obtain ⟨y₀, hy₀, rfl⟩ := Flat.generalizingMap p hspec
  have hy₀mem : y₀ ∈ (T'.E.nth ⟨j, hj'⟩).support := by
    rw [nth_eq_comap_nth hbc.2.2 hj hj', support_comap]
    exact hη.1
  obtain ⟨η', hη', hη'y₀⟩ := Closeds.exists_mem_genericPoints_specializes _ hy₀mem
  refine (mem_support_Zminus1_iff T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) y).mpr
    ⟨η', hη', ?_, hη'y₀.trans hy₀⟩
  have hη'E : η' ∈ ((T.E.nth ⟨j, hj⟩).comap p).support.genericPoints := by
    rw [← nth_eq_comap_nth hbc.2.2 hj hj']; exact hη'
  have h1 := mem_genericPoints_support_of_flat p _ hη'E
  have h2 : p η' = p y₀ := hη.2 h1.1 (hη'y₀.map p.continuous)
  rw [hbc.2.1, ord_comap_eq_of_mem_genericPoints_baseChange hbc hj hj' hη', h2]
  exact hord

omit [CharZero L] in
/-- `Z_{-1}` is compatible with a change of fields. -/
theorem Zminus1_baseChange (hbc : T'.IsBaseChangeOf T σ p) (m j : ℕ)
    (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι) :
    Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩) = (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).comap p := by
  refine ext_stalkIdeal fun y => ?_
  rw [stalkIdeal_comap]
  by_cases hy : y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support
  · have hy' := map_mem_support_Zminus1_of_isBaseChangeOf hbc m hj hj' hy
    have e1 : (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).stalkIdeal y =
        (T'.E.nth ⟨j, hj'⟩).stalkIdeal y :=
      stalkIdeal_Zminus1_eq T' m _ hy
    have e2 : (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).stalkIdeal (p y) =
        (T.E.nth ⟨j, hj⟩).stalkIdeal (p y) :=
      stalkIdeal_Zminus1_eq T m _ hy'
    rw [e1, e2, ← stalkIdeal_comap, ← nth_eq_comap_nth hbc.2.2 hj hj']
  · have hy' : p y ∉ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support := fun hc =>
      hy (mem_support_Zminus1_of_map_mem_of_isBaseChangeOf hbc m hj hj' hc)
    rw [stalkIdeal_eq_top_of_notMem_support _ hy, stalkIdeal_eq_top_of_notMem_support _ hy',
      Ideal.map_top]

omit [CharZero L] in
/-- `Z_{-1}|_S` is compatible with a change of fields along any `g` over `p`. -/
theorem centerS_baseChange (hbc : T'.IsBaseChangeOf T σ p) (m j : ℕ)
    (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι)
    {g : (T'.E.nth ⟨j, hj'⟩).subscheme ⟶ (T.E.nth ⟨j, hj⟩).subscheme}
    (hg : g ≫ (T.E.nth ⟨j, hj⟩).subschemeι = (T'.E.nth ⟨j, hj'⟩).subschemeι ≫ p) :
    centerS T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) =
      (centerS T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩)).comap g := by
  change (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).comap (T'.E.nth ⟨j, hj'⟩).subschemeι =
    ((Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).comap (T.E.nth ⟨j, hj⟩).subschemeι).comap g
  rw [← comap_comp, hg, comap_comp, Zminus1_baseChange hbc m j hj hj']

section Pair

variable (hbc : T'.IsBaseChangeOf T σ p) (m j : ℕ) (hj : j < Fintype.card T.E.ι)
  (hj' : j < Fintype.card T'.E.ι)

omit [CharZero L] in
/-- `Z_{-1}|_S` is compatible with the induced restriction of `p`. -/
theorem centerS_comap_restrictionMap_baseChange :
    centerS T' m (pos T' hj') = (centerS T m (pos T hj)).comap (restrictionMap hbc.2.2 hj hj') := by
  change (Zminus1 T'.I m (T'.E.component (pos T' hj'))).comap
      (T'.E.component (pos T' hj')).subschemeι =
    ((Zminus1 T.I m (T.E.component (pos T hj))).comap (T.E.component (pos T hj)).subschemeι).comap
      (restrictionMap hbc.2.2 hj hj')
  have e : Zminus1 T'.I m (T'.E.component (pos T' hj')) =
      (Zminus1 T.I m (T.E.component (pos T hj))).comap p :=
    Zminus1_baseChange hbc m j hj hj'
  rw [← comap_comp, restrictionMap_comp_subschemeι, comap_comp, e]

/-- The induced morphism of the blown-up hypersurfaces along a change of fields. -/
noncomputable def restrictedMapBaseChange :
    (centerS T' m (pos T' hj')).blowUp ⟶
      (centerS T m (pos T hj)).blowUp :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp
      (centerS_comap_restrictionMap_baseChange hbc m j hj hj')) ≫
    Scheme.Hom.blowUpMap (restrictionMap hbc.2.2 hj hj') (centerS T m (pos T hj))

omit [CharZero L] in
/-- The induced morphism lies over the restriction of `p` (`blowUpMap_π`). -/
theorem restrictedMapBaseChange_comp_π :
    restrictedMapBaseChange hbc m j hj hj' ≫ (centerS T m (pos T hj)).blowUpπ =
      (centerS T' m (pos T' hj')).blowUpπ ≫ restrictionMap hbc.2.2 hj hj' := by
  unfold restrictedMapBaseChange
  rw [Category.assoc, blowUpMap_π, ← Category.assoc,
    eqToHom_comp_blowUpπ (centerS_comap_restrictionMap_baseChange hbc m j hj hj')]

omit [CharZero k] [CharZero L] in
/-- The restriction of `p` is flat (a base change of the flat `p`). -/
theorem flat_restrictionMap_baseChange : Flat (restrictionMap hbc.2.2 hj hj') := by
  have : Flat p := flat_of_isPullback_specMap hbc.1
  exact property_of_isPullback @Flat (isPullback_restrictionMap hbc.2.2 hj hj').flip
    inferInstance

variable (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)
  (hI' : T'.I.IsDBalanced (T'.X.left ↘ Spec (.of L)) m) (hmax' : T'.I.maxOrd = m)

omit [CharZero L] in
/-- The base-change square of the blown-up hypersurfaces over `Spec σ`, by pasting the blow-up
square, the restriction square and the base-change square of the triples. -/
theorem isPullback_restrictedMapBaseChange :
    IsPullback (restrictedMapBaseChange hbc m j hj hj')
      ((centerS T' m (pos T' hj')).blowUpπ ≫ (T'.E.component (pos T' hj')).subschemeι ≫
        (T'.X.left ↘ Spec (.of L)))
      ((centerS T m (pos T hj)).blowUpπ ≫ (T.E.component (pos T hj)).subschemeι ≫
        (T.X.left ↘ Spec (.of k)))
      (Spec.map (CommRingCat.ofHom σ)) := by
  have hflat := flat_restrictionMap_baseChange hbc j hj hj'
  have sq1 : IsPullback (Scheme.Hom.blowUpMap (restrictionMap hbc.2.2 hj hj')
      (centerS T m (pos T hj))) ((centerS T m (pos T hj)).comap (restrictionMap hbc.2.2 hj
      hj')).blowUpπ (centerS T m (pos T hj)).blowUpπ
      (restrictionMap hbc.2.2 hj hj') := isPullback_blowUpMap _ _
  have sq2 := (isPullback_restrictionMap hbc.2.2 hj hj').flip
  have sq3 := hbc.1
  have sq := (sq1.paste_vert sq2).paste_vert sq3
  -- transport the top-left corner along the identification of the centres
  have e := congrArg Scheme.IdealSheafData.blowUp
    (centerS_comap_restrictionMap_baseChange hbc m j hj hj')
  refine isPullback_of_heq e.symm rfl rfl rfl ?_ ?_
    (heq_of_eq (Category.assoc _ _ _)) HEq.rfl sq
  · exact (eqToHom_comp_heq _ e).symm
  · refine (eqToHom_comp_heq _ e).symm.trans (heq_of_eq ?_)
    simp only [← Category.assoc]
    rw [eqToHom_comp_blowUpπ
      (centerS_comap_restrictionMap_baseChange hbc m j hj hj')]

/-- The restricted marked triples form a base-change pair along the induced morphism. -/
theorem isBaseChangeOf_restrictedTriple :
    (restrictedTriple T' m (pos T' hj') hI' hmax').IsBaseChangeOf
      (restrictedTriple T m (pos T hj) hI hmax) σ (restrictedMapBaseChange hbc m j hj hj') := by
  have hflat := flat_restrictionMap_baseChange hbc j hj hj'
  have hE' : T'.E.erase (pos T' hj') = (T.E.erase (pos T hj)).comap p :=
    erase_congr hbc.2.2 hj hj'
  refine ⟨⟨isPullback_restrictedMapBaseChange hbc m j hj hj', ?_, ?_⟩, rfl⟩
  · change (T'.I.comap (T'.E.component (pos T' hj')).subschemeι).markedTransform (centerS T' m
      (pos T' hj')) m =
      ((T.I.comap (T.E.component (pos T hj)).subschemeι).markedTransform
          (centerS T m (pos T hj)) m).comap
        (restrictedMapBaseChange hbc m j hj hj')
    unfold restrictedMapBaseChange
    rw [comap_comp, ← markedTransform_comap_blowUpMap_of_pow_dvd _ _ _ _
      (exceptionalDivisor_pow_dvd_comap_centerS m T (pos T hj)),
      markedTransform_comap_eqToHom (centerS_comap_restrictionMap_baseChange hbc m j hj hj'),
      ← comap_comp, restrictionMap_comp_subschemeι, comap_comp, ← hbc.2.1]
  · change ((T'.E.erase (pos T' hj')).comap (T'.E.component (pos T' hj')).subschemeι).totalTransform
        (centerS T' m (pos T' hj')) =
      (((T.E.erase (pos T hj)).comap (T.E.component (pos T hj)).subschemeι).totalTransform
        (centerS T m (pos T hj))).comap (restrictedMapBaseChange hbc m j hj hj')
    unfold restrictedMapBaseChange
    rw [DivisorFamily.comap_comp, ← totalTransform_comap_of_flat,
      totalTransform_comap_eqToHom (centerS_comap_restrictionMap_baseChange hbc m j hj hj'),
      ← DivisorFamily.comap_comp, restrictionMap_comp_subschemeι, DivisorFamily.comap_comp, hE']

include hbc in
/-- The restricted marked triples form a base-change pair along the morphism of the blown-up
hypersurfaces induced by `p` (existential form of `isBaseChangeOf_restrictedTriple`). -/
theorem exists_isBaseChangeOf_restrictedTriple :
    ∃ g : (restrictedTriple T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) hI' hmax').X.left ⟶
        (restrictedTriple T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) hI hmax).X.left,
      g ≫ ((centerS T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩)).blowUpπ ≫
          (T.E.nth ⟨j, hj⟩).subschemeι) =
        ((centerS T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩)).blowUpπ ≫
          (T'.E.nth ⟨j, hj'⟩).subschemeι) ≫ p ∧
      (restrictedTriple T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) hI' hmax').IsBaseChangeOf
        (restrictedTriple T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) hI hmax) σ g := by
  have hc : restrictedMapBaseChange hbc m j hj hj' ≫ ((centerS T m (pos T hj)).blowUpπ ≫
        (T.E.component (pos T hj)).subschemeι) =
      ((centerS T' m (pos T' hj')).blowUpπ ≫ (T'.E.component
          (pos T' hj')).subschemeι) ≫ p := by
    rw [← Category.assoc, restrictedMapBaseChange_comp_π, Category.assoc,
      restrictionMap_comp_subschemeι, Category.assoc]
  exact ⟨restrictedMapBaseChange hbc m j hj hj', hc,
    isBaseChangeOf_restrictedTriple hbc m j hj hj' hI hmax hI' hmax'⟩

variable {n : ℕ} (hn : T.HasDimLE n) (hn' : T'.HasDimLE n) {Dom : MarkedTriple k → Prop}
  (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
  {Dom' : MarkedTriple L → Prop} (B' : OrderGeSeqAssignment L Dom')
  (hDom' : ∀ T' : MarkedTriple L, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom' T')

include hbc in
/-- The output sequence of the base change is the pull-back of the output sequence. -/
theorem rawSeq_baseChange (hB : B.CommutesWithBaseChange B' σ) :
    rawSeq T' m (pos T' hj') hI' hmax' hn' B' hDom' =
      (rawSeq T m (pos T hj) hI hmax hn B hDom).pullback p := by
  have hflat : Flat p := flat_of_isPullback_specMap hbc.1
  have hg := hB (restrictedTriple T m (pos T hj) hI hmax)
    (restrictedTriple T' m (pos T' hj') hI' hmax') (restrictedMapBaseChange hbc m j hj hj')
    (isBaseChangeOf_restrictedTriple hbc m j hj hj' hI hmax hI' hmax')
    (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)
    (hDom' _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl)
  have e1 := pullback_pushforward_of_isPullback_of_flat
    (BlowUpSequence.cons _ (centerS T m (pos T hj))
      (B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)))
    (T.E.component (pos T hj)).subschemeι p (T'.E.component (pos T' hj')).subschemeι
    (restrictionMap hbc.2.2 hj hj') (isPullback_restrictionMap hbc.2.2 hj hj')
  have hg' : B'.seq (restrictedTriple T' m (pos T' hj') hI' hmax')
        (hDom' _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl) =
      ((B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)).pullback
        (Scheme.Hom.blowUpMap (restrictionMap hbc.2.2 hj hj') (centerS T m (pos T hj)))).pullback
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp
            (centerS_comap_restrictionMap_baseChange hbc m j hj
            hj'))) :=
    hg.trans (pullback_comp _ _ _)
  have e2 : (BlowUpSequence.cons _ (centerS T m (pos T hj))
        (B.seq (restrictedTriple T m (pos T hj) hI hmax)
          (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl))).pullback
        (restrictionMap hbc.2.2 hj hj') =
      BlowUpSequence.cons _ (centerS T' m (pos T' hj'))
        (B'.seq (restrictedTriple T' m (pos T' hj') hI' hmax')
          (hDom' _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl)) :=
    (pullback_cons _ _ _).trans
      (cons_congr (centerS_comap_restrictionMap_baseChange hbc m j hj hj').symm
        ((Hironaka.Sequence.pullback_eqToHom_heq _ _).symm.trans (heq_of_eq hg'.symm)))
  exact (e1.trans (congrArg (fun Q => BlowUpSequence.pushforward Q
    (T'.E.component (pos T' hj')).subschemeι) e2)).symm

end Pair

section ClassTransportBaseChange

omit [CharZero L] in
/-- D-balancedness ([Kol07, Definition 83]) is preserved by a change of fields. -/
theorem isDBalanced_comap_of_isPullback_specMap {X Y : Scheme.{u}} {p : Y ⟶ X}
    {g' : Y ⟶ Spec (.of L)} {f : X ⟶ Spec (.of k)} {σ : k →+* L}
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) [Smooth f] {I : X.IdealSheafData}
    {m : ℕ} (hI : IsDBalanced f I m) : IsDBalanced g' (I.comap p) m := by
  intro i hi
  rw [derivativeIter_comap_of_isPullback_specMap sq, ← comap_pow, ← comap_pow]
  exact comap_mono p (hI i hi)

omit [CharZero L] in
/-- The base change of a triple of the standing class of [Kol07, Lemma 102] stays in the class. -/
theorem domain_baseChange (n m j : ℕ) (σ : k →+* L) {T : Triple k} {T' : Triple L}
    {p : T'.X.left ⟶ T.X.left} (hbc : T'.IsBaseChangeOf T σ p)
    (hT : Domain n m j T) : Domain n m j T' := by
  obtain ⟨sq, hI, hE⟩ := hbc
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n', hn'n, hn'⟩ := hT.1
    have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
    exact ⟨n', hn'n, smoothOfRelativeDimension_of_isPullback_specMap sq n'⟩
  · rw [hI]
    exact isDBalanced_comap_of_isPullback_specMap sq hT.2.1
  · obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    obtain ⟨d', hd'⟩ := T'.smoothOfRelativeDimension
    rw [hI, Hironaka.BO.maxOrd_comap_of_isPullback_specMap sq d d' T.I]
    exact hT.2.2.1
  · have : Fintype.card T'.E.ι = Fintype.card T.E.ι := by rw [hE]; rfl
    rw [this]
    exact hT.2.2.2

end ClassTransportBaseChange

section FunctorLevelBaseChange

variable (n m j : ℕ) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
  {Dom' : MarkedTriple L → Prop} (B' : OrderGeSeqAssignment L Dom')
  (hDom' : ∀ T' : MarkedTriple L, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom' T') (σ : k →+* L)

/-- `BD_{n,m,j}` commutes with change of fields when `B`, `B'` do ([Kol07, 34.2]; clause (2) of
[Kol07, Lemma 102]). -/
theorem functor_commutesWithBaseChange (hB : B.CommutesWithBaseChange B' σ) :
    (functor n m j B hDom).CommutesWithBaseChange (functor n m j B' hDom') σ := by
  intro T T' p hbc hT hT'
  have hflat : Flat p := flat_of_isPullback_specMap hbc.1
  rw [functor_seq, functor_seq,
    rawSeq_baseChange hbc m j hT.2.2.2 hT'.2.2.2 hT.2.1 hT.2.2.1 hT'.2.1 hT'.2.2.1 hT.1 hT'.1 B
      hDom B' hDom' hB]
  exact eraseEmpty_pullback_of_flat_surjective _ _ hbc.surjective

end FunctorLevelBaseChange

end Hironaka.BD
