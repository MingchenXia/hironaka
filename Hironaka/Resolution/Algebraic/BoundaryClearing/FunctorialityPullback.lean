/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Output
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.ExceptionalBundle
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of `BD_{n,m,j}` under smooth morphisms

Clause (2) of [Kol07, Lemma 102], the smooth part: for a smooth surjection `h : Y → X`, Kollár
notes that pulling back by `h` and then restricting to `E^j_Y = h^{-1}(E^j)` gives the same triple
as restricting to `E^j` and then pulling back by `h|_{E^j_Y}`, so the functoriality of
`BMO_{n−1,m}` gives `h^* BD_{n,m,j}(X, I, E) = BD_{n,m,j}(Y, h^*I, h^{-1}E)`; for an arbitrary
smooth `h` "the same blow-ups end up with empty centers" ([Kol07, 34.1], the second bullet). This
module proves both for the construction of `Restriction.lean` and `Output.lean` (`rawSeq`,
`functor`), for a general pull-back pair `T'.IsPullbackOf T h`
(`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`) and the `j`-th members by POSITION
(`pos T hj = monoEquivOfFin T.E.ι rfl ⟨j, hj⟩`, so that `T.E.nth ⟨j, hj⟩ = T.E.component (pos T hj)`
definitionally).

*The centre.* `Z_{-1}` pulls back along ANY smooth `h` (`Zminus1_pullback`), stalkwise
(`ext_stalkIdeal`): at a point of `Z_{-1}(T')` both stalks are the stalk of the divisor
(`stalkIdeal_Zminus1_eq` of `Center.lean`, whose components are disjoint), elsewhere both are the
unit ideal. The two membership transports: a generic point of a component of `h^{-1}(E^j)` lies
over a generic point of `E^j` (`mem_genericPoints_support_of_flat`,
`Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`) with the same order (`ord_comap_of_smooth`,
`Hironaka/Scheme/IdealSheaf/Order/Smooth.lean`); conversely a point over `Z_{-1}(T)` lifts its
generalisation along the flat `h` (`Flat.generalizingMap`), lies on a component of `h^{-1}(E^j)`
whose generic point maps to a generic point of `E^j` specialising to the selected one, hence equal
to it by the maximality clause of `genericPoints`. Then `Z_{-1}|_S` pulls back along any `g : E'^j ⟶
E^j` over `h` (`centerS_pullback`).

*The restricted pair.* The induced restriction `restrictionMap : E'^j ⟶ E^j` is Mathlib's
`subschemeMap` after the identification `E'^j = h^{-1}(E^j)` (`component_eq_comap_component`); it
lies over `h`, is smooth (a base change of `h`, `AlgebraicGeometry.isPullback_subschemeι_comap`) and
surjective when
`h` is. The induced morphism of the blown-up hypersurfaces `restrictedMap` is `blowUpMap` along it,
after the identification of the centres (`centerS_comap_restrictionMap`); it lies over `h`
(`restrictedMap_comp_π`, `blowUpMap_π`, `AlgebraicGeometry.eqToHom_comp_blowUpπ`), is smooth and
surjective when `h` is,
and the two restricted marked triples form a pull-back pair along it
(`isPullbackOf_restrictedTriple`): the ideals by `markedTransform_comap_blowUpMap_of_pow_dvd` (the
divisibility
hypothesis is trivial, the exceptional divisor of `Z_{-1}|_S` being the unit ideal,
`exceptionalDivisor_centerS_eq_top` of `Composite.lean`), the families by
`totalTransform_comap_of_flat` and the congruence of `erase`, both transported through the
`eqToHom` of the centres (`markedTransform_comap_eqToHom`, `totalTransform_comap_eqToHom`).

*The output.* `rawSeq` is the push-forward of `cons (Z_{-1}|_S) (B(…))` along `E^j ↪ X`;
`pullback_pushforward_of_isPullback` (`Hironaka/Scheme/BlowUpSequence/Pushforward.lean`, with the
cartesian square of the restriction, `isPullback_restrictionMap`) turns `h^*(rawSeq T)` into the
push-forward of the pulled-back cons, whose centre is `Z_{-1}(T')|_{S'}` and whose tail is `B`'s
value on the pulled-back restricted triple by `B`'s own clause
(`cons_pullback_restrictionMap_of_eq`, `cons_congr` with the `eqToHom` transport
`pullback_eqToHom_heq`): `rawSeq_pullback_of_surjective`. For an arbitrary smooth `h` the tail
agrees only after deleting empty blow-ups (the second bullet of [Kol07, 34.1]); `eraseEmpty` passes
the push-forward and the cons (`eraseEmpty_pushforward`, `eraseEmpty_cons_eraseEmpty`,
`Hironaka/Scheme/BlowUpSequence/EraseEmptyTransport.lean`): `eraseEmpty_rawSeq_pullback`.

*The functor.* `functor = rawSeq` with its empty blow-ups deleted; by `commutesWithSmooth_iff`
(`Hironaka/Scheme/BlowUpSequence/Functoriality.lean`) only the second bullet is to be shown, and it
is `eraseEmpty_rawSeq_pullback` after `eraseEmpty_pullback_eraseEmpty'`; the first bullet alone is
`rawSeq_pullback_of_surjective` with `eraseEmpty_pullback_of_flat_surjective`
(`functor_commutesWithSmooth`, `functor_commutesWithSmoothSurjections`). The class transports
(`isDBalanced_comap_of_smooth`, `domain_pullback_of_surjective`) are [Kol07, Definition 83] under
the derivative's compatibility with smooth pull-back and the `maxOrd` lemmas of
`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`.

Used by `FunctorialityBaseChange.lean`, `Assembly.lean` and `AssemblyZero.lean`, and outside this
directory by `Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/Monomial.lean` and
`Hironaka/Resolution/Algebraic/OrderReduction/Step21Functorial.lean`.
-/

@[expose] public section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  IdealSheafData Scheme.IdealSheafData

namespace Hironaka.BD

variable {k : Type u} [Field k]

/-- `nth` along an equality of families. -/
theorem nth_congr {Y : Scheme.{u}} {E E' : DivisorFamily Y} (hE : E' = E) {j : ℕ}
    (hj : j < Fintype.card E.ι) (hj' : j < Fintype.card E'.ι) :
    E'.nth ⟨j, hj'⟩ = E.nth ⟨j, hj⟩ := by
  subst hE
  rfl

/-- The `j`-th member of the pulled-back family is the inverse image of the `j`-th member (Kollár's
`E^j_Y := h^{-1}(E^j)`, the proof of [Kol07, Lemma 102]). -/
theorem nth_eq_comap_nth {L : Type u} [Field L] {T : Triple k} {T' : Triple L}
    {h : T'.X.left ⟶ T.X.left} (hE : T'.E = T.E.comap h) {j : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) :
    T'.E.nth ⟨j, hj'⟩ = (T.E.nth ⟨j, hj⟩).comap h :=
  nth_congr hE (E := T.E.comap h) hj hj'

/-! ### Positions and the induced restriction -/

/-- The component at position `j`, as an index (reducible:
`T.E.nth ⟨j, hj⟩ = T.E.component (pos T hj)` definitionally). -/
abbrev pos (T : Triple k) {j : ℕ} (hj : j < Fintype.card T.E.ι) : T.E.ι :=
  monoEquivOfFin T.E.ι rfl ⟨j, hj⟩

/-- The same, in the component form of the positions. -/
theorem component_eq_comap_component {L : Type u} [Field L] {T : Triple k} {T' : Triple L}
    {h : T'.X.left ⟶ T.X.left} (hE : T'.E = T.E.comap h) {j : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) :
    T'.E.component (pos T' hj') = (T.E.component (pos T hj)).comap h :=
  nth_eq_comap_nth hE hj hj'

section Helpers

variable {X : Scheme.{u}}

/-- Surjective morphisms of schemes compose. -/
theorem surjective_comp {Z W V : Scheme.{u}} (f : Z ⟶ W) (g : W ⟶ V) (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Function.Surjective (f ≫ g) := by
  intro v
  obtain ⟨w, rfl⟩ := hg v
  obtain ⟨z, rfl⟩ := hf w
  exact ⟨z, Scheme.Hom.comp_apply f g z⟩

/-- Transport of a marked transform along an equality of centres. -/
theorem markedTransform_comap_eqToHom {D D' : X.IdealSheafData} (e : D' = D) (J : X.IdealSheafData)
    (m : ℕ) :
    (J.markedTransform D m).comap (eqToHom
        (congrArg Scheme.IdealSheafData.blowUp e)) = J.markedTransform D' m := by
  subst e
  simp

/-- Transport of a total transform along an equality of centres. -/
theorem totalTransform_comap_eqToHom {D D' : X.IdealSheafData} (e : D' = D) (F : DivisorFamily X) :
    (F.totalTransform D).comap (eqToHom
        (congrArg Scheme.IdealSheafData.blowUp e)) = F.totalTransform D' :=
        by
  subst e
  simp

/-- `erase` at a position, along an equality of families. -/
theorem erase_congr {E E' : DivisorFamily X} (hE : E' = E) {j : ℕ} (hj : j < Fintype.card E.ι)
    (hj' : j < Fintype.card E'.ι) :
    E'.erase (monoEquivOfFin E'.ι rfl ⟨j, hj'⟩) = E.erase (monoEquivOfFin E.ι rfl ⟨j, hj⟩) := by
  subst hE
  rfl

end Helpers

section Restriction

variable {L : Type u} [Field L] {T : Triple k} {T' : Triple L} {h : T'.X.left ⟶ T.X.left}
  (hE : T'.E = T.E.comap h) {j : ℕ} (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι)

/-- The restriction of `h` to the `j`-th members: `E'^j ⟶ E^j` over `h`. -/
noncomputable def restrictionMap :
    (T'.E.component (pos T' hj')).subscheme ⟶ (T.E.component (pos T hj)).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme (component_eq_comap_component hE hj hj')) ≫
    subschemeMap ((T.E.component (pos T hj)).comap h) (T.E.component (pos T hj)) h
      (le_map_comap _ h)

/-- The restriction lies over `h` (Mathlib's `subschemeMap_subschemeι`). -/
theorem restrictionMap_comp_subschemeι :
    restrictionMap hE hj hj' ≫ (T.E.component (pos T hj)).subschemeι =
      (T'.E.component (pos T' hj')).subschemeι ≫ h := by
  unfold restrictionMap
  rw [Category.assoc, subschemeMap_subschemeι, ← Category.assoc,
    eqToHom_subschemeι (component_eq_comap_component hE hj hj')]

/-- The restriction is smooth: the base change of `h` along `E^j ↪ X`. -/
theorem smooth_restrictionMap [Smooth h] : Smooth (restrictionMap hE hj hj') := by
  unfold restrictionMap
  have : Smooth (subschemeMap ((T.E.component (pos T hj)).comap h) (T.E.component (pos T hj)) h
      (le_map_comap _ h)) :=
    property_of_isPullback @Smooth
      (isPullback_subschemeι_comap (T.E.component (pos T hj)) h).flip
      inferInstance
  infer_instance

/-- The restriction is surjective when `h` is (base change). -/
theorem surjective_restrictionMap (hs : Function.Surjective h) :
    Function.Surjective (restrictionMap hE hj hj') := by
  have : Surjective h := ⟨hs⟩
  have : Surjective (subschemeMap ((T.E.component (pos T hj)).comap h) (T.E.component (pos T hj))
      h (le_map_comap _ h)) :=
    property_of_isPullback @Surjective
      (isPullback_subschemeι_comap (T.E.component (pos T hj)) h).flip
      inferInstance
  exact surjective_comp _ _ (surjective_of_isIso _) (Scheme.Hom.surjective _)

/-- The square of the induced restriction over `h` is cartesian (transport of the canonical one). -/
theorem isPullback_restrictionMap :
    IsPullback (T'.E.component (pos T' hj')).subschemeι (restrictionMap hE hj hj') h
      (T.E.component (pos T hj)).subschemeι := by
  have e := congrArg Scheme.IdealSheafData.subscheme (component_eq_comap_component hE hj hj')
  refine isPullback_of_heq e.symm rfl rfl rfl ?_ ?_ HEq.rfl HEq.rfl
    (isPullback_subschemeι_comap (T.E.component (pos T hj)) h)
  · exact (eqToHom_comp_heq _ e).symm.trans
      (heq_of_eq (eqToHom_subschemeι (component_eq_comap_component hE hj hj')))
  · exact (eqToHom_comp_heq _ e).symm

end Restriction

variable [CharZero k]

omit [CharZero k] in
/-- Direction 1: a point of `Z_{-1}(T')` lies over a point of `Z_{-1}(T)`. -/
theorem map_mem_support_Zminus1_of_isPullbackOf {T T' : Triple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h]
    (hpb : T'.IsPullbackOf T h) (m : ℕ) {j : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) {y : T'.X.left}
    (hy : y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support) :
    h y ∈ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support := by
  obtain ⟨_, hI, hE⟩ := hpb
  have key := (mem_support_Zminus1_iff T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) y).mp hy
  obtain ⟨η, hη, hord, hspec⟩ := key
  refine (mem_support_Zminus1_iff T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) (h y)).mpr
    ⟨h η, ?_, ?_, hspec.map h.continuous⟩
  · have hη' : η ∈ ((T.E.nth ⟨j, hj⟩).comap h).support.genericPoints := by
      rw [← nth_eq_comap_nth hE hj hj']; exact hη
    exact mem_genericPoints_support_of_flat h _ hη'
  · rw [hI, ord_comap_of_smooth] at hord; exact hord

omit [CharZero k] in
/-- Direction 2: a point over `Z_{-1}(T)` lies in `Z_{-1}(T')`. -/
theorem mem_support_Zminus1_of_map_mem_of_isPullbackOf {T T' : Triple k} {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hpb : T'.IsPullbackOf T h) (m : ℕ) {j : ℕ}
    (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) {y : T'.X.left}
    (hy : h y ∈ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support) :
    y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support := by
  obtain ⟨_, hI, hE⟩ := hpb
  obtain ⟨η, hη, hord, hspec⟩ :=
    (mem_support_Zminus1_iff T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) (h y)).mp hy
  obtain ⟨y₀, hy₀, rfl⟩ := Flat.generalizingMap h hspec
  have hy₀mem : y₀ ∈ (T'.E.nth ⟨j, hj'⟩).support := by
    rw [nth_eq_comap_nth hE hj hj', support_comap]
    exact hη.1
  obtain ⟨η', hη', hη'y₀⟩ := Closeds.exists_mem_genericPoints_specializes _ hy₀mem
  refine (mem_support_Zminus1_iff T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) y).mpr
    ⟨η', hη', ?_, hη'y₀.trans hy₀⟩
  have hη'E : η' ∈ ((T.E.nth ⟨j, hj⟩).comap h).support.genericPoints := by
    rw [← nth_eq_comap_nth hE hj hj']; exact hη'
  have h1 := mem_genericPoints_support_of_flat h _ hη'E
  have h2 : h η' = h y₀ := hη.2 h1.1 (hη'y₀.map h.continuous)
  rw [hI, ord_comap_of_smooth, h2]
  exact hord

omit [CharZero k] in
/-- `Z_{-1}` pulls back along any smooth `h`. -/
theorem Zminus1_pullback {T T' : Triple k} {h : T'.X.left ⟶ T.X.left} [Smooth h]
    (hpb : T'.IsPullbackOf T h) (m j : ℕ) (hj : j < Fintype.card T.E.ι)
    (hj' : j < Fintype.card T'.E.ι) :
    Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩) = (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).comap h := by
  refine ext_stalkIdeal fun y => ?_
  rw [stalkIdeal_comap]
  by_cases hy : y ∈ (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).support
  · have hy' := map_mem_support_Zminus1_of_isPullbackOf hpb m hj hj' hy
    have e1 : (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).stalkIdeal y =
        (T'.E.nth ⟨j, hj'⟩).stalkIdeal y :=
      stalkIdeal_Zminus1_eq T' m _ hy
    have e2 : (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).stalkIdeal (h y) =
        (T.E.nth ⟨j, hj⟩).stalkIdeal (h y) :=
      stalkIdeal_Zminus1_eq T m _ hy'
    rw [e1, e2, ← stalkIdeal_comap, ← nth_eq_comap_nth hpb.2.2 hj hj']
  · have hy' : h y ∉ (Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).support := fun hc =>
      hy (mem_support_Zminus1_of_map_mem_of_isPullbackOf hpb m hj hj' hc)
    rw [stalkIdeal_eq_top_of_notMem_support _ hy, stalkIdeal_eq_top_of_notMem_support _ hy',
      Ideal.map_top]

omit [CharZero k] in
/-- `Z_{-1}|_S` pulls back along any `g : E'^j ⟶ E^j` over `h`. -/
theorem centerS_pullback {T T' : Triple k} {h : T'.X.left ⟶ T.X.left} [Smooth h]
    (hpb : T'.IsPullbackOf T h)
    (m j : ℕ) (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι)
    {g : (T'.E.nth ⟨j, hj'⟩).subscheme ⟶ (T.E.nth ⟨j, hj⟩).subscheme}
    (hg : g ≫ (T.E.nth ⟨j, hj⟩).subschemeι = (T'.E.nth ⟨j, hj'⟩).subschemeι ≫ h) :
    centerS T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) =
      (centerS T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩)).comap g := by
  change (Zminus1 T'.I m (T'.E.nth ⟨j, hj'⟩)).comap (T'.E.nth ⟨j, hj'⟩).subschemeι =
    ((Zminus1 T.I m (T.E.nth ⟨j, hj⟩)).comap (T.E.nth ⟨j, hj⟩).subschemeι).comap g
  rw [← comap_comp, hg, comap_comp, Zminus1_pullback hpb m j hj hj']

section Pair

variable {T T' : Triple k} {h : T'.X.left ⟶ T.X.left} [Smooth h]
  (hpb : T'.IsPullbackOf T h) (m j : ℕ)
  (hj : j < Fintype.card T.E.ι) (hj' : j < Fintype.card T'.E.ι)

omit [CharZero k] in
/-- `Z_{-1}|_S` pulls back along the induced restriction. -/
theorem centerS_comap_restrictionMap :
    centerS T' m (pos T' hj') = (centerS T m (pos T hj)).comap (restrictionMap hpb.2.2 hj hj') := by
  change (Zminus1 T'.I m (T'.E.component (pos T' hj'))).comap
      (T'.E.component (pos T' hj')).subschemeι =
    ((Zminus1 T.I m (T.E.component (pos T hj))).comap (T.E.component (pos T hj)).subschemeι).comap
      (restrictionMap hpb.2.2 hj hj')
  have e : Zminus1 T'.I m (T'.E.component (pos T' hj')) =
      (Zminus1 T.I m (T.E.component (pos T hj))).comap h :=
    Zminus1_pullback hpb m j hj hj'
  rw [← comap_comp, restrictionMap_comp_subschemeι, comap_comp, e]

/-- The induced morphism of the blown-up hypersurfaces. -/
noncomputable def restrictedMap :
    (centerS T' m (pos T' hj')).blowUp ⟶
      (centerS T m (pos T hj)).blowUp :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp (centerS_comap_restrictionMap hpb m j hj hj')) ≫
    Scheme.Hom.blowUpMap (restrictionMap hpb.2.2 hj hj') (centerS T m (pos T hj))

omit [CharZero k] in
/-- The induced morphism lies over the restriction (`blowUpMap_π`). -/
theorem restrictedMap_comp_π :
    restrictedMap hpb m j hj hj' ≫ (centerS T m (pos T hj)).blowUpπ =
      (centerS T' m (pos T' hj')).blowUpπ ≫ restrictionMap hpb.2.2 hj hj' := by
  unfold restrictedMap
  rw [Category.assoc, blowUpMap_π, ← Category.assoc,
    eqToHom_comp_blowUpπ (centerS_comap_restrictionMap hpb m j hj hj')]

/-- An `eqToHom` is smooth. -/
theorem smooth_eqToHom {Z W : Scheme.{u}} (e : Z = W) : Smooth (eqToHom e) := by
  subst e
  rw [eqToHom_refl]
  infer_instance

omit [CharZero k] in
/-- The induced morphism is smooth (`blowUpMap` along a smooth morphism). -/
theorem smooth_restrictedMap : Smooth (restrictedMap hpb m j hj hj') := by
  unfold restrictedMap
  have := smooth_restrictionMap hpb.2.2 hj hj'
  have h2 : Smooth (Scheme.Hom.blowUpMap (restrictionMap hpb.2.2 hj hj')
      (centerS T m (pos T hj))) :=
    property_of_isPullback @Smooth
      (isPullback_blowUpMap _ _) inferInstance
  exact MorphismProperty.comp_mem _ _ _ (smooth_eqToHom _) h2

omit [CharZero k] in
/-- The induced morphism is surjective when `h` is. -/
theorem surjective_restrictedMap (hs : Function.Surjective h) :
    Function.Surjective (restrictedMap hpb m j hj hj') := by
  have := smooth_restrictionMap hpb.2.2 hj hj'
  have : Surjective (restrictionMap hpb.2.2 hj hj') :=
    ⟨surjective_restrictionMap hpb.2.2 hj hj' hs⟩
  have : Surjective (Scheme.Hom.blowUpMap (restrictionMap hpb.2.2 hj hj')
      (centerS T m (pos T hj))) :=
    property_of_isPullback @Surjective
      (isPullback_blowUpMap _ _) inferInstance
  exact surjective_comp _ _ (surjective_of_isIso _) (Scheme.Hom.surjective _)

variable (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)
  (hI' : T'.I.IsDBalanced (T'.X.left ↘ Spec (.of k)) m) (hmax' : T'.I.maxOrd = m)

omit [CharZero k] in
/-- The divisibility hypothesis of `markedTransform_comap_blowUpMap_of_pow_dvd` for `Z_{-1}|_S`: its
exceptional
divisor is the unit ideal (`exceptionalDivisor_centerS_eq_top`). -/
theorem exceptionalDivisor_pow_dvd_comap_centerS (T : Triple k) (i : T.E.ι) :
    (centerS T m i).exceptionalDivisor ^ m ∣
      (T.I.comap (T.E.component i).subschemeι).comap (centerS T m i).blowUpπ := by
  rw [exceptionalDivisor_centerS_eq_top, ← one_eq_top, one_pow]
  exact one_dvd _

/-- The restricted marked triples form a pull-back pair along the induced morphism. -/
theorem isPullbackOf_restrictedTriple :
    (restrictedTriple T' m (pos T' hj') hI' hmax').IsPullbackOf
      (restrictedTriple T m (pos T hj) hI hmax) (restrictedMap hpb m j hj hj') := by
  have hflat : Flat (restrictionMap hpb.2.2 hj hj') := by
    have := smooth_restrictionMap hpb.2.2 hj hj'
    infer_instance
  have hE' : T'.E.erase (pos T' hj') = (T.E.erase (pos T hj)).comap h :=
    erase_congr hpb.2.2 hj hj'
  refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
  · change restrictedMap hpb m j hj hj' ≫
        ((centerS T m (pos T hj)).blowUpπ ≫
          (T.E.component (pos T hj)).subschemeι ≫ (T.X.left ↘ Spec (.of k))) =
      (centerS T' m (pos T' hj')).blowUpπ ≫
        (T'.E.component (pos T' hj')).subschemeι ≫ (T'.X.left ↘ Spec (.of k))
    rw [← hpb.1, ← Category.assoc, restrictedMap_comp_π, Category.assoc, ← Category.assoc
      (restrictionMap _ _ _), restrictionMap_comp_subschemeι, Category.assoc]
  · change (T'.I.comap (T'.E.component (pos T' hj')).subschemeι).markedTransform (centerS T' m
      (pos T' hj')) m =
      ((T.I.comap (T.E.component (pos T hj)).subschemeι).markedTransform
          (centerS T m (pos T hj)) m).comap (restrictedMap hpb m j hj hj')
    unfold restrictedMap
    rw [comap_comp, ← markedTransform_comap_blowUpMap_of_pow_dvd _ _ _ _
      (exceptionalDivisor_pow_dvd_comap_centerS m T (pos T hj)),
      markedTransform_comap_eqToHom (centerS_comap_restrictionMap hpb m j hj hj'), ← comap_comp,
      restrictionMap_comp_subschemeι, comap_comp, ← hpb.2.1]
  · change ((T'.E.erase (pos T' hj')).comap (T'.E.component (pos T' hj')).subschemeι).totalTransform
        (centerS T' m (pos T' hj')) =
      (((T.E.erase (pos T hj)).comap (T.E.component (pos T hj)).subschemeι).totalTransform
        (centerS T m (pos T hj))).comap (restrictedMap hpb m j hj hj')
    unfold restrictedMap
    rw [DivisorFamily.comap_comp, ← totalTransform_comap_of_flat,
      totalTransform_comap_eqToHom (centerS_comap_restrictionMap hpb m j hj hj'),
      ← DivisorFamily.comap_comp, restrictionMap_comp_subschemeι, DivisorFamily.comap_comp, hE']

include hpb in
/-- The restricted marked triples form a pull-back pair along a smooth morphism over `h`,
surjective when `h` is (existential form of `isPullbackOf_restrictedTriple`). -/
theorem exists_isPullbackOf_restrictedTriple :
    ∃ g : (restrictedTriple T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) hI' hmax').X.left ⟶
        (restrictedTriple T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) hI hmax).X.left,
      g ≫ ((centerS T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩)).blowUpπ ≫
          (T.E.nth ⟨j, hj⟩).subschemeι) =
        ((centerS T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩)).blowUpπ ≫
          (T'.E.nth ⟨j, hj'⟩).subschemeι) ≫ h ∧
      Smooth g ∧ (Function.Surjective h → Function.Surjective g) ∧
        (restrictedTriple T' m (monoEquivOfFin T'.E.ι rfl ⟨j, hj'⟩) hI' hmax').IsPullbackOf
          (restrictedTriple T m (monoEquivOfFin T.E.ι rfl ⟨j, hj⟩) hI hmax) g := by
  have hc : restrictedMap hpb m j hj hj' ≫ ((centerS T m (pos T hj)).blowUpπ ≫
        (T.E.component (pos T hj)).subschemeι) =
      ((centerS T' m (pos T' hj')).blowUpπ ≫ (T'.E.component
          (pos T' hj')).subschemeι) ≫ h := by
    rw [← Category.assoc, restrictedMap_comp_π, Category.assoc, restrictionMap_comp_subschemeι,
      Category.assoc]
  exact ⟨restrictedMap hpb m j hj hj', hc, smooth_restrictedMap hpb m j hj hj',
    surjective_restrictedMap hpb m j hj hj',
    isPullbackOf_restrictedTriple hpb m j hj hj' hI hmax hI' hmax'⟩

variable {n : ℕ} (hn : T.HasDimLE n) (hn' : T'.HasDimLE n) {Dom : MarkedTriple k → Prop}
  (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')

include hpb in
/-- The output's first step and tail, pulled back along the induced restriction: the cons of the
pulled-back centre and the pulled-back tail (definitional), rewritten as the cons of
`Z_{-1}(T')|_S'` and the tail on the restricted triple of `T'` when `B` commutes with the induced
morphism. -/
theorem cons_pullback_restrictionMap_of_eq (hR : Dom (restrictedTriple T m (pos T hj) hI hmax))
    (hR' : Dom (restrictedTriple T' m (pos T' hj') hI' hmax'))
    (hg : B.seq (restrictedTriple T' m (pos T' hj') hI' hmax') hR' =
      (B.seq (restrictedTriple T m (pos T hj) hI hmax) hR).pullback
        (restrictedMap hpb m j hj hj')) :
    (BlowUpSequence.cons _ (centerS T m (pos T hj))
        (B.seq (restrictedTriple T m (pos T hj) hI hmax) hR)).pullback
        (restrictionMap hpb.2.2 hj hj') =
      BlowUpSequence.cons _ (centerS T' m (pos T' hj'))
        (B.seq (restrictedTriple T' m (pos T' hj') hI' hmax') hR') := by
  refine (pullback_cons _ _ _).trans
    (cons_congr (centerS_comap_restrictionMap hpb m j hj hj').symm ?_)
  have hg' : B.seq (restrictedTriple T' m (pos T' hj') hI' hmax') hR' =
      ((B.seq (restrictedTriple T m (pos T hj) hI hmax) hR).pullback
        (Scheme.Hom.blowUpMap (restrictionMap hpb.2.2 hj hj') (centerS T m (pos T hj)))).pullback
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp
            (centerS_comap_restrictionMap hpb m j hj hj'))) :=
    hg.trans (pullback_comp _ _ _)
  exact (Hironaka.Sequence.pullback_eqToHom_heq _ _).symm.trans (heq_of_eq hg'.symm)

include hpb in
/-- The output sequence pulls back along a smooth surjection (the first bullet of [Kol07, 34.1]). -/
theorem rawSeq_pullback_of_surjective (hs : Function.Surjective h)
    (hB : B.CommutesWithSmoothSurjections) :
    rawSeq T' m (pos T' hj') hI' hmax' hn' B hDom =
      (rawSeq T m (pos T hj) hI hmax hn B hDom).pullback h := by
  have : @Smooth (restrictedTriple T' m (pos T' hj') hI' hmax').X.left
      (restrictedTriple T m (pos T hj) hI hmax).X.left (restrictedMap hpb m j hj hj') :=
    smooth_restrictedMap hpb m j hj hj'
  have hg := hB (restrictedTriple T m (pos T hj) hI hmax)
    (restrictedTriple T' m (pos T' hj') hI' hmax') (restrictedMap hpb m j hj hj')
    (surjective_restrictedMap hpb m j hj hj' hs)
    (isPullbackOf_restrictedTriple hpb m j hj hj' hI hmax hI' hmax')
  have e1 := pullback_pushforward_of_isPullback
    (BlowUpSequence.cons _ (centerS T m (pos T hj))
      (B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)))
    (T.E.component (pos T hj)).subschemeι h (T'.E.component (pos T' hj')).subschemeι
    (restrictionMap hpb.2.2 hj hj') (isPullback_restrictionMap hpb.2.2 hj hj')
  have e2 := cons_pullback_restrictionMap_of_eq hpb m j hj hj' hI hmax hI' hmax' B
    (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)
    (hDom _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl) (hg _ _)
  exact (e1.trans (congrArg (fun Q => BlowUpSequence.pushforward Q
    (T'.E.component (pos T' hj')).subschemeι) e2)).symm

include hpb in
/-- After deleting the empty blow-ups the outputs agree for any smooth `h` (the second bullet of
[Kol07, 34.1]). -/
theorem eraseEmpty_rawSeq_pullback (hB : B.CommutesWithSmooth) :
    (rawSeq T' m (pos T' hj') hI' hmax' hn' B hDom).eraseEmpty =
      ((rawSeq T m (pos T hj) hI hmax hn B hDom).pullback h).eraseEmpty := by
  have : @Smooth (restrictedTriple T' m (pos T' hj') hI' hmax').X.left
      (restrictedTriple T m (pos T hj) hI hmax).X.left (restrictedMap hpb m j hj hj') :=
    smooth_restrictedMap hpb m j hj hj'
  have hg : B.seq (restrictedTriple T' m (pos T' hj') hI' hmax')
        (hDom _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl) =
      ((B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)).pullback
        (restrictedMap hpb m j hj hj')).eraseEmpty :=
    hB.2 (restrictedTriple T m (pos T hj) hI hmax) (restrictedTriple T' m (pos T' hj') hI' hmax')
      (restrictedMap hpb m j hj hj')
      (isPullbackOf_restrictedTriple hpb m j hj hj' hI hmax hI' hmax')
      _ _
  have e1 := pullback_pushforward_of_isPullback
    (BlowUpSequence.cons _ (centerS T m (pos T hj))
      (B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)))
    (T.E.component (pos T hj)).subschemeι h (T'.E.component (pos T' hj')).subschemeι
    (restrictionMap hpb.2.2 hj hj') (isPullback_restrictionMap hpb.2.2 hj hj')
  have hY : (B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)).pullback
        (restrictedMap hpb m j hj hj') =
      ((B.seq (restrictedTriple T m (pos T hj) hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl)).pullback
        (Scheme.Hom.blowUpMap (restrictionMap hpb.2.2 hj hj') (centerS T m (pos T hj)))).pullback
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp
            (centerS_comap_restrictionMap hpb m j hj hj'))) :=
    pullback_comp _ _ _
  have e2 : (BlowUpSequence.cons _ (centerS T' m (pos T' hj'))
        (B.seq (restrictedTriple T' m (pos T' hj') hI' hmax')
          (hDom _ (hasDimLE_restrictedTriple T' m _ hI' hmax' hn') rfl))).eraseEmpty =
      ((BlowUpSequence.cons _ (centerS T m (pos T hj))
        (B.seq (restrictedTriple T m (pos T hj) hI hmax)
          (hDom _ (hasDimLE_restrictedTriple T m _ hI hmax hn) rfl))).pullback
        (restrictionMap hpb.2.2 hj hj')).eraseEmpty :=
    (congrArg (fun Q : BlowUpSequence (centerS T' m (pos T' hj')).blowUp =>
        (BlowUpSequence.cons _ (centerS T' m (pos T' hj')) Q).eraseEmpty) hg).trans
      ((eraseEmpty_cons_eraseEmpty _ _).trans
        (congrArg BlowUpSequence.eraseEmpty
          ((cons_congr (centerS_comap_restrictionMap hpb m j hj hj')
            ((heq_of_eq hY).trans (Hironaka.Sequence.pullback_eqToHom_heq _ _))).trans
            (pullback_cons _ _ _).symm)))
  exact (eraseEmpty_pushforward _ _).trans
    ((congrArg (fun Q => BlowUpSequence.pushforward Q (T'.E.component (pos T' hj')).subschemeι)
      e2).trans ((eraseEmpty_pushforward _ _).symm.trans
        (congrArg BlowUpSequence.eraseEmpty e1.symm)))

end Pair

/-! ### Class transport and the functor level -/

section ClassTransport

omit [CharZero k] in
/-- D-balancedness ([Kol07, Definition 83]) pulls back along a smooth morphism. -/
theorem isDBalanced_comap_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] (g : Y ⟶ X) [Smooth g] {I : X.IdealSheafData} {m : ℕ} (hI : IsDBalanced f I m) :
    IsDBalanced (g ≫ f) (I.comap g) m := by
  intro i hi
  rw [derivativeIter_comap_of_smooth, ← comap_pow, ← comap_pow]
  exact comap_mono g (hI i hi)

omit [CharZero k] in
/-- The pull-back of a triple of the standing class of [Kol07, Lemma 102] along a smooth surjection,
when of dimension `≤ n`, is in the class. -/
theorem domain_pullback_of_surjective (n m j : ℕ) {T T' : Triple k} {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hpb : T'.IsPullbackOf T h) (hs : Function.Surjective h) (hT : Domain n m j T)
    (hn' : T'.HasDimLE n) : Domain n m j T' := by
  obtain ⟨hover, hI, hE⟩ := hpb
  refine ⟨hn', ?_, ?_, ?_⟩
  · rw [hI, ← hover]
    exact isDBalanced_comap_of_smooth _ h hT.2.1
  · rw [hI, le_antisymm (Hironaka.BO.maxOrd_comap_le_of_smooth h T.I)
      (Hironaka.BO.maxOrd_le_maxOrd_comap_of_surjective h hs T.I)]
    exact hT.2.2.1
  · have : Fintype.card T'.E.ι = Fintype.card T.E.ι := by rw [hE]; rfl
    rw [this]
    exact hT.2.2.2

end ClassTransport

section FunctorLevel

variable (n m j : ℕ) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')

/-- `BD_{n,m,j}` commutes with smooth morphisms when `B` does ([Kol07, 34.1]; clause (2) of
[Kol07, Lemma 102]). -/
theorem functor_commutesWithSmooth (hB : B.CommutesWithSmooth) :
    (functor n m j B hDom).CommutesWithSmooth := by
  rw [OrderSeqAssignment.commutesWithSmooth_iff]
  intro T T' h _ hpb hT hT'
  rw [functor_seq, functor_seq, eraseEmpty_pullback_eraseEmpty']
  exact eraseEmpty_rawSeq_pullback hpb m j hT.2.2.2 hT'.2.2.2 hT.2.1 hT.2.2.1 hT'.2.1 hT'.2.2.1
    hT.1 hT'.1 B hDom hB

/-- `BD_{n,m,j}` commutes with smooth surjections when `B` does. -/
theorem functor_commutesWithSmoothSurjections (hB : B.CommutesWithSmoothSurjections) :
    (functor n m j B hDom).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hpb hT hT'
  rw [functor_seq, functor_seq,
    rawSeq_pullback_of_surjective hpb m j hT.2.2.2 hT'.2.2.2 hT.2.1 hT.2.2.1 hT'.2.1 hT'.2.2.1
      hT.1 hT'.1 B hDom hs hB]
  exact eraseEmpty_pullback_of_flat_surjective _ _ hs

end FunctorLevel

end Hironaka.BD
