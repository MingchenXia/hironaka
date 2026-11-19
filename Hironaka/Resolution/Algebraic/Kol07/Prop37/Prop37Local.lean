/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Setting
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Smooth blow-ups of order `m` are Zariski-local: descent of Definitions 65 and 66

The proof of [Kol07, Proposition 37] glues the first centers `Z₀ᵢ' ⊂ Uᵢ` of the local sequences
to a center `Z₀ ⊂ X` and continues "this way we obtain `X₁ := B_{Z₀} X`"; that the glued center
is again a **smooth blow-up of order `m`** for `(X, I, E)` ([Kol07, Definition 65]: `Z₀` smooth
over `k`, having simple normal crossings with `E`, with `ord_{Z₀} I = m`) is left implicit, the
three conditions being local on `X`. This module proves it, for a covering family of open
immersions `ι i : W i → X` along which the center and the data are pulled back, and then for the
cover `g : X' = ∐ Uᵢ → X` of `Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean` (where
the conditions on `X'` first restrict to the pieces `Uᵢ` by the smooth-pullback lemmas of
`Hironaka/Sequence/Pullback*.lean`, the inclusions being open immersions). It then shows that the
condition of
[Kol07, Definition 66] on a whole sequence is local, and combines this with the descent of
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Descent.lean`.

* **Smoothness** (`smooth_subschemeι_comp_of_covers`): `V(Z) → Spec k` is smooth when its
  restrictions to the open pieces `V(Z|_{Uᵢ}) = V(Z) ∩ Uᵢ` are; smoothness is local at the source
  (Mathlib's `IsZariskiLocalAtSource`, applied by hand), the pieces being an open cover of `V(Z)`
  by the base-change squares `AlgebraicGeometry.isPullback_subschemeι_comap`.
* **Simple normal crossings** (`hasSncWith_of_covers`): condition (4) of [Kol07, Definition 24] is
  a condition at each point `x ∈ Z` on the stalk `𝒪_{X,x}`; an open immersion `ι` is an
  isomorphism on stalks, so the coordinates at `w ∈ ι⁻¹ Z` transport to coordinates at `ι w`:
  regular systems of parameters along a ring isomorphism
  (`isRegularSystemOfParameters_comp_ringEquiv`), the stalks of the inverse images being the
  images of the stalks (`stalkIdeal_comap`). This is the transport of snc data along a smooth
  morphism in the other direction, available because the stalk map is invertible.
* **The order** (`ordAlongEq_of_covers`, `leOrdAlong_of_covers`): `ord_Z I` is computed at the
  generic points of `Z`; a generic point of `Z` lying in `Uᵢ` is a generic point of `Z ∩ Uᵢ`
  (specialisation is reflected by an open embedding,
  `mem_genericPoints_comap_of_isOpenImmersion`), and the order at a point is invariant under open
  immersions (`ord_comap_of_isOpenImmersion`).
* **The triples** (`Triple.isOrderBlowUp_of_isPullbackOf_covers`,
  `Triple.isOrderBlowUp_of_coverDesc` and the marked versions): the corollaries in the vocabulary
  of Definition 65 on triples carrying the pullback data (`IsPullbackOf`), the `coverDesc` form
  restricting the hypothesis on `X'` to the summands `Uᵢ` along the open immersions `Sigma.ι`
  first.
* **Definition 66 is local, stage by stage** (`isOrderSeq_of_covers`, `isOrderGeSeq_of_covers`):
  a blow-up sequence on `X` is a smooth blow-up sequence of order `m` for `(X, I, E)` when its
  pullbacks to the members of a covering family of open immersions are, for the pulled-back data.
  By induction on the sequence: the first center's three conditions descend (above); then the
  induced data of the pullbacks are the pullbacks of the induced data (the total transform along
  any flat morphism; the weak transform because the order along the center is now known on `X`,
  `weakTransform_comap_of_orderAlong_of_equidim`; the marked transform along any flat morphism
  given `F^m ∣ π^* I`), so the tails are pullbacks of the tail on `Z₀.blowUp` along the lifted
  covering family, to which the induction hypothesis applies.
* **The descent with the order** (`Triple.exists_isOrderSeq_pullback_eq_of_agreeOnOverlaps`,
  `Triple.exists_isOrderSeq_pullback_coverDesc_eq`, marked versions): the descent of the sequence
  (`exists_pullback_eq_of_agreeOnOverlaps`, `Triple.exists_pullback_coverDesc_eq`) followed by
  the locality of Definition 66; on the affine cover the hypothesis on `X'` restricts to the
  summands first (`IsOrderSeq.pullback_of_equidim`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.IdealSheafData
  Scheme IsLocalRing BlowUpSequence TopologicalSpace

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Transport of local coordinates along a ring isomorphism -/

/-- A regular system of parameters transports along an isomorphism of local rings: the image of the
maximal ideal is the maximal ideal (a surjection of local rings is a local homomorphism) and the
Krull dimension is invariant. -/
theorem isRegularSystemOfParameters_comp_ringEquiv {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (e : R ≃+* S) {n : ℕ} {z : Fin n → R}
    (hz : IsRegularSystemOfParameters z) : IsRegularSystemOfParameters (fun i => e (z i)) := by
  obtain ⟨hspan, hdim⟩ := hz
  have : IsLocalHom (e : R →+* S) := IsLocalHom.of_surjective _ e.surjective
  have : IsLocalHom (e.symm : S →+* R) := IsLocalHom.of_surjective _ e.symm.surjective
  refine ⟨?_, hdim.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have hrange : Set.range (fun i => e (z i)) = (e : R →+* S) '' Set.range z := by
    ext s
    simp
  rw [hrange, ← Ideal.map_span, hspan]
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
  intro s hs
  have h₁ : e.symm s ∈ IsLocalRing.maximalIdeal R :=
    IsLocalRing.map_maximalIdeal_le (e.symm : S →+* R) (Ideal.mem_map_of_mem _ hs)
  have h₂ : s = (e : R →+* S) (e.symm s) := (e.apply_symm_apply s).symm
  rw [h₂]
  exact Ideal.mem_map_of_mem _ h₁

/-- An ideal whose image under a ring isomorphism is `J` is the image of `J` under the inverse. -/
theorem Ideal.eq_map_symm_of_map_eq {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {I : Ideal R} {J : Ideal S} (h : I.map e = J) : I = J.map e.symm := by
  rw [Ideal.map_symm, ← h, Ideal.comap_map_of_bijective _ e.bijective]

/-! ### Descent of the stalk conditions along an open immersion -/

variable {W : Scheme.{u}} (ι : W ⟶ X) [IsOpenImmersion ι]

/-- The stalk map of an open immersion, as a ring isomorphism `𝒪_{X, ι w} ≃ 𝒪_{W, w}`. -/
noncomputable def stalkEquivOfIsOpenImmersion (w : W) :
    X.presheaf.stalk (ι w) ≃+* W.presheaf.stalk w :=
  (asIso (ι.stalkMap w)).commRingCatIsoToRingEquiv

theorem stalkEquivOfIsOpenImmersion_toRingHom (w : W) :
    ((stalkEquivOfIsOpenImmersion ι w : X.presheaf.stalk (ι w) ≃+* W.presheaf.stalk w) :
      X.presheaf.stalk (ι w) →+* W.presheaf.stalk w) = (ι.stalkMap w).hom := by
  simp [stalkEquivOfIsOpenImmersion]

/-- The stalk of an ideal sheaf at `ι w` is the preimage, under the stalk isomorphism, of the stalk
of its inverse image at `w` (`stalkIdeal_comap` read backwards). -/
theorem stalkIdeal_eq_map_symm_stalkIdeal_comap (J : X.IdealSheafData) (w : W) :
    J.stalkIdeal (ι w) =
      ((J.comap ι).stalkIdeal w).map (stalkEquivOfIsOpenImmersion ι w).symm := by
  apply Ideal.eq_map_symm_of_map_eq
  rw [Scheme.IdealSheafData.stalkIdeal_comap]
  rfl

/-- Coordinates at `w` transport to coordinates at `ι w` along the stalk isomorphism. -/
noncomputable def transportCoords (w : W) {n : ℕ} (z : Fin n → W.presheaf.stalk w) :
    Fin n → X.presheaf.stalk (ι w) :=
  fun i => (stalkEquivOfIsOpenImmersion ι w).symm (z i)

/-- Simple normal crossings at a point [Kol07, Definition 24] descend along an open immersion:
the coordinates at `w` transport to coordinates at `ι w`, the components of `E` through `ι w` are
the components of `ι⁻¹ E` through `w`, and their stalks correspond (the stalk map being an
isomorphism). -/
theorem isSncAt_of_isOpenImmersion (E : DivisorFamily X) {w : W} {n : ℕ}
    {z : Fin n → W.presheaf.stalk w} (h : (E.comap ι).IsSncAt w z) :
    E.IsSncAt (ι w) (transportCoords ι w z) := by
  obtain ⟨hz, c, hc, hcE⟩ := h
  refine ⟨isRegularSystemOfParameters_comp_ringEquiv _ hz, ?_⟩
  let τ : {i : E.ι // ι w ∈ (E.component i).support} →
      {i : (E.comap ι).ι // w ∈ ((E.comap ι).component i).support} :=
    fun i => ⟨i.1, (mem_support_comap_iff_apply (E.component i.1) ι w).mpr i.2⟩
  have hτ : Function.Injective τ := fun i j hij =>
    Subtype.ext (show (τ i).1 = (τ j).1 from congrArg Subtype.val hij)
  refine ⟨fun i => c (τ i), hc.comp hτ, fun i => ?_⟩
  have hi := hcE (τ i)
  change ((E.component i.1).comap ι).stalkIdeal w = Ideal.span {z (c (τ i))} at hi
  change (E.component i.1).stalkIdeal (ι w) =
    Ideal.span {(stalkEquivOfIsOpenImmersion ι w).symm (z (c (τ i)))}
  rw [stalkIdeal_eq_map_symm_stalkIdeal_comap ι (E.component i.1) w, hi, Ideal.map_span,
    Set.image_singleton]

/-- Simple normal crossings of a closed subscheme with a family [Kol07, Definition 24 (4)]
descend along a covering family of open immersions: at a point `x = ι i w` of `Z` the coordinates
at `w` for `ι⁻¹ Z`, `ι⁻¹ E` transport to `x`. -/
theorem hasSncWith_of_covers {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (E : DivisorFamily X)
    (Z : X.IdealSheafData) (h : ∀ i, (E.comap (ι i)).HasSncWith (Z.comap (ι i))) :
    E.HasSncWith Z := by
  intro x hx
  obtain ⟨i, w, rfl⟩ := hcov x
  have hw : w ∈ (Z.comap (ι i)).support := (mem_support_comap_iff_apply Z (ι i) w).mpr hx
  obtain ⟨n, z, hz, s, hs⟩ := h i w hw
  refine ⟨n, transportCoords (ι i) w z, isSncAt_of_isOpenImmersion (ι i) E hz, s, ?_⟩
  rw [stalkIdeal_eq_map_symm_stalkIdeal_comap (ι i) Z w, hs, Ideal.map_span, Set.image_image]
  rfl

/-! ### Descent of the order along an open immersion -/

/-- A generic point of `Z` lying in the image of the open immersion `ι` comes from a generic point
of `ι⁻¹ Z`: specialisation is reflected by an open embedding, so a generisation of `w` in `ι⁻¹ Z`
maps to a generisation of `ι w` in `Z`, which is `ι w` itself. -/
theorem mem_genericPoints_comap_of_isOpenImmersion (Z : X.IdealSheafData) {w : W}
    (hη : ι w ∈ Z.support.genericPoints) : w ∈ (Z.comap ι).support.genericPoints := by
  obtain ⟨hmem, hmax⟩ := hη
  refine ⟨(mem_support_comap_iff_apply Z ι w).mpr hmem, fun w' hw' hspec => ?_⟩
  have h₁ : ι w' ∈ Z.support := (mem_support_comap_iff_apply Z ι w').mp hw'
  have h₂ : ι w' ⤳ ι w := hspec.map ι.continuous
  exact ι.isOpenEmbedding.injective (hmax h₁ h₂)

/-- The order condition `ord_Z I = m` of [Kol07, Definition 65 (2)] descends along a covering
family of open immersions: every generic point of `Z` is a generic point of some `Z ∩ Uᵢ`, where
the order is that of the inverse image. -/
theorem ordAlongEq_of_covers {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (I Z : X.IdealSheafData)
    {m : ℕ∞} (h : ∀ i, (I.comap (ι i)).OrdAlongEq (Z.comap (ι i)).support m) :
    I.OrdAlongEq Z.support m := by
  intro η hη
  obtain ⟨i, w, rfl⟩ := hcov η
  have hw := mem_genericPoints_comap_of_isOpenImmersion (ι i) Z hη
  have := h i w hw
  rwa [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion] at this

/-- The marked form: `ord_Z I ≥ m` descends along a covering family of open immersions. -/
theorem leOrdAlong_of_covers {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (I Z : X.IdealSheafData)
    {m : ℕ∞} (h : ∀ i, (I.comap (ι i)).LeOrdAlong (Z.comap (ι i)).support m) :
    I.LeOrdAlong Z.support m := by
  intro η hη
  obtain ⟨i, w, rfl⟩ := hcov η
  have hw := mem_genericPoints_comap_of_isOpenImmersion (ι i) Z hη
  have := h i w hw
  rwa [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion] at this

/-! ### Descent of smoothness of the centre along an open cover -/

/-- Smoothness of the center ([Kol07, Definition 65 (1)] with Notation 19): `V(Z) → B` is smooth
when its restrictions to the open pieces `V(Z|_{Uᵢ}) = V(Z) ∩ Uᵢ` of a covering family of open
immersions are; smoothness is local at the source (`IsZariskiLocalAtSource`, applied by hand),
the pieces forming an open cover of `V(Z)` by the base-change squares
`AlgebraicGeometry.isPullback_subschemeι_comap`. -/
theorem smooth_subschemeι_comp_of_covers {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (Z : X.IdealSheafData)
    {B : Scheme.{u}} (f : X ⟶ B) (h : ∀ i, Smooth ((Z.comap (ι i)).subschemeι ≫ ι i ≫ f)) :
    Smooth (Z.subschemeι ≫ f) := by
  -- Mathlib's instance `HasRingHomProperty.instIsZariskiLocalAtSource` is not found by instance
  -- search here; it is applied by hand.
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  let m : ∀ i, (Z.comap (ι i)).subscheme ⟶ Z.subscheme := fun i =>
    Scheme.IdealSheafData.subschemeMap (Z.comap (ι i)) Z (ι i)
      (Scheme.IdealSheafData.le_map_comap Z (ι i))
  have hsq : ∀ i, IsPullback (Z.comap (ι i)).subschemeι (m i) (ι i) Z.subschemeι := fun i =>
    isPullback_subschemeι_comap Z (ι i)
  have hio : ∀ i, IsOpenImmersion (m i) := fun i =>
    property_of_isPullback _ (hsq i).flip inferInstance
  have hcov' : ∀ z, ∃ i w, m i w = z := by
    intro z
    obtain ⟨i, w, hw⟩ := hcov (Z.subschemeι z)
    have hrange := range_fst_of_isPullback (hsq i).flip
    have hz : z ∈ Set.range (m i) := by
      rw [hrange]
      exact ⟨w, hw⟩
    obtain ⟨y, hy⟩ := hz
    exact ⟨i, y, hy⟩
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers σ (fun i => (Z.comap (ι i)).subscheme) m hcov') fun i => ?_
  change Smooth (m i ≫ Z.subschemeι ≫ f)
  rw [← Category.assoc, ← (hsq i).w, Category.assoc]
  exact h i

end Hironaka.Sequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### Definition 66 is local: stagewise descent along a covering family of open immersions -/

/-- The condition of [Kol07, Definition 66] is local: a blow-up sequence on `X` is a smooth blow-up
sequence of order `m` for `(X, I, E)` when its pullbacks along a covering family of open
immersions are, for the pulled-back data (the recursion of the proof of
[Kol07, Proposition 37]). Induction on the sequence: the first center's conditions descend
(`smooth_subschemeι_comp_of_covers`, `hasSncWith_of_covers`, `ordAlongEq_of_covers`); with the
order along the center known on `X`, the weak and total transforms commute with the pullbacks
along the lifted family, so the tails are the pullbacks of the tail along the lifted covering
family, and the induction hypothesis applies on `Z₀.blowUp`. -/
theorem isOrderSeq_of_covers [CharZero k] (S : BlowUpSequence X) :
    ∀ (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {σ : Type u}
      {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (ι i)],
      (∀ x, ∃ i w, ι i w = x) → ∀ (I : X.IdealSheafData) (E : DivisorFamily X) {m : ℕ},
      (∀ i, (S.pullback (ι i)).IsOrderSeq (ι i ≫ f) (I.comap (ι i)) (E.comap (ι i)) m) →
      S.IsOrderSeq f I E m := by
  induction S with
  | nil X =>
    intro f n _ σ W ι _ _ I E m _
    exact isOrderSeq_nil (f := f) (I := I) (E := E) (m := m)
  | cons X D rest ih =>
    intro f n _ σ W ι _ hcov I E m h
    have h' : ∀ i, (Smooth ((D.comap (ι i)).subschemeι ≫ ι i ≫ f) ∧
        (E.comap (ι i)).HasSncWith (D.comap (ι i)) ∧
        (I.comap (ι i)).OrdAlongEq (D.comap (ι i)).support (m : ℕ∞)) ∧
        (rest.pullback (Scheme.Hom.blowUpMap (ι i) D)).IsOrderSeq ((D.comap (ι i)).blowUpπ ≫ ι i ≫
            f)
          ((I.comap (ι i)).weakTransform (D.comap (ι i)))
          ((E.comap (ι i)).totalTransform (D.comap (ι i))) m := fun i => by
      have hi : (cons (W i) (D.comap (ι i))
          (rest.pullback (Scheme.Hom.blowUpMap (ι i) D))).IsOrderSeq
          (ι i ≫ f) (I.comap (ι i)) (E.comap (ι i)) m := h i
      exact (isOrderSeq_cons_iff _ _ _ _ _ _).1 hi
    have hsm : Smooth (D.subschemeι ≫ f) :=
      smooth_subschemeι_comp_of_covers ι hcov D f fun i => (h' i).1.1
    have hsnc : E.HasSncWith D := hasSncWith_of_covers ι hcov E D fun i => (h' i).1.2.1
    have hord : I.OrdAlongEq D.support (m : ℕ∞) :=
      ordAlongEq_of_covers ι hcov I D fun i => (h' i).1.2.2
    refine (isOrderSeq_cons_iff _ _ _ _ _ _).2 ⟨⟨hsm, hsnc, hord⟩, ?_⟩
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    refine ih (D.blowUpπ ≫ f) n (fun i => Scheme.Hom.blowUpMap (ι i) D)
      (exists_blowUpMap_eq_of_covers ι hcov D) (I.weakTransform D) (E.totalTransform D)
      fun i => ?_
    have hSORD : SmoothOfRelativeDimension n (ι i ≫ f) := by
      simpa using smoothOfRelativeDimension_comp 0 n (ι i) f
    have hw : (I.comap (ι i)).weakTransform (D.comap (ι i)) =
        (I.weakTransform D).comap (Scheme.Hom.blowUpMap (ι i) D) :=
      weakTransform_comap_of_orderAlong_of_equidim f n (ι i) n D I hord
    have ht : (E.comap (ι i)).totalTransform (D.comap (ι i)) =
        (E.totalTransform D).comap (Scheme.Hom.blowUpMap (ι i) D) :=
      totalTransform_comap_of_flat (ι i) D E
    have hcomp : (D.comap (ι i)).blowUpπ ≫ ι i ≫ f = Scheme.Hom.blowUpMap (ι
        i) D ≫ D.blowUpπ ≫ f := by
      rw [← Category.assoc, ← blowUpMap_π, Category.assoc]
    have := (h' i).2
    rwa [hcomp, hw, ht] at this

/-- The marked condition of [Kol07, Definition 66] is local: the marked transform commutes with
the pullbacks along the lifted family for any flat morphism, given `F^m ∣ π^* I` (from the order
`≥ m` along the center, now known on `X`). -/
theorem isOrderGeSeq_of_covers [CharZero k] (S : BlowUpSequence X) :
    ∀ (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {σ : Type u}
      {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (ι i)],
      (∀ x, ∃ i w, ι i w = x) → ∀ (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X),
      (∀ i, (S.pullback (ι i)).IsOrderGeSeq (ι i ≫ f) (I.comap (ι i)) m (E.comap (ι i))) →
      S.IsOrderGeSeq f I m E := by
  induction S with
  | nil X =>
    intro f n _ σ W ι _ _ I m E _
    exact isOrderGeSeq_nil (f := f) (I := I) (E := E) (m := m)
  | cons X D rest ih =>
    intro f n _ σ W ι _ hcov I m E h
    have h' : ∀ i, (Smooth ((D.comap (ι i)).subschemeι ≫ ι i ≫ f) ∧
        (E.comap (ι i)).HasSncWith (D.comap (ι i)) ∧
        (I.comap (ι i)).LeOrdAlong (D.comap (ι i)).support (m : ℕ∞)) ∧
        (rest.pullback (Scheme.Hom.blowUpMap (ι i) D)).IsOrderGeSeq ((D.comap (ι i)).blowUpπ ≫ ι i ≫
            f)
          ((I.comap (ι i)).markedTransform (D.comap (ι i)) m) m
          ((E.comap (ι i)).totalTransform (D.comap (ι i))) := fun i => by
      have hi : (cons (W i) (D.comap (ι i))
          (rest.pullback (Scheme.Hom.blowUpMap (ι i) D))).IsOrderGeSeq
          (ι i ≫ f) (I.comap (ι i)) m (E.comap (ι i)) := h i
      exact (isOrderGeSeq_cons_iff _ _ _ _ _ _).1 hi
    have hsm : Smooth (D.subschemeι ≫ f) :=
      smooth_subschemeι_comp_of_covers ι hcov D f fun i => (h' i).1.1
    have hsnc : E.HasSncWith D := hasSncWith_of_covers ι hcov E D fun i => (h' i).1.2.1
    have hord : I.LeOrdAlong D.support (m : ℕ∞) :=
      leOrdAlong_of_covers ι hcov I D fun i => (h' i).1.2.2
    refine (isOrderGeSeq_cons_iff _ _ _ _ _ _).2 ⟨⟨hsm, hsnc, hord⟩, ?_⟩
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    refine ih (D.blowUpπ ≫ f) n (fun i => Scheme.Hom.blowUpMap (ι i) D)
      (exists_blowUpMap_eq_of_covers ι hcov D) (I.markedTransform D m) m (E.totalTransform D)
      fun i => ?_
    have hw : (I.comap (ι i)).markedTransform (D.comap (ι i)) m =
        (I.markedTransform D m).comap (Scheme.Hom.blowUpMap (ι i) D) :=
      markedTransform_comap_blowUpMap_of_pow_dvd (ι i) D I m
        (pow_dvd_comap_of_leOrdAlong f n D I hord)
    have ht : (E.comap (ι i)).totalTransform (D.comap (ι i)) =
        (E.totalTransform D).comap (Scheme.Hom.blowUpMap (ι i) D) :=
      totalTransform_comap_of_flat (ι i) D E
    have hcomp : (D.comap (ι i)).blowUpπ ≫ ι i ≫ f = Scheme.Hom.blowUpMap (ι
        i) D ≫ D.blowUpπ ≫ f := by
      rw [← Category.assoc, ← blowUpMap_π, Category.assoc]
    have := (h' i).2
    rwa [hcomp, hw, ht] at this

end Hironaka.Sequence

namespace Hironaka

variable {k : Type u} [Field k]

/-! ### Descent of Definition 65 on triples -/

/-- If the inverse images of a center `Z ⊂ X` along a covering family of open immersions
`ι i : (Ts i).X.left → T.X.left`, the `Ts i` carrying the pullback data of `T`, are smooth blow-ups
of order `m` ([Kol07, Definition 65]) for the `Ts i`, then `Z` is one for `T`: the three conditions
are local on `X` (`smooth_subschemeι_comp_of_covers`, `hasSncWith_of_covers`,
`ordAlongEq_of_covers`). This is the step left implicit in the proof of
[Kol07, Proposition 37]. -/
theorem _root_.AlgebraicGeometry.Triple.isOrderBlowUp_of_isPullbackOf_covers
    {T : Triple k} {σ : Type u}
    {Ts : σ → Triple k} (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) [∀ i, IsOpenImmersion (ι i)]
    (hcov : ∀ x, ∃ i w, ι i w = x) (hp : ∀ i, (Ts i).IsPullbackOf T (ι i))
    (Z : T.X.left.IdealSheafData)
    {m : ℕ} (h : ∀ i, (Ts i).IsOrderBlowUp (Z.comap (ι i)) m) : T.IsOrderBlowUp Z m := by
  refine ⟨Hironaka.Sequence.smooth_subschemeι_comp_of_covers ι hcov Z _ fun i => ?_,
    Hironaka.Sequence.hasSncWith_of_covers ι hcov T.E Z fun i => ?_,
    Hironaka.Sequence.ordAlongEq_of_covers ι hcov T.I Z fun i => ?_⟩
  · have := (h i).1
    rwa [← (hp i).1] at this
  · have := (h i).2.1
    rwa [(hp i).2.2] at this
  · have := (h i).2.2
    rwa [(hp i).2.1] at this

/-- The marked version: a center whose inverse images are smooth blow-ups of order `≥ m` for the
pieces is one for `T`. -/
theorem MarkedTriple.isOrderGeBlowUp_of_isPullbackOf_covers {T : MarkedTriple k}
    {σ : Type u} {Ts : σ → MarkedTriple k} (ι : ∀ i, (Ts i).X.left ⟶ T.X.left)
    [∀ i, IsOpenImmersion (ι i)]
    (hcov : ∀ x, ∃ i w, ι i w = x) (hp : ∀ i, (Ts i).IsPullbackOf T (ι i))
    (Z : T.X.left.IdealSheafData) (h : ∀ i, (Ts i).IsOrderGeBlowUp (Z.comap (ι i))) :
    T.IsOrderGeBlowUp Z := by
  refine ⟨Hironaka.Sequence.smooth_subschemeι_comp_of_covers ι hcov Z _ fun i => ?_,
    Hironaka.Sequence.hasSncWith_of_covers ι hcov T.E Z fun i => ?_,
    Hironaka.Sequence.leOrdAlong_of_covers ι hcov T.I Z fun i => ?_⟩
  · have := (h i).1
    rwa [← (hp i).1.1] at this
  · have := (h i).2.1
    rwa [(hp i).1.2.2] at this
  · have := (h i).2.2
    rwa [(hp i).1.2.1, (hp i).2] at this

/-! ### Descent of Definition 65 along the affine cover -/

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- The members `Uᵢ → X` of the affine cover form a covering family of open immersions. -/
theorem exists_affineCover_f_eq (T : Triple k) (x : T.X.left) : ∃ i w, T.affineCover.f i w = x :=
  T.affineCover.exists_eq x

/-- A center of `X` whose inverse image on `X'` is a smooth blow-up of order `m` for
`(X', g^* I, g^{-1} E)` is one for `(X, I, E)`: the three conditions restrict from `X' = ∐ Uᵢ` to
each summand `Uᵢ` along the open immersion `Sigma.ι i` (the smooth-pullback lemmas), and descend
from the summands to `X`. -/
theorem isOrderBlowUp_of_coverDesc [CharZero k] (T : Triple k) (Z : T.X.left.IdealSheafData) {m : ℕ}
    (h : T.coverTriple.IsOrderBlowUp (Z.comap T.coverDesc) m) : T.IsOrderBlowUp Z m := by
  obtain ⟨hsm, hsnc, hord⟩ := h
  have hZ : ∀ i, Z.comap (T.affineCover.f i) =
      (Z.comap T.coverDesc).comap (Sigma.ι (fun i => T.affineCover.X i) i) := fun i => by
    rw [← Scheme.IdealSheafData.comap_comp, ι_comp_coverDesc]
  have hI : ∀ i, T.I.comap (T.affineCover.f i) =
      (T.I.comap T.coverDesc).comap (Sigma.ι (fun i => T.affineCover.X i) i) := fun i => by
    rw [← Scheme.IdealSheafData.comap_comp, ι_comp_coverDesc]
  have hE : ∀ i, T.E.comap (T.affineCover.f i) =
      (T.E.comap T.coverDesc).comap (Sigma.ι (fun i => T.affineCover.X i) i) := fun i => by
    rw [← DivisorFamily.comap_comp, ι_comp_coverDesc]
  have hsmX' : Smooth (T.coverScheme ↘ Spec (CommRingCat.of k)) := T.coverTriple.smooth
  refine ⟨Hironaka.Sequence.smooth_subschemeι_comp_of_covers T.affineCover.f
      (exists_affineCover_f_eq T) Z _ fun i => ?_,
    Hironaka.Sequence.hasSncWith_of_covers T.affineCover.f (exists_affineCover_f_eq T) T.E Z
      fun i => ?_,
    Hironaka.Sequence.ordAlongEq_of_covers T.affineCover.f (exists_affineCover_f_eq T) T.I Z
      fun i => ?_⟩
  · have : Smooth ((Z.comap T.coverDesc).subschemeι ≫
        T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := hsm
    rw [hZ i, ← ι_comp_coverDesc T i, Category.assoc]
    exact smooth_subschemeι_comap_comp (Z.comap T.coverDesc)
      (Sigma.ι (fun i => T.affineCover.X i) i) (T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
  · rw [hZ i, hE i]
    exact hasSncWith_comap_of_smooth (T.coverScheme ↘ Spec (.of k)) _ hsnc
  · rw [hZ i, hI i]
    exact ordAlongEq_comap_of_smooth _ hord

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

namespace MarkedTriple

/-- The marked version along the affine cover. -/
theorem isOrderGeBlowUp_of_coverDesc [CharZero k] (T : MarkedTriple k) (Z : T.X.left.IdealSheafData)
    (h : T.coverTriple.IsOrderGeBlowUp (Z.comap T.toTriple.coverDesc)) : T.IsOrderGeBlowUp Z := by
  obtain ⟨hsm, hsnc, hord⟩ := h
  have hZ : ∀ i, Z.comap (T.toTriple.affineCover.f i) =
      (Z.comap T.toTriple.coverDesc).comap (Sigma.ι (fun i => T.toTriple.affineCover.X i) i) :=
    fun i => by rw [← Scheme.IdealSheafData.comap_comp, Triple.ι_comp_coverDesc]
  have hI : ∀ i, T.I.comap (T.toTriple.affineCover.f i) =
      (T.I.comap T.toTriple.coverDesc).comap (Sigma.ι (fun i => T.toTriple.affineCover.X i) i) :=
    fun i => by rw [← Scheme.IdealSheafData.comap_comp, Triple.ι_comp_coverDesc]
  have hE : ∀ i, T.E.comap (T.toTriple.affineCover.f i) =
      (T.E.comap T.toTriple.coverDesc).comap (Sigma.ι (fun i => T.toTriple.affineCover.X i) i) :=
    fun i => by rw [← DivisorFamily.comap_comp, Triple.ι_comp_coverDesc]
  have hsmX' : Smooth (T.toTriple.coverScheme ↘ Spec (CommRingCat.of k)) :=
    T.toTriple.coverTriple.smooth
  refine ⟨Hironaka.Sequence.smooth_subschemeι_comp_of_covers T.toTriple.affineCover.f
      (Triple.exists_affineCover_f_eq T.toTriple) Z _ fun i => ?_,
    Hironaka.Sequence.hasSncWith_of_covers T.toTriple.affineCover.f
      (Triple.exists_affineCover_f_eq T.toTriple) T.E Z fun i => ?_,
    Hironaka.Sequence.leOrdAlong_of_covers T.toTriple.affineCover.f
      (Triple.exists_affineCover_f_eq T.toTriple) T.I Z fun i => ?_⟩
  · have : Smooth ((Z.comap T.toTriple.coverDesc).subschemeι ≫
        T.toTriple.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := hsm
    rw [hZ i, ← Triple.ι_comp_coverDesc T.toTriple i, Category.assoc]
    exact smooth_subschemeι_comap_comp (Z.comap T.toTriple.coverDesc)
      (Sigma.ι (fun i => T.toTriple.affineCover.X i) i)
      (T.toTriple.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
  · rw [hZ i, hE i]
    exact hasSncWith_comap_of_smooth (T.toTriple.coverScheme ↘ Spec (.of k)) _
      hsnc
  · rw [hZ i, hI i]
    exact leOrdAlong_comap_of_smooth _ hord

end MarkedTriple

/-! ### The descent with the order -/

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

open Scheme

/-- The descent of the proof of [Kol07, Proposition 37] with the order condition of
[Kol07, Definition 66]: if each `S i` is a smooth blow-up sequence of order `m` for the
pullback-data triple `Ts i`, the descended sequence (`exists_pullback_eq_of_agreeOnOverlaps`) is
one for `T`, Definition 66 being local (`isOrderSeq_of_covers`). -/
theorem exists_isOrderSeq_pullback_eq_of_agreeOnOverlaps [CharZero k] {T : Triple k} {σ : Type u}
    {Ts : σ → Triple k} (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) [∀ i, IsOpenImmersion (ι i)]
    (hcov : ∀ x, ∃ i w, ι i w = x) (hp : ∀ i, (Ts i).IsPullbackOf T (ι i))
    (S : ∀ i, BlowUpSequence (Ts i).X.left) {m : ℕ}
    (hS : ∀ i, (S i).IsOrderSeq ((Ts i).X.left ↘ Spec (.of k)) (Ts i).I (Ts i).E m)
    (hc : BlowUpSequence.AgreeOnOverlaps ι S) :
    ∃ S₀ : BlowUpSequence T.X.left, S₀.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      ∀ i, S₀.pullback (ι i) = S i := by
  obtain ⟨S₀, hS₀⟩ := Hironaka.Sequence.exists_pullback_eq_of_agreeOnOverlaps ι hcov S hc
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨S₀, Hironaka.Sequence.isOrderSeq_of_covers S₀ (T.X.left ↘ Spec (.of k)) n ι hcov T.I T.E
    fun i => ?_, hS₀⟩
  rw [hS₀ i, (hp i).1, ← (hp i).2.1, ← (hp i).2.2]
  exact hS i

variable (T : Triple k)

/-- Kollár's form of the descent with the order (the proof of [Kol07, Proposition 37]): a smooth
blow-up sequence of order `m` for `(X', g^* I, g^{-1} E)` with `τ₁^* S' = τ₂^* S'` is `g^* S` for a
smooth blow-up sequence `S` of order `m` for `(X, I, E)`; the descent of the sequence, the
hypothesis restricted to the summands `Uᵢ` of `X'` (`IsOrderSeq.pullback_of_equidim` along the
open immersions `Sigma.ι`), and the locality of Definition 66. -/
theorem exists_isOrderSeq_pullback_coverDesc_eq [CharZero k] {m : ℕ}
    (S' : BlowUpSequence T.coverScheme)
    (hS : S'.IsOrderSeq (T.coverScheme ↘ Spec (.of k)) (T.I.comap T.coverDesc)
      (T.E.comap T.coverDesc) m)
    (h : S'.pullback T.coverFst = S'.pullback T.coverSnd) :
    ∃ S : BlowUpSequence T.X.left, S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.pullback T.coverDesc = S' := by
  obtain ⟨S, hS'⟩ := exists_pullback_coverDesc_eq T S' h
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := exists_smoothOfRelativeDimension_coverScheme T
  refine ⟨S, Hironaka.Sequence.isOrderSeq_of_covers S (T.X.left ↘ Spec (.of k)) n T.affineCover.f
    (exists_affineCover_f_eq T) T.I T.E fun i => ?_, hS'⟩
  have hSORD : SmoothOfRelativeDimension n' (Sigma.ι (fun i => T.affineCover.X i) i ≫
      (T.coverScheme ↘ Spec (CommRingCat.of k))) := by
    simpa using smoothOfRelativeDimension_comp 0 n' (Sigma.ι (fun i => T.affineCover.X i) i)
      (T.coverScheme ↘ Spec (CommRingCat.of k))
  have hpull := IsOrderSeq.pullback_of_equidim
    (T.coverScheme ↘ Spec (.of k)) n' (Sigma.ι (fun i => T.affineCover.X i) i) n' hS
  rw [← ι_comp_coverDesc T i, pullback_comp, hS',
    Scheme.IdealSheafData.comap_comp, DivisorFamily.comap_comp, Category.assoc]
  exact hpull

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

namespace MarkedTriple

open Scheme

/-- The marked version of the descent with the order. -/
theorem exists_isOrderGeSeq_pullback_eq_of_agreeOnOverlaps [CharZero k] {T : MarkedTriple k}
    {σ : Type u} {Ts : σ → MarkedTriple k} (ι : ∀ i, (Ts i).X.left ⟶ T.X.left)
    [∀ i, IsOpenImmersion (ι i)]
    (hcov : ∀ x, ∃ i w, ι i w = x) (hp : ∀ i, (Ts i).IsPullbackOf T (ι i))
    (S : ∀ i, BlowUpSequence (Ts i).X.left)
    (hS : ∀ i, (S i).IsOrderGeSeq ((Ts i).X.left ↘ Spec (.of k)) (Ts i).I (Ts i).m (Ts i).E)
    (hc : BlowUpSequence.AgreeOnOverlaps ι S) :
    ∃ S₀ : BlowUpSequence T.X.left, S₀.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧
      ∀ i, S₀.pullback (ι i) = S i := by
  obtain ⟨S₀, hS₀⟩ := Hironaka.Sequence.exists_pullback_eq_of_agreeOnOverlaps ι hcov S hc
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨S₀, Hironaka.Sequence.isOrderGeSeq_of_covers S₀ (T.X.left ↘ Spec (.of k)) n ι hcov T.I T.m
    T.E fun i => ?_, hS₀⟩
  rw [hS₀ i, (hp i).1.1, ← (hp i).1.2.1, ← (hp i).1.2.2, ← (hp i).2]
  exact hS i

/-- The marked version of Kollár's form of the descent, with the order `≥ m`. -/
theorem exists_isOrderGeSeq_pullback_coverDesc_eq [CharZero k] (T : MarkedTriple k)
    (S' : BlowUpSequence T.toTriple.coverScheme)
    (hS : S'.IsOrderGeSeq (T.toTriple.coverScheme ↘ Spec (.of k))
      (T.I.comap T.toTriple.coverDesc) T.m (T.E.comap T.toTriple.coverDesc))
    (h : S'.pullback T.toTriple.coverFst = S'.pullback T.toTriple.coverSnd) :
    ∃ S : BlowUpSequence T.X.left, S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧
      S.pullback T.toTriple.coverDesc = S' := by
  obtain ⟨S, hS'⟩ := Triple.exists_pullback_coverDesc_eq T.toTriple S' h
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := Triple.exists_smoothOfRelativeDimension_coverScheme T.toTriple
  refine ⟨S, Hironaka.Sequence.isOrderGeSeq_of_covers S (T.X.left ↘ Spec (.of k)) n
    T.toTriple.affineCover.f (Triple.exists_affineCover_f_eq T.toTriple) T.I T.m T.E
    fun i => ?_, hS'⟩
  have hpull := IsOrderGeSeq.pullback_of_smooth
    (T.toTriple.coverScheme ↘ Spec (.of k)) n' (Sigma.ι (fun i => T.toTriple.affineCover.X i) i) hS
  rw [← Triple.ι_comp_coverDesc T.toTriple i, pullback_comp, hS',
    Scheme.IdealSheafData.comap_comp, DivisorFamily.comap_comp, Category.assoc]
  exact hpull

end MarkedTriple

end Hironaka
