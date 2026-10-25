/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Global.StableOpenStatement
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.Limits.SpreadModification

/-!
# The closed fibre of a stable model has no contracted clopen subset

The input supplied by the consumer of `StableOpenNbhdConn` (ERRATA DJA-O36, node G4 of
`PLAN-T5.md`; Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
proof of Theorem 1.5, T:3384–3394). Let `W` be a valuation ring of finite height with
algebraically closed fraction field, `(C, D)` a curve over `W` in the situation of Temkin's §4.5
(`IsValuationCurve`), and `β : C' ⟶ C` a stable η-modification with `C'` projective over `W`. At a
geometric point `a` over the closed point `t` of `Spec W` which is algebraic over `κ(t)`:

* the closed fibre `(β ≫ φ)⁻¹(t)` is connected, by Zariski's connectedness theorem
  (`Cohomology.Connected.isConnected_fiber_of_isProjectiveOver`), since the generic fibre of `C'`
  is homeomorphic to that of `C`, an open subset of the integral scheme `C`
  (`isIrreducible_preimage_genericPoint`);
* `β` is surjective (`surjective_of_isEtaModification`), so it maps the closed fibre of `C'` onto
  that of `C`, which has at least two points when `C` comes from a curve of pure relative
  dimension one (`nontrivial_preimage_snd_of_hasPureFiberDimension`);
* the base change `X_a ⟶ X_t` of `Spec K ⟶ Spec κ(t)` is open, closed and surjective, so a
  nonempty clopen subset of `X_a` maps onto the connected `X_t`
  (`noContractedClopen_of_isConnected_fiber`); a contracted one would contract `X_t`.

Main statement: `noContractedClopen_of_isStableModification`.

Blueprint: `sm-global-stable-open.tex`, `lem:sm-gso-connected-fibre`,
`lem:sm-gso-stable-model-no-contracted-clopen`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap IsStableModification IsEtaModification fiberMap)

section Topology

variable {X C S : Scheme.{u}}

/-- **No contracted clopen subset from a connected fibre** (blueprint
`lem:sm-gso-connected-fibre`). Let `a = Spec ι ≫ (Spec κ(t) ⟶ S)` be a geometric point over
`t ∈ S` with `ι : κ(t) ⟶ K` integral. If the fibre `(β ≫ g)⁻¹(t)` is connected and its image
under `β` is not a subsingleton, then no nonempty clopen subset of `X_a` is contracted by `β_a`.
The base change `X_a ⟶ X_t` of `Spec K ⟶ Spec κ(t)` is open (a morphism to the spectrum of a
field is universally open), closed (`Spec ι` is integral) and surjective. -/
theorem noContractedClopen_of_isConnected_fiber (β : X ⟶ C) (g : C ⟶ S) (t : S) {K : Type u}
    [Field K] (ι : S.residueField t ⟶ .of K) (hι : ι.hom.IsIntegral)
    (hconn : _root_.IsConnected ((β ≫ g) ⁻¹' {t}))
    (himg : (β '' ((β ≫ g) ⁻¹' {t})).Nontrivial) :
    NoContractedClopen β g (Spec.map ι ≫ S.fromSpecResidueField t) := by
  let e := pullbackLeftPullbackSndIso (β ≫ g) (S.fromSpecResidueField t) (Spec.map ι)
  let π' : pullback (β ≫ g) (Spec.map ι ≫ S.fromSpecResidueField t) ⟶ (β ≫ g).fiber t :=
    e.inv ≫ pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)
  have : IsIntegralHom (Spec.map ι) := IsIntegralHom.SpecMap_iff.mpr hι
  have h0 : IsIntegralHom
      (pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)) :=
    inferInstance
  have h1 : UniversallyClosed
      (pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)) :=
    inferInstance
  have hc : UniversallyClosed π' :=
    MorphismProperty.comp_mem (W := @UniversallyClosed) _ _ inferInstance h1
  have h2 : UniversallyOpen
      (pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)) :=
    inferInstance
  have ho : UniversallyOpen π' :=
    MorphismProperty.comp_mem (W := @UniversallyOpen) _ _ inferInstance h2
  have : Surjective (Spec.map ι) :=
    ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have h3 : Surjective
      (pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)) :=
    inferInstance
  have hs : Function.Surjective π' := by
    intro x
    obtain ⟨y, rfl⟩ := h3.surj x
    refine ⟨e.hom y, ?_⟩
    have hy : e.inv (e.hom y) = y := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    change pullback.fst (pullback.snd (β ≫ g) (S.fromSpecResidueField t)) (Spec.map ι)
      (e.inv (e.hom y)) = _
    rw [hy]
  intro Z hZ hne hsub
  have hcl : IsClosedMap π' := π'.isClosedMap
  have hop : IsOpenMap π' := π'.isOpenMap
  have : ConnectedSpace ((β ≫ g).fiber t) := by
    have : ConnectedSpace (((β ≫ g) ⁻¹' {t} : Set X)) := isConnected_iff_connectedSpace.mp hconn
    exact ((β ≫ g).fiberHomeo t).symm.surjective.connectedSpace
      ((β ≫ g).fiberHomeo t).symm.continuous
  have huniv : π' '' Z = Set.univ :=
    IsClopen.eq_univ ⟨hcl _ hZ.1, hop _ hZ.2⟩ (hne.image _)
  have hfst : π' ≫ (β ≫ g).fiberι t =
      pullback.fst (β ≫ g) (Spec.map ι ≫ S.fromSpecResidueField t) := by
    change (e.inv ≫ pullback.fst _ (Spec.map ι)) ≫ pullback.fst (β ≫ g)
      (S.fromSpecResidueField t) = _
    rw [Category.assoc]
    exact pullbackLeftPullbackSndIso_inv_fst _ _ _
  apply himg.not_subsingleton
  have key : β '' ((β ≫ g) ⁻¹' {t}) =
      pullback.fst g (Spec.map ι ≫ S.fromSpecResidueField t) ''
        (pullbackCompMap β g (Spec.map ι ≫ S.fromSpecResidueField t) '' Z) := by
    rw [← (β ≫ g).range_fiberι t, ← Set.image_univ, ← huniv, Set.image_image, Set.image_image,
      Set.image_image]
    congr 1
    funext y
    rw [← Scheme.Hom.comp_apply π' ((β ≫ g).fiberι t), hfst, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, Curves.pullbackCompMap_fst]
  rw [key]
  exact hsub.image _

/-- **Curves of pure relative dimension one have nontrivial fibres**: if every irreducible
component of every fibre of `g` has dimension one, a nonempty fibre `g⁻¹(s)` has at least two
points (a one-point space has dimension zero). -/
theorem nontrivial_preimage_of_hasPureFiberDimension {g : C ⟶ S}
    (hdim : DeJong.HasPureFiberDimension g 1) {s : S} (hne : (g ⁻¹' {s}).Nonempty) :
    (g ⁻¹' {s}).Nontrivial := by
  by_contra hsub
  rw [Set.not_nontrivial_iff] at hsub
  have hss : Subsingleton (g.fiber s) := ⟨fun x y ↦ (g.fiberHomeo s).injective
    (Subtype.ext (hsub (g.fiberHomeo s x).2 (g.fiberHomeo s y).2))⟩
  obtain ⟨x, hx⟩ := hne
  let p : g.fiber s := (g.fiberHomeo s).symm ⟨x, hx⟩
  obtain ⟨Z, hZ, -⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {p} isIrreducible_singleton
  have h := hdim s Z hZ
  have : Subsingleton Z := Set.subsingleton_coe Z |>.mpr (Set.subsingleton_of_subsingleton)
  have h0 := topologicalKrullDim_zero_of_discreteTopology Z
  rw [h] at h0
  exact absurd h0 (by decide)

/-- **Base change of a curve of pure relative dimension one has nontrivial fibres**: for
`g : C ⟶ S` of pure relative dimension one and `ψ : T ⟶ S`, a nonempty fibre of
`C ×_S T ⟶ T` has at least two points (it maps onto the fibre of `g` over the image point). -/
theorem nontrivial_preimage_snd_of_hasPureFiberDimension {T : Scheme.{u}} {g : C ⟶ S}
    (hdim : DeJong.HasPureFiberDimension g 1) (ψ : T ⟶ S) {t : T}
    (hne : (pullback.snd g ψ ⁻¹' {t}).Nonempty) :
    (pullback.snd g ψ ⁻¹' {t}).Nontrivial := by
  obtain ⟨z, hz⟩ := hne
  have hne' : (g ⁻¹' {ψ t}).Nonempty := ⟨pullback.fst g ψ z, by
    change g (pullback.fst g ψ z) = ψ t
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg ψ hz⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, hne₁₂⟩ := nontrivial_preimage_of_hasPureFiberDimension hdim hne'
  obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := ψ) x₁ t hx₁
  obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := ψ) x₂ t hx₂
  refine ⟨z₁, hz₁', z₂, hz₂', fun h ↦ hne₁₂ ?_⟩
  rw [← hz₁, ← hz₂, h]

end Topology

section Valuation

variable {K : Type u} [Field K] {W : ValuationSubring K}
  {C C' : Scheme.{u}} {φ : C ⟶ Spec (.of W)} {D : C.IdealSheafData}

/-- The generic fibre of a curve over a valuation ring of finite height in the situation of
`IsValuationCurve` is irreducible: it is a nonempty open subset of the integral scheme `C` (the
generic point of `Spec W` is open, and flatness makes the fibre nonempty). -/
theorem isIrreducible_preimage_genericPoint [Finite (PrimeSpectrum W)] (hV : IsValuationCurve φ D) :
    IsIrreducible (φ ⁻¹' {genericPoint (Spec (.of W))}) := by
  have := hV.isIntegral
  have := hV.flat
  have : IsProper φ := hV.isProjectiveOver.isProper
  have hη : IsOpen ({genericPoint (Spec (.of W))} : Set (Spec (.of W))) :=
    Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (.of W)
  have hne : (φ ⁻¹' {genericPoint (Spec (.of W))}).Nonempty := by
    have h := Cohomology.Connected.nonempty_fiber_of_flat φ (genericPoint (Spec (.of W)))
    exact h
  exact ⟨hne, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset
    (hη.preimage φ.continuous) (Set.subset_univ _)⟩

/-- **η-modifications of an integral curve over `W` are surjective**: the image is closed
(`β` is proper) and contains the dense generic fibre of `C` (on which `β` is an isomorphism). -/
theorem surjective_of_isEtaModification [Finite (PrimeSpectrum W)] (hV : IsValuationCurve φ D)
    {β : C' ⟶ C} (hβ : IsEtaModification β φ) : Function.Surjective β := by
  have := hV.isIntegral
  have : IsProper β := hβ.toIsProper
  have := hβ.isIso_fiberMap
  set η := genericPoint (Spec (.of W))
  have hsub : φ ⁻¹' {η} ⊆ Set.range β := by
    intro y hy
    obtain ⟨w, rfl⟩ := (φ.range_fiberι η).ge hy
    obtain ⟨v, hv⟩ := (fiberMap β φ η).homeomorph.surjective w
    refine ⟨(β ≫ φ).fiberι η v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Curves.fiberMap_fiberι, Scheme.Hom.comp_apply]
    exact congrArg _ hv
  have hdense : Dense (φ ⁻¹' {η}) := by
    have hirr := isIrreducible_preimage_genericPoint hV
    have hη : IsOpen ({η} : Set (Spec (.of W))) :=
      Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (.of W)
    exact (hη.preimage φ.continuous).dense hirr.nonempty
  have hcl : IsClosed (Set.range β) := β.isClosedMap.isClosed_range
  intro y
  have : y ∈ closure (φ ⁻¹' {η}) := hdense.closure_eq ▸ Set.mem_univ y
  exact closure_minimal hsub hcl this

/-- **The generic fibre of an η-modification is irreducible**: it is homeomorphic (through the
isomorphism of generic fibres) to the generic fibre of `C`. -/
theorem isIrreducible_preimage_genericPoint_comp [Finite (PrimeSpectrum W)]
    (hV : IsValuationCurve φ D) {β : C' ⟶ C} (hβ : IsEtaModification β φ) :
    IsIrreducible ((β ≫ φ) ⁻¹' {genericPoint (Spec (.of W))}) := by
  have := hβ.isIso_fiberMap
  set η := genericPoint (Spec (.of W))
  have hirr := isIrreducible_preimage_genericPoint hV
  -- the generic fibre of `C` as a space is irreducible
  have : IrreducibleSpace (φ ⁻¹' {η} : Set C) := Subtype.irreducibleSpace hirr
  have h1 : IsIrreducible (Set.univ : Set (φ.fiber η)) := by
    have := (IrreducibleSpace.isIrreducible_univ (φ ⁻¹' {η} : Set C)).image
      (φ.fiberHomeo η).symm (φ.fiberHomeo η).symm.continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr (φ.fiberHomeo η).symm.surjective] at this
  -- hence so is the generic fibre of `C'`
  have h2 : IsIrreducible (Set.univ : Set ((β ≫ φ).fiber η)) := by
    have := h1.image (inv (fiberMap β φ η)) (inv (fiberMap β φ η)).continuous.continuousOn
    have hs : Function.Surjective (inv (fiberMap β φ η)) :=
      (inv (fiberMap β φ η)).homeomorph.surjective
    rwa [Set.image_univ, Set.range_eq_univ.mpr hs] at this
  have := h2.image ((β ≫ φ).fiberι η) ((β ≫ φ).fiberι η).continuous.continuousOn
  rwa [Set.image_univ, Scheme.Hom.range_fiberι] at this

/-- **The closed fibre of a stable model has no contracted clopen subset** (blueprint
`lem:sm-gso-stable-model-no-contracted-clopen`; ERRATA DJA-O36). Let `W` be a valuation ring of
finite height with algebraically closed fraction field, `(C, D)` a curve over `W` as in
`IsValuationCurve` whose closed fibre has at least two points, and `β : C' ⟶ C` a stable
η-modification with `C'` projective over `W`. At every geometric point
`Spec ι ≫ (Spec κ(t) ⟶ Spec W)` over the closed point `t`, with `ι` integral, no nonempty clopen
subset of the geometric fibre of `C'` is contracted by `β`: the closed fibre of `C'` is connected
(Zariski) and maps onto that of `C`. -/
theorem noContractedClopen_of_isStableModification [IsAlgClosed K] [Finite (PrimeSpectrum W)]
    (hV : IsValuationCurve φ D) {β : C' ⟶ C} {D' : C'.IdealSheafData}
    (hstab : IsStableModification β φ D D') (hproj : IsProjectiveOver (β ≫ φ))
    (hfib : (φ ⁻¹' {IsLocalRing.closedPoint W}).Nontrivial) {L : Type u} [Field L]
    (ι : (Spec (.of W)).residueField (IsLocalRing.closedPoint W) ⟶ .of L)
    (hι : ι.hom.IsIntegral) :
    NoContractedClopen β φ
      (Spec.map ι ≫ (Spec (.of W)).fromSpecResidueField (IsLocalRing.closedPoint W)) := by
  have : IsDomain W := inferInstance
  have hsurj := surjective_of_isEtaModification hV hstab.toIsEtaModification
  have : Flat (β ≫ φ) := hstab.isSemistablePair.nodal.toFlat
  have : Nonempty C' := by
    obtain ⟨y, -⟩ := hfib.nonempty
    obtain ⟨x, -⟩ := hsurj y
    exact ⟨x⟩
  have hsep : ∀ p : PrimeSpectrum W, IsSepClosed (FractionRing (W ⧸ p.asIdeal)) :=
    fun p ↦ Cohomology.Connected.isSepClosed_fractionRing_quotient K p
  have hgen : _root_.IsPreconnected ((β ≫ φ) ⁻¹' {(⊥ : PrimeSpectrum W)}) := by
    have h := isIrreducible_preimage_genericPoint_comp hV hstab.toIsEtaModification
    have hη : genericPoint (Spec (.of W)) = (⊥ : PrimeSpectrum W) :=
      genericPoint_eq_bot_of_affine (.of W)
    rw [hη] at h
    exact h.2.isPreconnected
  have hconn : _root_.IsConnected ((β ≫ φ) ⁻¹' {IsLocalRing.closedPoint W}) :=
    Cohomology.Connected.isConnected_fiber_of_isProjectiveOver hsep (β ≫ φ) hproj hgen _
  refine noContractedClopen_of_isConnected_fiber β φ (IsLocalRing.closedPoint W) ι hι hconn ?_
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hfib
  obtain ⟨x₁, rfl⟩ := hsurj y₁
  obtain ⟨x₂, rfl⟩ := hsurj y₂
  exact ⟨β x₁, ⟨x₁, hy₁, rfl⟩, β x₂, ⟨x₂, hy₂, rfl⟩, hne⟩

end Valuation

end DeJongAlterations.StableModification.Global
