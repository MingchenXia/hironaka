/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3D)
-/
import DeJongAlterations.StableModification.Projectivity.StableFibre
import DeJongAlterations.StableModification.Global.Setup
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.Global.MainModel
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Connected and projective geometric fibres of a locally projective stable modification

Temkin's T59 step (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), proof of Thm 1.1, T:1731–1737; ERRATA T59; PLAN-OM3 §8 G3) needs that a connected
component of a geometric fibre `C'_ā` of `C' → S'` cannot be contracted by the stable
modification `β : C' ⟶ T = C ×_S S'`. We obtain the connectedness of suitable geometric fibres
from a valuation ring: for a point `y ∈ T` we choose a valuation ring `W` of an algebraic closure
`L` of the function field of `T` whose closed point is sent to `y` (the center map of the
Riemann–Zariski space is surjective, `exists_extension_specClosedPoint`), base change `β` to
`Spec W`, and

* apply lane OM3C's projectivity over valuation rings (`ValuationProjectivity`): the base change
  `C'_W` is projective over `W`;
* apply lane COH3C's connectedness theorem (`Cohomology.Connected.isConnected_fiber_of_isProjectiveOver`):
  the closed fibre of `C'_W → Spec W` is connected, because the generic fibre is (it is the base
  change of the geometrically integral generic fibre of `C' → S'`).

The geometric point is `ā : Spec κ(W) ⟶ Spec W ⟶ T`, which lies over `y`, and `C'_ā` is the
closed fibre (`exists_geometricPoint_connected`).

**Remark (PLAN-OM3 §8 G3).** The plan derives the projectivity of `C'_W` from "local projectivity
and Segre"; local projectivity of `β` over an open cover of `T` does not give it (the cover is
not pulled back from `S'`). Lane OM3C's `thm:sm-val-proj` is what gives it.

Blueprint: `sm-projectivity-stable.tex`, `lem:sm-tsm-valuation-centre`,
`lem:sm-tsm-connected-fibre`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

open RiemannZariskiSpace

section Centre

variable {Y : Scheme.{u}} [IsIntegral Y] {L : Type u} [Field L] [Algebra Y.functionField L]

/-- **Every point is a centre**: for an integral scheme `Y`, a field `L ⊇ K(Y)` and `y ∈ Y` there
is a valuation ring `W` of `L` and an extension `φ : Spec W ⟶ Y` of the generic point
`Spec L ⟶ Y` sending the closed point of `Spec W` to `y` (the center map of the Riemann–Zariski
space of an affine neighbourhood of `y` is surjective). -/
theorem exists_extension_specClosedPoint (y : Y) :
    ∃ (W : RiemannZariskiSpace L) (φ : Spec (.of W.valuationSubring) ⟶ Y),
      toSpecValuationSubring W ≫ φ = functionFieldPoint Y L ∧ φ (specClosedPoint W) = y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hgU : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hyU⟩
  have hηU := functionFieldPoint_preimage (L := L) hU hgU
  let g := sectionsToField (functionFieldPoint Y L) U hηU
  have hg : Function.Injective g := injective_sectionsToField_functionFieldPoint hU hgU
  let _ : Algebra Γ(Y, U) L := g.toAlgebra
  obtain ⟨V, hV⟩ := center_surjective (A := Γ(Y, U)) (L := L) hg (hU.primeIdealOf ⟨y, hyU⟩)
  have hVmem : V.1 ∈ ofRingHom g := V.2
  refine ⟨V.1, extensionOfMem _ hU hηU V.1 hVmem,
    toSpecValuationSubring_comp_extensionOfMem hU hηU V.1 hVmem, ?_⟩
  have h1 : (Spec.map (CommRingCat.ofHom (g.codRestrict V.1.valuationSubring
      (mem_ofRingHom.1 hVmem)))) (specClosedPoint V.1) = center V := rfl
  change (Spec.map (CommRingCat.ofHom (g.codRestrict V.1.valuationSubring
      (mem_ofRingHom.1 hVmem))) ≫ hU.fromSpec) (specClosedPoint V.1) = y
  rw [Scheme.Hom.comp_apply, h1, hV]
  exact hU.fromSpec_primeIdealOf ⟨y, hyU⟩

end Centre

section Topology

/-- Preconnectedness passes to the image of a continuous surjection. -/
theorem preconnectedSpace_of_surjective {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [PreconnectedSpace α] {f : α → β} (hf : Continuous f) (hs : Function.Surjective f) :
    PreconnectedSpace β :=
  ⟨by simpa [hs.range_eq] using isPreconnected_range hf⟩

end Topology

section Geometric

variable {k : Type u} [Field k] {S' Y X : Scheme.{u}} [IsIntegral S'] [IsIntegral Y]
  (pS' : S' ⟶ Spec (.of k)) (q : Y ⟶ S') [Flat q] [LocallyOfFinitePresentation q]
  [LocallyOfFiniteType (q ≫ pS')] (hq : DeJong.IsRelativelyProjective pS' q)
  (hqgen : q (genericPoint Y) = genericPoint S') (β : X ⟶ Y) [DeJong.IsNodalCurve (β ≫ q)]
  (hsm : Smooth ((β ≫ q).fiberToSpecResidueField (genericPoint S')))
  (hgi : GeometricallyIntegral ((β ≫ q).fiberToSpecResidueField (genericPoint S')))
  (hloc : LocallyRelativelyProjective (q ≫ pS') β)

include hq hqgen hsm hgi hloc in
/-- **Connected projective geometric fibres** (Temkin's T59 step, PLAN-OM3 §8 G3, corrected).
Let `q : Y ⟶ S'` be flat, finitely presented and projective relative to `pS' : S' ⟶ Spec k`
between integral schemes, sending the generic point to the generic point, and `β : X ⟶ Y`
locally relatively projective over `q ≫ pS'` with `β ≫ q` a nodal curve whose generic fibre is
smooth and geometrically integral. Granting lane OM3C's projectivity over valuation rings, every
point `y ∈ Y` has a geometric point `ā : Spec K ⟶ Y` over it (`K` algebraically closed) such that
the geometric fibre `X_ā = X ×_{S'} Spec K` of `β ≫ q` is projective over `K` and connected. -/
theorem exists_geometricPoint_connected (hVal : ValuationProjectivity.{u}) (y : Y) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (ā : Spec (.of K) ⟶ Y), (∀ z, ā z = y) ∧
      IsProjectiveOver (pullback.snd (β ≫ q) (ā ≫ q)) ∧
      PreconnectedSpace (pullback (C := Scheme.{u}) (β ≫ q) (ā ≫ q)) := by
  let L := AlgebraicClosure Y.functionField
  obtain ⟨W, φ, hφ, hφc⟩ := exists_extension_specClosedPoint (L := L) y
  have : Finite (PrimeSpectrum W.valuationSubring) :=
    Global.finite_primeSpectrum_of_mem (pS := q ≫ pS') W ⟨φ, hφ⟩
  have hres : ∀ t : PrimeSpectrum W.valuationSubring, IsAlgClosed t.asIdeal.ResidueField :=
    fun t => BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed L t
  have hsep : ∀ t : PrimeSpectrum W.valuationSubring,
      IsSepClosed (FractionRing (W.valuationSubring ⧸ t.asIdeal)) :=
    fun t => Cohomology.Connected.isSepClosed_fractionRing_quotient L t
  set a : Spec (.of W.valuationSubring) ⟶ S' := φ ≫ q with ha
  have hφη : φ (genericPoint (Spec (.of W.valuationSubring))) = genericPoint Y :=
    Global.apply_genericPoint_of_extension W φ hφ
  have hη : a (genericPoint (Spec (.of W.valuationSubring))) = genericPoint S' := by
    rw [ha, Scheme.Hom.comp_apply, hφη, hqgen]
  -- the base change of `Y` is projective over `W`
  have hYW : IsProjectiveOver (pullback.snd q a) := by
    have h2 := hq.pullback_snd a
    have e : a ≫ pS' = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Spec.preimage (a ≫ pS')).hom) := by
      simp
    rw [e, isRelativelyProjective_comp_specMap_iff] at h2
    exact (DeJong.isRelativelyProjective_id_iff _).mp h2
  -- local projectivity is inherited
  have hlocW : LocallyRelativelyProjective (pullback.snd q a) (Curves.pullbackCompMap β q a) := by
    have h1 := Global.locallyRelativelyProjective_of_isPullback hloc
      (Limits.SpreadModification.isPullback_pullbackCompMap β q a)
    rw [pullback.condition_assoc] at h1
    have e : a ≫ pS' = Spec.map (CommRingCat.ofHom (Spec.preimage (a ≫ pS')).hom) := by simp
    rw [e, locallyRelativelyProjective_comp_specMap_iff] at h1
    exact h1
  have hnod : DeJong.IsNodalCurve (Curves.pullbackCompMap β q a ≫ pullback.snd q a) := by
    rw [Curves.pullbackCompMap_snd]
    infer_instance
  have hgen : ∀ x, (Curves.pullbackCompMap β q a ≫ pullback.snd q a) x =
      genericPoint (Spec (.of W.valuationSubring)) →
      DeJong.IsSmoothAt (Curves.pullbackCompMap β q a ≫ pullback.snd q a) x := by
    rw [Curves.pullbackCompMap_snd]
    intro x hx
    exact Global.isSmoothAt_of_smooth_fiber _ _
      (Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite _)
      (Field.toIsField (Spec (.of W.valuationSubring)).functionField)
      (Global.smooth_fiber_pullback_snd (β ≫ q) hsm a hη) x hx
  have hrel := hVal W.valuationSubring hres (pullback.snd q a) hYW inferInstance inferInstance _
    hnod hgen hlocW
  set F := pullback.snd (β ≫ q) a with hF
  have hFproj : IsProjectiveOver F := by
    have := hrel.isProjectiveOver hYW
    rwa [Curves.pullbackCompMap_snd] at this
  -- the geometric point over the closed point of `Spec W`
  set c : Spec (.of W.valuationSubring) := IsLocalRing.closedPoint W.valuationSubring
  have hK : IsAlgClosed ((Spec (.of W.valuationSubring)).residueField c) := by
    have := hres c
    exact IsAlgClosed.of_ringEquiv _ _
      (Scheme.Spec.residueFieldIso (.of W.valuationSubring) c).commRingCatIsoToRingEquiv.symm
  let i := (Spec (.of W.valuationSubring)).fromSpecResidueField c
  have hia : (i ≫ φ) ≫ q = i ≫ a := Category.assoc _ _ _
  let e := pullbackLeftPullbackSndIso (β ≫ q) a i
  refine ⟨(Spec (.of W.valuationSubring)).residueField c, inferInstance, hK, i ≫ φ, ?_, ?_, ?_⟩
  · intro z
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hφc
  · rw [hia]
    have h1 := ((DeJong.isRelativelyProjective_id_iff F).mpr hFproj).pullback_snd i
    have e' : i ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Spec.preimage i).hom) := by simp
    rw [e', isRelativelyProjective_comp_specMap_iff] at h1
    have h2 := (DeJong.isRelativelyProjective_id_iff _).mp h1
    have h3 := DeJong.IsProjectiveOver.comp_isClosedImmersion h2 e.inv
    rwa [pullbackLeftPullbackSndIso_inv_snd_snd] at h3
  · rw [hia]
    -- the closed fibre of `F` is connected
    by_cases hne : Nonempty (pullback (C := Scheme.{u}) (β ≫ q) a)
    · have hgenc : _root_.IsPreconnected (F ⁻¹' {(⊥ : PrimeSpectrum W.valuationSubring)}) := by
        have hη' : a (⊥ : PrimeSpectrum W.valuationSubring) = genericPoint S' := by
          exact (congrArg a (genericPoint_eq_bot_of_affine
            (CommRingCat.of W.valuationSubring)).symm).trans hη
        rw [← hη'] at hgi
        have : IsIntegral (F.fiber (⊥ : PrimeSpectrum W.valuationSubring)) :=
          hgi.geometrically_isIntegral _ _ _
            (Global.isPullback_fiber_pullback_snd (β ≫ q) a (⊥ : PrimeSpectrum W.valuationSubring))
        have h := isPreconnected_range (F.fiberι (⊥ : PrimeSpectrum W.valuationSubring)).continuous
        have h2 := Scheme.Hom.range_fiberι F (⊥ : PrimeSpectrum W.valuationSubring)
        rw [h2] at h
        exact h
      have hconn := Cohomology.Connected.isConnected_fiber_of_isProjectiveOver hsep F hFproj
        hgenc c
      have : PreconnectedSpace (F ⁻¹' {c}) := Subtype.preconnectedSpace hconn.isPreconnected
      have : PreconnectedSpace (pullback (C := Scheme.{u}) F i) :=
        preconnectedSpace_of_surjective (F.fiberHomeo c).symm.continuous
          (F.fiberHomeo c).symm.surjective
      exact preconnectedSpace_of_surjective (Scheme.homeoOfIso e).continuous
        (Scheme.homeoOfIso e).surjective
    · have : IsEmpty (pullback (C := Scheme.{u}) (β ≫ q) (i ≫ a)) := by
        refine ⟨fun x => hne ⟨(e.inv ≫ pullback.fst F i) x⟩⟩
      exact ⟨by rw [Set.univ_eq_empty_iff.mpr this]; exact isPreconnected_empty⟩

end Geometric

end

end DeJongAlterations.StableModification.Projectivity
