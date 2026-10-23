/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.Gluing.Setup
import DeJongAlterations.StableModification.Gluing.ExtensionAssembly
import DeJongAlterations.StableModification.LocalUniformization.GlobalNormal
import DeJongAlterations.StableModification.BlowDown.NoClosedExc
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeightClosure
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.BlowDown.ContractionStein
import DeJongAlterations.StableModification.BlowDown.ContractionDimension
import DeJongAlterations.StableModification.Limits.SpreadModification
import DeJongAlterations.Geometry.NormalCurveModification

/-!
# A nodal modification of a curve over a valuation ring (PLAN-T5 §2.2 steps 1–8)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.5.1 (`sepclosprop`, T:3243–3266). This file chains the nodes of `PLAN-T5.md` §2.2
(lane T45A): the projective refinement `C' → C` with its pieces (`Gluing.exists_projective_refinement`,
A1–A3), projective strictly semi-stable models of the pieces (node A4, **taken as the hypothesis
`ProjectiveCofinality R`**), the normalization `N = Nor(C')` (A5) and the insertion of the local
models into `N` (A6–A8, `Gluing.exists_nodal_modification_normalization`).

## Main results

* `apply_genericPoint_eq_bot_of_flat`, `flat_of_apply_genericPoint_eq_bot`,
  `locallyOfFinitePresentation_of_flat`: an integral scheme dominating `Spec V`, `V` a valuation
  ring, is flat over `V`, hence of finite presentation if of finite type (Temkin, Lemma 3.5.1).
* `isLocallyNoetherian_genericOpen`, `isEtaModification_of_isNodalCurve`: a modification of a
  relative curve with normal generic fibre by a nodal curve is an η-modification.
* `ProjectiveCofinality R`: the statement of node A4 (not proved here).
* `exists_nodal_modification`: **under `ProjectiveCofinality R`, every proper flat integral
  relative curve over a valuation ring `R` of finite height and equal characteristic with
  algebraically closed fraction field has a modification `X → C` with `X` nodal over `R`**,
  factoring through the finite normalization `N` of a projective refinement, `N` flat, of finite
  presentation, and projective over `R` if `C` is.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace DeJongAlterations.StableModification.Gluing

open ValCurves Curves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open DeJong (IsNodalCurve)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Flat

variable {V : Type u} [CommRing V] [IsDomain V]

/-- A flat morphism from an integral scheme to `Spec V`, `V` a domain, maps the generic point to
the generic point `⊥` (flat morphisms are generalizing). -/
theorem apply_genericPoint_eq_bot_of_flat {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of V)) [Flat g] : g (genericPoint X) = (⊥ : PrimeSpectrum V) := by
  have hsp : (⊥ : PrimeSpectrum V) ⤳ g (genericPoint X) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨x', hx', hgx'⟩ := Flat.generalizingMap g hsp
  have : x' = genericPoint X :=
    (hx'.antisymm ((genericPoint_spec X).specializes (Set.mem_univ x'))).eq
  rw [← this, hgx']

variable [ValuationRing V]

/-- **An integral scheme dominating `Spec V` is flat** over a valuation ring `V` (lane COH's
`flat_of_dense_preimage_bot`): its generic point lies over the generic point of `Spec V`. -/
theorem flat_of_apply_genericPoint_eq_bot {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of V)) (hg : g (genericPoint X) = (⊥ : PrimeSpectrum V)) : Flat g := by
  refine Cohomology.ConnectedBirationalHeight.flat_of_dense_preimage_bot g ?_
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← hcl]
  exact closure_mono (Set.singleton_subset_iff.mpr hg)

/-- **Flat and locally of finite type over a valuation ring implies locally of finite
presentation** (Temkin, Lemma 3.5.1, `ValuationRing.finitePresentation_of_finiteType_of_flat`). -/
theorem locallyOfFinitePresentation_of_flat {X : Scheme.{u}} (g : X ⟶ Spec (.of V)) [Flat g]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have e : U ≤ g ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top]
    exact le_top
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hU⟩, hxU, e, ?_⟩
  change (g.appLE ⊤ U e).hom.FinitePresentation
  have hft : (g.appLE ⊤ U e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have hfl : (g.appLE ⊤ U e).hom.Flat :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  let ψ : V →+* Γ(X, U) := (g.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (.of V)).inv.hom
  have hψ : (g.appLE ⊤ U e).hom = ψ.comp (Scheme.ΓSpecIso (.of V)).hom.hom := by
    ext a
    change _ = (g.appLE ⊤ U e) (((Scheme.ΓSpecIso (.of V)).hom ≫ (Scheme.ΓSpecIso (.of V)).inv) a)
    rw [Iso.hom_inv_id, CommRingCat.id_apply]
  have hψft : ψ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2)
  have hψfl : ψ.Flat := RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)) hfl
  let := ψ.toAlgebra
  have : Algebra.FiniteType V Γ(X, U) := hψft
  have : Module.Flat V Γ(X, U) := hψfl
  have hψfp : ψ.FinitePresentation := ValuationRing.finitePresentation_of_finiteType_of_flat
  rw [hψ]
  exact RingHom.finitePresentation_stableUnderComposition _ _
    (RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).hom)) hψfp

end Flat

section Eta

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C X : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of V))

/-- The generic open of `Spec V` is a locally Noetherian scheme (it is the spectrum of a field). -/
theorem isLocallyNoetherian_genericOpen :
    IsLocallyNoetherian (BlowDown.genericOpen V).toScheme := by
  let η := genericPoint (Spec (.of V))
  have hfield : IsField ((Spec (.of V)).presheaf.stalk η) :=
    isField_stalk_of_closure_mem_irreducibleComponents (Spec (.of V)) η (by
      rw [(genericPoint_spec (Spec (.of V))).def, irreducibleComponents_eq_singleton]
      exact Set.mem_singleton _)
  have := Limits.SpreadModification.isOpenImmersion_fromSpecResidueField η
    (Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (.of V)) hfield
  let e := IsOpenImmersion.isoOfRangeEq ((Spec (.of V)).fromSpecResidueField η)
    (BlowDown.genericOpen V).ι (by
      rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, BlowDown.coe_genericOpen])
  exact isLocallyNoetherian_of_isOpenImmersion e.inv

variable [Flat φ] [LocallyOfFiniteType φ]

/-- **Modifications by nodal curves are η-modifications** when the generic fibre is normal
(`PLAN-T5.md` §2.2 step 8, the η-modification part of node A8). Let `V` be a valuation ring of
finite height and `φ : C → Spec V` flat, locally of finite type, with `C` integral and normal at
the points over the generic point. If `β : X → C` is a modification with `X` nodal over `V`, then
`β` is an isomorphism over the generic fibre `C_η` (Codex's
`Geometry.NormalCurveModification.isIso_of_isModification`: `C_η` is a normal locally Noetherian
curve, of dimension at most one as the image of the nodal `X_η`), i.e. an η-modification. -/
theorem isEtaModification_of_isNodalCurve
    (hnorm : ∀ x : C, φ x = genericPoint (Spec (.of V)) →
      IsIntegrallyClosed (C.presheaf.stalk x))
    (β : X ⟶ C) [IsModification β] [IsNodalCurve (β ≫ φ)] : Curves.IsEtaModification β φ := by
  have hβ : IsModification β := inferInstance
  have := hβ.sourceIntegral
  set U := φ ⁻¹ᵁ BlowDown.genericOpen V
  have hgen : φ (genericPoint C) = genericPoint (Spec (.of V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact apply_genericPoint_eq_bot_of_flat φ
  have hξU : genericPoint C ∈ U := hgen
  have : Nonempty U := ⟨⟨_, hξU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  -- `C_η` is normal
  have hUn : IsNormalScheme U.toScheme := by
    intro y
    have hy : φ (U.ι y) = genericPoint (Spec (.of V)) := y.2
    have : IsIntegrallyClosed (C.presheaf.stalk (U.ι y)) := hnorm _ hy
    let e := asIso (U.ι.stalkMap y)
    exact ⟨e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain,
      IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv⟩
  -- `C_η` is locally Noetherian
  have := isLocallyNoetherian_genericOpen (V := V)
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (φ ∣_ _)
  -- `C_η` has dimension at most one
  have : Surjective β := ⟨(surjective_of_isDominant_of_isClosed_range β
    β.isClosedMap.isClosed_range).surj⟩
  have hdimF := BlowDown.topologicalKrullDim_fiber_le_one_of_isNodalCurve_comp φ β
    (genericPoint (Spec (.of V)))
  have hset : (U : Set C) = φ ⁻¹' {genericPoint (Spec (.of V))} := by
    change φ ⁻¹' (BlowDown.genericOpen V : Set (Spec (.of V))) = _
    rw [BlowDown.coe_genericOpen]
  let h₁ : U.toScheme ≃ₜ φ.fiber (genericPoint (Spec (.of V))) :=
    (Homeomorph.setCongr hset).trans (φ.fiberHomeo _).symm
  have hdim : topologicalKrullDim U.toScheme ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq h₁ h₁.isHomeomorph]
    exact hdimF
  -- `β` is an isomorphism over `C_η`
  have := Geometry.CurveCompactification.isModification_morphismRestrict β U
  have : IsIso (β ∣_ U) := Geometry.NormalCurveModification.isIso_of_isModification _ hUn hdim
  exact Limits.SpreadModification.isEtaModification_of_isIso_morphismRestrict β φ
    (BlowDown.genericOpen V) ⟨_, rfl⟩

end Eta

section Assembly

variable {K : Type u} [Field K] (R : ValuationSubring K)

/-- **Projective cofinality** (`PLAN-T5.md` §2.2 step 4, node A4; Temkin, Proposition 4.3.1 with
the projectivity of the output tracked): every modification `h : W → T` of an affine integral
strictly semi-stable relative curve `ψ : T = Spec E → Spec R` is dominated by a strictly
semi-stable modification `f : B → T` which is projective over `T` (relative to `ψ`). This is **not
proved** in lane T45A (it needs SERRE-I, lane OM3C); it is the explicit hypothesis of
`exists_nodal_modification`. Without the projectivity of `f` it is
`Gluing.exists_dominates_isStrictlySemistable_of_isModification`. -/
def ProjectiveCofinality : Prop :=
  ∀ (E : Type u) [CommRing E] [IsDomain E] (ψ : Spec (.of E) ⟶ Spec (.of R)),
    IsStrictlySemistable ψ ⊤ → fiberTrdeg ψ (genericPoint (Spec (.of E))) = 1 →
    ∀ {W : Scheme.{u}} (h : W ⟶ Spec (.of E)), IsModification h →
      ∃ (B : Scheme.{u}) (_ : IsIntegral B) (f : B ⟶ Spec (.of E)) (_ : IsModification f),
        IsStrictlySemistable (f ≫ ψ) ⊤ ∧ DeJong.IsRelativelyProjective ψ f ∧
          ∃ q : B ⟶ W, q ≫ h = f

variable {R}

/-- **A semi-stable modification of a curve over a valuation ring** (`PLAN-T5.md` §2.2 steps 1–8,
nodes A1–A8, with node A4 as the hypothesis `ProjectiveCofinality R`; Temkin, proof of
Proposition 4.5.1, T:3243–3266). Let `K` be algebraically closed, `R ⊆ K` a valuation ring of
finite height and equal characteristic, and `φ : C → Spec R` a proper flat relative curve,
integral, with `trdeg K(C)/K = 1`. Then there are

* the projective refinement `p : C' → C` (a modification, projective relative to `φ`), whose
  normalization `ν : N = Nor(C') → C'` is finite, with `N` flat and of finite presentation over
  `R`, and projective over `R` if `C` is;
* a modification `β : X → N` with `X → C` a modification and `X` a **nodal curve over `R`**,
  locally projective over `N` (`Projectivity.LocallyRelativelyProjective`, the input `hloc` of
  OM3C's valuation-level projectivity theorem, PLAN-T5 V1), and an η-modification of `C` if `C`
  is normal along its generic fibre (e.g. smooth there).

The `X` is obtained by inserting the projective strictly semi-stable models of the pieces of the
refinement into `N` around its finitely many non-nodal points (`exists_nodal_modification_normalization`). -/
theorem exists_nodal_modification [IsAlgClosed K] [Finite (PrimeSpectrum R)]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p) (hA4 : ProjectiveCofinality R)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R))
    [IsProper φ] [Flat φ] (htr : fiberTrdeg φ (genericPoint C) = 1) :
    ∃ (C' : Scheme.{u}) (p : C' ⟶ C) (_ : IsIntegral C'), IsModification p ∧
      DeJong.IsRelativelyProjective φ p ∧ IsFinite (genericPt C').fromNormalization ∧
      Flat ((genericPt C').fromNormalization ≫ p ≫ φ) ∧
      LocallyOfFinitePresentation ((genericPt C').fromNormalization ≫ p ≫ φ) ∧
      (IsProjectiveOver φ → IsProjectiveOver ((genericPt C').fromNormalization ≫ p ≫ φ)) ∧
      ∃ (X : Scheme.{u}) (β : X ⟶ (genericPt C').normalization), IsModification β ∧
        IsModification (β ≫ (genericPt C').fromNormalization ≫ p) ∧
        IsNodalCurve (β ≫ (genericPt C').fromNormalization ≫ p ≫ φ) ∧
        Projectivity.LocallyRelativelyProjective ((genericPt C').fromNormalization ≫ p ≫ φ) β ∧
        ((∀ x : C, φ x = genericPoint (Spec (.of R)) → IsIntegrallyClosed (C.presheaf.stalk x)) →
          Curves.IsEtaModification (β ≫ (genericPt C').fromNormalization ≫ p) φ) := by
  obtain ⟨C', p, hp, hpproj, ι, hι, E, _, _, g, W, h, hW, hpieces⟩ :=
    exists_projective_refinement hchar φ htr
  have := hp
  have := hp.sourceIntegral
  -- the projective strictly semi-stable models of the pieces (node A4)
  have hmodels : ∀ i, ∃ (B : Scheme.{u}) (_ : IsIntegral B) (f : B ⟶ Spec (.of (E i)))
      (_ : IsModification f), IsStrictlySemistable (f ≫ g i ≫ φ) ⊤ ∧
        DeJong.IsRelativelyProjective (g i ≫ φ) f ∧ ∃ q : B ⟶ (W i).toScheme, q ≫ h i = f := by
    intro i
    obtain ⟨hss, htri, -, hhm, -⟩ := hpieces i
    exact hA4 (E i) (g i ≫ φ) hss htri (h i) hhm
  choose B hBi f hfm hfss hfproj q hq using hmodels
  have hhm : ∀ i, IsModification (h i) := fun i ↦ (hpieces i).2.2.2.1
  have hhg : ∀ i, h i ≫ g i = (W i).ι ≫ p := fun i ↦ (hpieces i).2.2.1
  -- the models `qᵢ : Bᵢ → Wᵢ`
  have hqm : ∀ i, IsModification (q i) := by
    intro i
    have := hhm i
    have := hfm i
    have : IsModification (q i ≫ h i) := by rw [hq i]; infer_instance
    exact isModification_of_comp (q i) (h i)
  have hcomp : ∀ i, q i ≫ (W i).ι ≫ p ≫ φ = f i ≫ g i ≫ φ := fun i ↦ by
    rw [← Category.assoc (W i).ι, ← hhg i, Category.assoc, ← Category.assoc (q i), hq i]
  have hqnod : ∀ i, IsNodalCurve (q i ≫ (W i).ι ≫ p ≫ φ) := fun i ↦ by
    rw [hcomp i]
    exact (hfss i).isNodalCurve
  have hqflat : ∀ i, Flat (q i ≫ (W i).ι ≫ p ≫ φ) := fun i ↦ (hqnod i).toFlat
  have hqproj : ∀ i, DeJong.IsRelativelyProjective ((W i).ι ≫ p ≫ φ) (q i) := by
    intro i
    have := hhm i
    have h1 := BlowDown.NoClosedExc.isRelativelyProjective_of_comp (g i ≫ φ) (q i) (h i)
      (by rw [hq i]; exact hfproj i)
    rwa [← Category.assoc, hhg i, Category.assoc] at h1
  have hqnorm : ∀ i, IsNormalScheme (B i) := fun i ↦
    LocalUniformization.isNormalScheme_of_isStrictlySemistable (isNormalScheme_spec R) (hfss i)
  -- `C'` over `R`
  have : IsProper p := hp.toIsProper
  have hgen : (p ≫ φ) (genericPoint C') = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, Geometry.NormalCurveModification.genericPoint_map p hp.birational]
    exact apply_genericPoint_eq_bot_of_flat φ
  have : Flat (p ≫ φ) := flat_of_apply_genericPoint_eq_bot (p ≫ φ) hgen
  have : LocallyOfFinitePresentation (p ≫ φ) := locallyOfFinitePresentation_of_flat (p ≫ φ)
  have hdim : fiberTrdeg (p ≫ φ) (genericPoint C') ≤ 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint φ p, htr]
  have hsep : ∀ P : PrimeSpectrum R, IsSepClosed (FractionRing (R ⧸ P.asIdeal)) :=
    fun P ↦ Cohomology.Connected.isSepClosed_fractionRing_quotient K P
  -- nodes A5–A8
  obtain ⟨hfin, X, β, hβ, hβν, hnod, hlrp, -⟩ :=
    exists_nodal_modification_normalization hsep (p ≫ φ) hdim hW q hqnorm hqflat hqproj hqnod
  have hmod : IsModification (β ≫ (genericPt C').fromNormalization ≫ p) := by
    rw [← Category.assoc]
    exact IsModification.comp _ p
  refine ⟨C', p, inferInstance, hp, hpproj, hfin,
    flat_fromNormalization_genericPt q (p ≫ φ) hW hqnorm hqflat hqproj,
    locallyOfFinitePresentation_fromNormalization_genericPt q (p ≫ φ) hW hqnorm hqflat hqproj,
    fun hφ ↦ isProjectiveOver_fromNormalization_genericPt (p ≫ φ)
      (DeJong.IsRelativelyProjective.isProjectiveOver hφ hpproj), X, β, hβ, hmod, hnod, hlrp,
      fun hnorm ↦ ?_⟩
  have : IsNodalCurve ((β ≫ (genericPt C').fromNormalization ≫ p) ≫ φ) := by
    simp only [Category.assoc]
    exact hnod
  exact isEtaModification_of_isNodalCurve φ hnorm _

end Assembly

end DeJongAlterations.StableModification.Gluing
