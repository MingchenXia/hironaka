import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness

/-!
# Glued steps with prescribed ambient blowups (goal G11, route step 5)

`HironakaG11WindowTowers.ManifoldSmoothCentres.exists_singularCentreBlowup_windows` chooses the
blowups of the window ambients itself. To follow GIVEN ambient towers (e.g. the simultaneous
canonical towers of `HironakaG11CompatibleCanonicalTowers`), the step must accept prescribed blowups
`π i` of the window ambients along the local centres: **`exists_singularCentreBlowup_given_blowups`**
gives the global singular-centre blowup and, for these `π i`, the open immersions of the strict
transforms of the window carriers with the squares and ranges. No named proposition; nothing proves
or assumes G11. Blueprint: `hironaka-g11-resume-lift-uniqueness.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11GluedWindowSteps

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
  HironakaG11SingularCentreModification HironakaG11CompatibleAnalyticCover
  HironakaG11ManifoldWindowCentres HironakaG11BlowupLocality HironakaG11GluedCentreIteration
  HironakaG11WindowTowers BlowupTowers EmbeddedBlowup

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type*} (F : ManifoldSmoothCentres X ι)

/-- **One global singular-centre blowup, with prescribed blowups of the window ambients.** For a
compatible family of smooth centres on manifold windows with closed glued centre in the singular
locus and ANY blowups `π i : Z i → M i` of the window ambients along the local centres, there are
a global singular-centre blowup `p : Y ⟶ X` along the glued centre and open immersions `L i` of the
strict transforms of the window carriers into `Y` with
`L i ≫ p = (strict transform projection) ≫ (window i)` and range the preimage of the window. -/
theorem exists_singularCentreBlowup_given_blowups (hc : F.Compatible) (hcl : IsClosed F.support)
    (hsing : F.support ⊆ intrinsicSingularLocus X.obj) (Z : ∀ i, CMfd.{0} (F.dim i))
    (π : ∀ i, Z i → F.ambient i) (hπ : ∀ i, IsBlowupAlong (F.dim i) (F.centre i) (π i)) :
    ∃ (hS : X.IsAnalyticSubset F.support) (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion X F.support hS) ∧
      IsSingularCentreStep p ∧ IsSingularCentreModification p ∧
      Function.Surjective p.hom.left.base ∧ IsIsoOver p F.supportᶜ ∧
      ∃ L : ∀ i, ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            (hπ i) (F.analytic i)) ⟶ Y,
        ∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
          L i ≫ p = strictTransformMorphism (hπ i) (F.analytic i) ≫ F.map i ∧
          range (L i).hom.left.base = p.hom.left.base ⁻¹' range (F.map i).hom.left.base := by
  obtain ⟨hS, Y, p, hblow, hstep, hmod, hsurj, hiso⟩ := F.exists_singularCentreBlowup hc hcl hsing
  refine ⟨hS, Y, p, hblow, hstep, hmod, hsurj, hiso, ?_⟩
  have hrange := OriginalAnalyticClosedSubspace.inclusion_range X F.support hS
  have hloc : ∀ i, ∃ L : ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        (hπ i) (F.analytic i)) ⟶ Y,
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
        L ≫ p = strictTransformMorphism (hπ i) (F.analytic i) ≫ F.map i ∧
        range L.hom.left.base = p.hom.left.base ⁻¹' range (F.map i).hom.left.base := by
    intro i
    have hW := strictTransformMorphism_isIdealBlowup (hπ i) (F.analytic i) (F.centre_subset i)
      (ManifoldSmoothCentres.carrier_subset_closure_diff F hsing i)
    have htr : (F.map i).hom.left.base ⁻¹'
        range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base =
          (Subtype.val : F.carrier i → F.ambient i) ⁻¹' F.centre i := by
      rw [hrange]
      exact F.preimage_support hc i
    have hW' : IsIdealBlowup (strictTransformMorphism (hπ i) (F.analytic i))
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealModule
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left ((F.map i).hom.left.base ⁻¹'
            range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base))
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealInclusion
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left ((F.map i).hom.left.base ⁻¹'
            range (OriginalAnalyticClosedSubspace.inclusion X F.support hS).hom.left.base)) := by
      rw [htr]
      exact hW
    obtain ⟨L, ⟨hL, -⟩, hLo, hLr⟩ :=
      exists_openImmersion_of_isSmoothCentreBlowup hblow (F.isOpenImmersion i) hW'
    exact ⟨L, hLo, hL, hLr⟩
  choose L hL using hloc
  exact ⟨L, hL⟩

end

end Hironaka.Analytic.Unibranch.HironakaG11GluedWindowSteps
