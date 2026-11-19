import Hironaka.Analytic.Unibranch.HironakaG11GluedWindowSteps
import Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels
import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction

/-! ANY actual current centre blowup: internally constructed next strict windows and
one true retained-shadow HS threshold-cover propagation.
Blueprint FIRST: original-native-shadow-threshold-step.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowThresholdStep
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace SmoothCentreModification
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalLocalEmbeddingStalkHS
  OriginalIntrinsicHSSuperlevels HironakaG11HSPhaseInduction HironakaG11ManifoldWindowCentres
  HironakaG11WindowTowers HironakaG11BlowupLocality BlowupTowers EmbeddedBlowup

variable {X Y : SourceReducedComplexSpace} {ι : Type*}
  (F : ManifoldSmoothCentres X ι) (hc : F.Compatible) (hcl : IsClosed F.support)
  (p : Y ⟶ X)
  (hp : IsSmoothCentreBlowup p
    (OriginalAnalyticClosedSubspace.inclusion X F.support (F.isAnalyticSubset_support hc hcl)))
  (Z : ∀ i, CMfd.{0} (F.dim i)) (π : ∀ i, Z i→F.ambient i)
  (hπ : ∀ i, IsBlowupAlong (F.dim i) (F.centre i) (π i))

/-- The genuine whole strict carrier of the ACTUAL prescribed local ambient blowup. -/
def strictSource (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform (F.dim i) (π i) (F.carrier i))
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (hπ i) (F.analytic i))

def strictProjection (i : ι) : strictSource F Z π hπ i ⟶
    ofClosedAnalytic (F.carrier i) (F.analytic i) :=
  strictTransformMorphism (hπ i) (F.analytic i)

include hc hcl hp

/-- ANY actual realization p: actual next native windows, not a caller window/range packet. -/
theorem exists_strict_native_windows (hsing : F.support⊆intrinsicSingularLocus X.obj) :
    ∃ L : ∀ i, strictSource F Z π hπ i ⟶ Y, ∀ i,
      LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
      L i ≫ p = strictProjection F Z π hπ i ≫ F.map i ∧
      range (L i).hom.left.base=p.hom.left.base ⁻¹' range (F.map i).hom.left.base ∧
      ∀ L', L' ≫ p = strictProjection F Z π hπ i ≫ F.map i → L'=L i := by
  have hrange:=OriginalAnalyticClosedSubspace.inclusion_range X F.support
    (F.isAnalyticSubset_support hc hcl)
  have hex : ∀ i, ∃ L : strictSource F Z π hπ i ⟶ Y,
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      L ≫ p = strictProjection F Z π hπ i ≫ F.map i ∧
      range L.hom.left.base=p.hom.left.base ⁻¹' range (F.map i).hom.left.base ∧
      ∀ L', L' ≫ p = strictProjection F Z π hπ i ≫ F.map i → L'=L := by
    intro i
    have htr : (F.map i).hom.left.base ⁻¹' range
        (OriginalAnalyticClosedSubspace.inclusion X F.support
          (F.isAnalyticSubset_support hc hcl)).hom.left.base=F.trace i := by
      rw [hrange]
      exact F.preimage_support hc i
    have hLocal : IsIdealBlowup (strictProjection F Z π hπ i)
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealModule
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left
          ((F.map i).hom.left.base ⁻¹' range
            (OriginalAnalyticClosedSubspace.inclusion X F.support
              (F.isAnalyticSubset_support hc hcl)).hom.left.base))
        (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealInclusion
          (ofClosedAnalytic (F.carrier i) (F.analytic i)).obj.left
          ((F.map i).hom.left.base ⁻¹' range
            (OriginalAnalyticClosedSubspace.inclusion X F.support
              (F.isAnalyticSubset_support hc hcl)).hom.left.base)) := by
      rw [htr]
      exact strictTransformMorphism_isIdealBlowup (hπ i) (F.analytic i) (F.centre_subset i)
        (ManifoldSmoothCentres.carrier_subset_closure_diff F hsing i)
    obtain ⟨L,⟨hSquare,hUnique⟩,hOpen,hRange⟩:=
      exists_openImmersion_of_isSmoothCentreBlowup hp (F.isOpenImmersion i) hLocal
    exact ⟨L,hOpen,hSquare,hRange,hUnique⟩
  choose L hL using hex
  exact ⟨L,hL⟩

/-- True current-centre containment, not a future threshold/cover certificate. -/
theorem threshold_image {H : ℕ→ℕ}
    (hCentre : F.support⊆originalSingularHSThreshold X H) :
    originalSingularHSThreshold Y H⊆p.hom.left.base ⁻¹' originalSingularHSThreshold X H := by
  have hIso:=hp.isIsoOver_compl_range
  rw [OriginalAnalyticClosedSubspace.inclusion_range] at hIso
  intro y hy
  by_cases hx : p.hom.left.base y∈F.support
  · exact hCentre hx
  · have hyOff : p.hom.left.base y∈F.supportᶜ := hx
    refine ⟨?_,?_⟩
    · intro hxReg
      exact hy.1 ((hIso.mem_intrinsicRegularLocus_iff hyOff).mpr hxReg)
    · have hHS:=originalStalkHS_isIsoOver hIso hyOff
      intro l
      exact (hy.2 l).trans_eq (congrFun hHS l)

/-- Construct ACTUAL next native windows and propagate ONLY the retained-shadow threshold cover. -/
theorem exists_step_threshold_cover {H : ℕ→ℕ}
    (hCentre : F.support⊆originalSingularHSThreshold X H) (S : Set X.obj.left)
    (hCover : originalSingularHSThreshold X H∩S⊆⋃ i,range (F.map i).hom.left.base) :
    ∃ L : ∀ i, strictSource F Z π hπ i ⟶ Y,
      (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
        L i ≫ p = strictProjection F Z π hπ i ≫ F.map i ∧
        range (L i).hom.left.base=p.hom.left.base ⁻¹' range (F.map i).hom.left.base ∧
        ∀ L', L' ≫ p = strictProjection F Z π hπ i ≫ F.map i → L'=L i) ∧
      originalSingularHSThreshold Y H∩p.hom.left.base ⁻¹' S⊆
        ⋃ i,range (L i).hom.left.base := by
  have hsing : F.support⊆intrinsicSingularLocus X.obj := fun _ hx=>(hCentre hx).1
  obtain ⟨L,hL⟩:=exists_strict_native_windows F hc hcl p hp Z π hπ hsing
  refine ⟨L,hL,?_⟩
  rintro y ⟨hyC,hyS⟩
  have hxC:=threshold_image F hc hcl p hp hCentre hyC
  obtain ⟨i,hi⟩:=mem_iUnion.mp (hCover ⟨hxC,hyS⟩)
  exact mem_iUnion.mpr ⟨i,(Set.ext_iff.mp (hL i).2.2.1 y).mpr hi⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowThresholdStep
