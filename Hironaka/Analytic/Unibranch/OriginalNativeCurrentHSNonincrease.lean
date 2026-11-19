import Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout
import Hironaka.Analytic.Unibranch.OriginalNativeShadowThresholdStep

/-! Global original HS nonincrease for ANY actual realization of the SAME current
centre blowup and TRUE prescribed next original ambient heads. No nextXStage packet.
Blueprint FIRST: original-native-current-hs-nonincrease.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSNonincrease
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace SmoothCentreModification
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11HSPhaseInduction
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11PresWindows HironakaG11PresReduction HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG11WindowTowers HironakaG11ManifoldWindowCentres
  OriginalNativeCurrentHSReadout BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain)

variable {Base : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}
  (w : ι→DimEmbedding Base N) (raw : ∀ i,MarkedIdeal N (Amb w i)) (e : ι→ℕ)
  {H : ℕ→ℕ} (hRaw : ∀ i,IsNativeWindowRecord (w i) (raw i) H) (he : ∀ i,1≤e i)
  {Λ : Type*} [LinearOrder Λ] (R : ResolutionInvariant.{0} N N Λ)
  {m : ℕ} (s : GStage R (chosenRecord w raw e) (mapAdm w) m) (xs : XStage w s.T)
  (hTr : RecordsTransport R (chosenRecord w raw e) (mapAdm w))

private abbrev domains := fun i=>(chosen_isHSWindowRecord w raw e hRaw he i).1
private abbrev initialCosupp :=
  HSPresentation.cosupp_subset (fun i=>chosen_presentation w raw e hRaw he R i)
private abbrev footprints : ∀ i,Set (w i).ambient := fun _=>univ

private theorem selfCover : ∀ i (c : (w i).carrier),
    c.val∈(chosenRecord w raw e i).cosupp →
      ∃ j,∃ c' : (w j).carrier,c'.val∈footprints w j ∧
        (w j).toLocalEmbedding.toPoint c'=(w i).toLocalEmbedding.toPoint c := by
  intro i c _
  exact ⟨i,c,mem_univ _,rfl⟩

private abbrev centreSubset :=
  (HSPresentation.cosuppInStrictSing
    (fun i=>chosen_presentation w raw e hRaw he R i)).gcentre_subset
      (K := footprints w) s xs

-- This is ONLY a reducible notation for the SAME accepted xs.centres constructor.
private abbrev family := xs.centres (domains w raw e hRaw he)
  (initialCosupp w raw e hRaw he R) (selfCover w raw e) hTr s
  (centreSubset w raw e hRaw he R s xs)

private abbrev nextStage := s.next (domains w raw e hRaw he)
  (initialCosupp w raw e hRaw he R) (selfCover w raw e) (adm_exists_map w) hTr
private abbrev nextAmbient (i : ι) : CMfd.{0} N :=
  gnextSpace (domains w raw e hRaw he) (initialCosupp w raw e hRaw he R)
    (selfCover w raw e) (adm_exists_map w) hTr s i
private abbrev nextMap (i : ι) : nextAmbient w raw e hRaw he R s hTr i→(s.T i).1 :=
  gnextMap (domains w raw e hRaw he) (initialCosupp w raw e hRaw he R)
    (selfCover w raw e) (adm_exists_map w) hTr s i
private abbrev nextBlowup (i : ι) :=
  gnextMap_isBlowup (domains w raw e hRaw he) (initialCosupp w raw e hRaw he R)
    (selfCover w raw e) (adm_exists_map w) hTr s i

include hRaw he hTr

private theorem family_compatible : (family w raw e hRaw he R s xs hTr).Compatible :=
  xs.centres_compatible (domains w raw e hRaw he) (initialCosupp w raw e hRaw he R)
    (selfCover w raw e) hTr s (centreSubset w raw e hRaw he R s xs)

private theorem family_singular : (family w raw e hRaw he R s xs hTr).support⊆
    intrinsicSingularLocus xs.Y.obj := by
  intro x hx
  obtain ⟨i,c,hc,hcx⟩:=(family w raw e hRaw he R s xs hTr).mem_support.mp hx
  exact hcx ▸ (current_native_data w raw e hRaw he R s xs i c).2.2 hc.1

private theorem family_profile (x : xs.Y.obj.left)
    (hx : x∈(family w raw e hRaw he R s xs hTr).support) :
    originalStalkHS xs.Y x=H :=
  current_global_centre_profile w raw e hRaw he R s xs (footprints w)
    (selfCover w raw e) hTr x hx

/-- Literal true-next strict carrier, derived by full-carrier density, not a nextXStage premise. -/
theorem strict_carrier_next_eq (i : ι) :
    strictTransform N (nextMap w raw e hRaw he R s hTr i) (xs.carrier i)=
      strictAlong ((nextStage w raw e hRaw he R s hTr).T i).2 (w i).carrier := by
  change _=BlowupStrictSubmanifold.geoStrictTransform
    (nextMap w raw e hRaw he R s hTr i)
    (gcentre R (chosenRecord w raw e) (footprints w) s.T i)
    (strictAlong (s.T i).2 (w i).carrier)
  rw [← xs.carrier_eq i]
  exact (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform
    (nextBlowup w raw e hRaw he R s hTr i)
    (ManifoldSmoothCentres.carrier_subset_closure_diff
      (family w raw e hRaw he R s xs hTr) (family_singular w raw e hRaw he R s xs hTr) i)).symm

/-- SAME initial presentation at the TRUE next canonical tower, on its ACTUAL reduced strict source. -/
theorem next_strict_hs_bound (i : ι)
    (c : (OriginalNativeShadowThresholdStep.strictSource
      (family w raw e hRaw he R s xs hTr) (nextAmbient w raw e hRaw he R s hTr)
      (nextMap w raw e hRaw he R s hTr) (nextBlowup w raw e hRaw he R s hTr) i).obj.left) :
    originalStalkHS
      (OriginalNativeShadowThresholdStep.strictSource
        (family w raw e hRaw he R s xs hTr) (nextAmbient w raw e hRaw he R s hTr)
        (nextMap w raw e hRaw he R s hTr) (nextBlowup w raw e hRaw he R s hTr) i) c≤H := by
  have hNext:=(chosen_presentation w raw e hRaw he R i
    ((nextStage w raw e hRaw he R s hTr).T i).2
    ((nextStage w raw e hRaw he R s hTr).canonical i)).2
  rw [← strict_carrier_next_eq w raw e hRaw he R s xs hTr i] at hNext
  exact (hNext
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (nextBlowup w raw e hRaw he R s hTr i) (xs.analytic i)) c).1

variable {Y : SourceReducedComplexSpace}
  (hClosed : IsClosed (family w raw e hRaw he R s xs hTr).support) (p : Y⟶xs.Y)
  (hp : IsSmoothCentreBlowup p
    (OriginalAnalyticClosedSubspace.inclusion xs.Y
      (family w raw e hRaw he R s xs hTr).support
      ((family w raw e hRaw he R s xs hTr).isAnalyticSubset_support
        (family_compatible w raw e hRaw he R s xs hTr) hClosed)))
include hClosed hp

/-- ANY SAME actual p: construct real strict native windows, derive GLOBAL whole HS decrease and
FULL native inverse outside the literal old threshold. No nextXStage/local-HS packet. -/
theorem exists_next_hs_nonincrease :
    ∃ L : ∀ i, OriginalNativeShadowThresholdStep.strictSource
        (family w raw e hRaw he R s xs hTr) (nextAmbient w raw e hRaw he R s hTr)
        (nextMap w raw e hRaw he R s hTr) (nextBlowup w raw e hRaw he R s hTr) i ⟶ Y,
      (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
        L i ≫ p=OriginalNativeShadowThresholdStep.strictProjection
          (family w raw e hRaw he R s xs hTr) (nextAmbient w raw e hRaw he R s hTr)
          (nextMap w raw e hRaw he R s hTr) (nextBlowup w raw e hRaw he R s hTr) i ≫ xs.map i ∧
        range (L i).hom.left.base=p.hom.left.base ⁻¹' range (xs.map i).hom.left.base ∧
        ∀ L',L' ≫ p=OriginalNativeShadowThresholdStep.strictProjection
          (family w raw e hRaw he R s xs hTr) (nextAmbient w raw e hRaw he R s hTr)
          (nextMap w raw e hRaw he R s hTr) (nextBlowup w raw e hRaw he R s hTr) i ≫ xs.map i → L'=L i) ∧
      (∀ y,originalStalkHS Y y≤originalStalkHS xs.Y (p.hom.left.base y)) ∧
      IsIsoOver p (originalSingularHSThreshold xs.Y H)ᶜ ∧
      ∀ y,p.hom.left.base y∉originalSingularHSThreshold xs.Y H →
        originalStalkHS Y y=originalStalkHS xs.Y (p.hom.left.base y) := by
  let F:=family w raw e hRaw he R s xs hTr
  have hsing:=family_singular w raw e hRaw he R s xs hTr
  obtain ⟨L,hL⟩:=OriginalNativeShadowThresholdStep.exists_strict_native_windows F
    (family_compatible w raw e hRaw he R s xs hTr) hClosed p hp
    (nextAmbient w raw e hRaw he R s hTr) (nextMap w raw e hRaw he R s hTr)
    (nextBlowup w raw e hRaw he R s hTr) hsing
  have hIso:=hp.isIsoOver_compl_range
  rw [OriginalAnalyticClosedSubspace.inclusion_range] at hIso
  have hCentre : F.support⊆originalSingularHSThreshold xs.Y H := by
    intro x hx
    exact ⟨hsing hx,fun l=>(congrFun (family_profile w raw e hRaw he R s xs hTr x hx) l).ge⟩
  have hOff : IsIsoOver p (originalSingularHSThreshold xs.Y H)ᶜ :=
    hIso.of_isOpen_subset (original_hs_threshold_dictionary xs.Y H).2.1.isClosed.isOpen_compl
      (compl_subset_compl.mpr hCentre)
  refine ⟨L,hL,?_,hOff,fun y hy=>originalStalkHS_isIsoOver hOff hy⟩
  intro y
  by_cases hx : p.hom.left.base y∈F.support
  · obtain ⟨i,c,_,hc⟩:=F.mem_support.mp hx
    have hyRange : y∈range (L i).hom.left.base :=
      (Set.ext_iff.mp (hL i).2.2.1 y).mpr ⟨c,hc⟩
    obtain ⟨z,hz⟩:=hyRange
    have hLocal:=next_strict_hs_bound w raw e hRaw he R s xs hTr i z
    have hHS:=originalStalkHS_openImmersion (L i) (hL i).1 z
    rw [hz] at hHS
    rw [family_profile w raw e hRaw he R s xs hTr (p.hom.left.base y) hx]
    exact fun l=>(congrFun hHS l).trans_le (hLocal l)
  · exact fun l=>(congrFun (originalStalkHS_isIsoOver hIso hx) l).le

end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSNonincrease
