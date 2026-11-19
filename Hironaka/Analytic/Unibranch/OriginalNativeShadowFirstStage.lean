import Hironaka.Analytic.Unibranch.OriginalNativeShadowFlatWindows
import Hironaka.Analytic.Unibranch.OriginalNativeShadowThresholdStep

/-! The genuine compatible first ambient/native stage of the SAME frozen
native compact-shadow blowup. Blueprint FIRST: original-native-shadow-first-stage.tex.
Auxiliary whole windows have TRUE self-coverage, never compactness. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstStage
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalNativeHSCompactShadowWindows HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11PresLineState HironakaG11PresReduction HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG1CanonicalStageCentreIdeal
  HironakaG11HSPhaseInduction HironakaG11ManifoldWindowCentres HironakaG11WindowTowers
  HironakaG11BlowupLocality HironakaIntrinsicComplexAnalyticRegularLocus
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal HironakaActualPowerBoundaryExponents
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces SmoothCentreModification
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
private abbrev dimension := originalStalkHS X M.point 1 - 1
private abbrev invariant := OriginalNativeShadowInvariantCentre.invariant M
private abbrev resolutionInvariant := (invariant M).toResolutionInvariant
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
local notation "w" => OriginalNativeShadowFlatWindows.window M hK
local notation "Q" => OriginalNativeShadowFlatWindows.record M hK
local notation "R" => resolutionInvariant M
local notation "l" => OriginalNativeShadowInvariantCentre.level M hK

/-- Genuine original-invariant presentation of the INITIAL common powers. -/
theorem presentation (i : (M.windows hK).ι) : HSPresentation R (w i) (Q i) (originalStalkHS X M.point) :=
  ((OriginalNativeShadowFlatWindows.native_record M hK i).isHSWindowRecord.powerMarked
    (OriginalNativeShadowInvariantCentre.exponent_pos M hK i)).hsPresentation R

theorem domain (i : (M.windows hK).ι) : IsInvDomain (dimension M) (Q i) :=
  ((OriginalNativeShadowFlatWindows.native_record M hK i).isHSWindowRecord.powerMarked
    (OriginalNativeShadowInvariantCentre.exponent_pos M hK i)).1

theorem cosupp_subset (i : (M.windows hK).ι) : (Q i).cosupp ⊆ (w i).carrier :=
  HSPresentation.cosupp_subset (presentation M hK) i

/-- TRUE same-point self-coverage, with no compact-whole-window assertion. -/
theorem selfCover (i : (M.windows hK).ι) (c : (w i).carrier) (_hc : c.val ∈ (Q i).cosupp) :
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ (univ : Set (w j).ambient) ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c :=
  ⟨i, c, mem_univ _, rfl⟩

theorem recordsTransport : RecordsTransport R Q (mapAdm w) :=
  HironakaG1CanonicalStageCentreIdeal.recordsTransport w Q (invariant M)
    (domain M hK) (OriginalNativeShadowFlatWindows.initialClass M hK)

def zeroStage : GStage R Q (mapAdm w) 0 := GStage.zero R Q (mapAdm w)

theorem initial_cosupp (i : (M.windows hK).ι) :
    (Q i).cosupp = (OriginalNativeShadowFlatWindows.ambientEquiv M hK i) ⁻¹'
      (OriginalNativeShadowFirstPrefix.record M hK i).cosupp := by
  rw [OriginalNativeShadowFlatWindows.record_eq_pullback M hK i]
  let e := OriginalNativeShadowFlatWindows.ambientEquiv M hK i
  exact cosupp_pullback e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (OriginalNativeShadowFirstPrefix.domain M hK i).isWellFormed.isCoherent hg)

theorem initial_value (i : (M.windows hK).ι) (y : Amb w i) (hy : y ∈ (Q i).cosupp) :
    (R).inv (Q i) BlowupTower.refl y =
      (R).inv (OriginalNativeShadowFirstPrefix.record M hK i) BlowupTower.refl
        (OriginalNativeShadowFlatWindows.ambientEquiv M hK i y) := by
  have hOld := (Set.ext_iff.mp (initial_cosupp M hK i) y).mp hy
  rw [OriginalNativeShadowFlatWindows.record_eq_pullback M hK i]
  exact (R).isInvValue.towerIso (OriginalNativeShadowFlatWindows.ambientEquiv M hK i)
    (OriginalNativeShadowFirstPrefix.record M hK i) (OriginalNativeShadowFirstPrefix.domain M hK i)
    BlowupTower.refl BlowupTower.refl _ IsTowerIso.refl trivial y hOld

theorem initial_bound (i : (M.windows hK).ι) (y : Amb w i) (hy : y ∈ (Q i).cosupp) :
    (R).inv (Q i) BlowupTower.refl y ≤ l := by
  rw [initial_value M hK i y hy]
  exact OriginalNativeShadowFirstPrefix.value_bound M hK i _
    ((Set.ext_iff.mp (initial_cosupp M hK i) y).mp hy)

theorem maximum_attained : ∃ i, ∃ y : Amb w i, y ∈ (Q i).cosupp ∧ (R).inv (Q i) BlowupTower.refl y = l := by
  obtain ⟨x, -, hx⟩ := OriginalNativeShadowFirstBlowup.centre_meets_shadow M hK
  obtain ⟨i, z, hz, -⟩ := (F).mem_support.mp hx
  have hc : z.val ∈ (F).centre i := hz
  have hd := (Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.centre_dictionary M hK i) z.val).mp hc
  let e := OriginalNativeShadowFlatWindows.ambientEquiv M hK i
  let y : Amb w i := e.symm z.val
  have hy : y ∈ (Q i).cosupp :=
    (Set.ext_iff.mp (initial_cosupp M hK i) y).mpr (by
      change e (e.symm z.val) ∈ (OriginalNativeShadowFirstPrefix.record M hK i).cosupp
      exact (e.apply_symm_apply z.val).symm ▸ hd.1)
  refine ⟨i, y, hy, ?_⟩
  exact (initial_value M hK i y hy).trans ((congrArg
    ((R).inv (OriginalNativeShadowFirstPrefix.record M hK i) BlowupTower.refl)
    (e.apply_symm_apply z.val)).trans hd.2)

theorem greatest : IsGreatest (gfootValues R Q (fun _ => univ) (zeroStage M hK).T) l := by
  obtain ⟨i, y, hy, heq⟩ := maximum_attained M hK
  refine ⟨mem_iUnion.mpr ⟨i, y, ⟨hy, mem_univ _⟩, heq⟩, ?_⟩
  rintro v hv
  obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hv
  exact initial_bound M hK j z hz.1

/-- Whole first local centres, including empty and nonempty Cartier cases. -/
theorem centre_dictionary (i : (M.windows hK).ι) :
    gcentre R Q (fun _ => univ) (zeroStage M hK).T i =
      (OriginalNativeShadowFlatWindows.ambientEquiv M hK i) ⁻¹' (F).centre i := by
  ext y
  have hcos := Set.ext_iff.mp (initial_cosupp M hK i) y
  have hc := Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.centre_dictionary M hK i)
    (OriginalNativeShadowFlatWindows.ambientEquiv M hK i y)
  constructor
  · rintro ⟨hy, hUpper⟩
    have heq : (R).inv (Q i) BlowupTower.refl y = l :=
      le_antisymm (initial_bound M hK i y hy) (hUpper (greatest M hK).1)
    exact hc.mpr ⟨hcos.mp hy, (initial_value M hK i y hy).symm.trans heq⟩
  · intro hy
    obtain ⟨hOld, heq⟩ := hc.mp hy
    have hNew := hcos.mpr hOld
    refine ⟨hNew, ?_⟩
    have hv := (initial_value M hK i y hNew).trans heq
    change (R).inv (Q i) BlowupTower.refl y ∈ upperBounds _
    exact hv.symm ▸ (greatest M hK).2

/-- The real one-step compatible canonical ambient history. -/
def ambientStage : GStage R Q (mapAdm w) 1 :=
  (zeroStage M hK).next (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (adm_exists_map w) (recordsTransport M hK)

theorem ambient_length (i : (M.windows hK).ι) : ((ambientStage M hK).T i).2.length = 1 :=
  (ambientStage M hK).length i

theorem surviving_value_lt (i : (M.windows hK).ι) (z : ((ambientStage M hK).T i).1)
    (hz : z ∈ rcos Q (ambientStage M hK).T i) : rvalue R Q (ambientStage M hK).T i z < l :=
  rvalue_next_lt (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (adm_exists_map w) (recordsTransport M hK) (zeroStage M hK) (greatest M hK) i z hz

/-- Actual manifold centres on the true zero native stage. -/
def centres : ManifoldSmoothCentres (N).source (M.windows hK).ι :=
  (XStage.zero w).centres (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (recordsTransport M hK) (zeroStage M hK)
    (fun i _ hy => cosupp_subset M hK i hy.1)

theorem centres_compatible : (centres M hK).Compatible :=
  (XStage.zero w).centres_compatible (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (recordsTransport M hK) (zeroStage M hK)
    (fun i _ hy => cosupp_subset M hK i hy.1)

theorem support_eq : (centres M hK).support = (F).support := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, hy, hxy⟩ := (centres M hK).mem_support.mp hx
    have hc : OriginalNativeShadowFlatWindows.ambientEquiv M hK i y.val ∈ (F).centre i :=
      (Set.ext_iff.mp (centre_dictionary M hK i) y.val).mp hy
    let z := (OriginalNativeShadowFlatWindows.baseMap M hK i).hom.left.base y
    refine (F).mem_support.mpr ⟨i, z, hc, ?_⟩
    exact (congrArg (fun f => f.hom.left.base y)
      (OriginalNativeShadowFlatWindows.base_square M hK i)).trans hxy
  · intro hx
    obtain ⟨i, z, hz, hzx⟩ := (F).mem_support.mp hx
    let e := OriginalNativeShadowFlatWindows.ambientEquiv M hK i
    let y : (w i).carrier := ⟨e.symm z.val, by
      change e (e.symm z.val) ∈ (F).windowCarrier i
      exact (e.apply_symm_apply z.val).symm ▸ z.property⟩
    have hy : y.val ∈ (centres M hK).centre i := by
      apply (Set.ext_iff.mp (centre_dictionary M hK i) y.val).mpr
      change e (e.symm z.val) ∈ (F).centre i
      exact (e.apply_symm_apply z.val).symm ▸ hz
    have hpoint : (OriginalNativeShadowFlatWindows.baseMap M hK i).hom.left.base y = z :=
      Subtype.ext (e.apply_symm_apply z.val)
    refine (centres M hK).mem_support.mpr ⟨i, y, hy, ?_⟩
    exact (congrArg (fun f => f.hom.left.base y)
      (OriginalNativeShadowFlatWindows.base_square M hK i)).symm.trans
      ((congrArg ((F).windowMap i).hom.left.base hpoint).trans hzx)

theorem support_closed : IsClosed (centres M hK).support :=
  (support_eq M hK).symm ▸ OriginalNativeShadowFirstBlowup.centres_closed M hK

theorem support_singular : (centres M hK).support ⊆ intrinsicSingularLocus (N).source.obj :=
  (support_eq M hK).symm ▸ OriginalNativeShadowFirstBlowup.centres_singular M hK

variable (s : OriginalNativeShadowFirstBlowup.Step M hK)

private theorem blowup_same_set {B Y : SourceReducedComplexSpace} {C D : Set B.obj.left}
    (hCD : C = D) (hC : B.IsAnalyticSubset C) (hD : B.IsAnalyticSubset D)
    {p : Y ⟶ B} (hp : IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion B D hD)) :
    IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion B C hC) := by
  subst D
  exact hp

private theorem actual_blowup : IsSmoothCentreBlowup s.projection
    (OriginalAnalyticClosedSubspace.inclusion (N).source (centres M hK).support
      ((centres M hK).isAnalyticSubset_support (centres_compatible M hK) (support_closed M hK))) := by
  exact blowup_same_set (support_eq M hK) _ s.centre_analytic s.blowup

private def nextSpace (i : (M.windows hK).ι) : CMfd.{0} (dimension M) :=
  gnextSpace (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (adm_exists_map w) (recordsTransport M hK) (zeroStage M hK) i

private def nextMap (i : (M.windows hK).ι) : nextSpace M hK i → Amb w i :=
  gnextMap (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (adm_exists_map w) (recordsTransport M hK) (zeroStage M hK) i

private theorem nextBlowup (i : (M.windows hK).ι) :
    IsBlowupAlong (dimension M)
      (gcentre R Q (fun _ => univ) (zeroStage M hK).T i) (nextMap M hK i) :=
  gnextMap_isBlowup (domain M hK) (cosupp_subset M hK) (selfCover M hK)
    (adm_exists_map w) (recordsTransport M hK) (zeroStage M hK) i

private def strictSource (i : (M.windows hK).ι) : SourceReducedComplexSpace :=
  OriginalNativeShadowThresholdStep.strictSource (centres M hK) (nextSpace M hK)
    (nextMap M hK) (nextBlowup M hK) i

private theorem exists_windows : ∃ L : ∀ i, strictSource M hK i ⟶ s.source, ∀ i,
    LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
    L i ≫ s.projection = OriginalNativeShadowThresholdStep.strictProjection (centres M hK)
      (nextSpace M hK) (nextMap M hK) (nextBlowup M hK) i ≫ (centres M hK).map i ∧
    range (L i).hom.left.base = s.projection.hom.left.base ⁻¹' range ((centres M hK).map i).hom.left.base ∧
    ∀ L', L' ≫ s.projection = OriginalNativeShadowThresholdStep.strictProjection (centres M hK)
      (nextSpace M hK) (nextMap M hK) (nextBlowup M hK) i ≫ (centres M hK).map i → L' = L i :=
  OriginalNativeShadowThresholdStep.exists_strict_native_windows (centres M hK)
    (centres_compatible M hK) (support_closed M hK) s.projection (actual_blowup M hK s)
    (nextSpace M hK) (nextMap M hK) (nextBlowup M hK) (support_singular M hK)

/-- All fields are constructed on the SAME frozen native first-step source. -/
def nativeStage : XStage w (ambientStage M hK).T where
  Y := s.source
  q := s.projection
  isSingularCentreModification := s.modification
  carrier i := strictTransform (dimension M) (nextMap M hK i) (w i).carrier
  analytic i := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (nextBlowup M hK i) ((centres M hK).analytic i)
  map := (exists_windows M hK s).choose
  isOpenImmersion i := (exists_windows M hK s).choose_spec i |>.1
  carrier_eq i := by
    exact (BlowupStrictIdeal.geoStrictTransform_eq_strictTransform (nextBlowup M hK i)
      (ManifoldSmoothCentres.carrier_subset_closure_diff (centres M hK) (support_singular M hK) i)).symm
  square i c _hc := by
    exact congrArg (fun f => f.hom.left.base c) ((exists_windows M hK s).choose_spec i).2.1
  range_map i := ((exists_windows M hK s).choose_spec i).2.2.1

theorem native_source : (nativeStage M hK s).Y = s.source := rfl

theorem native_projection : (nativeStage M hK s).q = s.projection := rfl

theorem native_square (i : (M.windows hK).ι) (c : (nativeStage M hK s).carrier i) :
    s.projection.hom.left.base (((nativeStage M hK s).map i).hom.left.base c) =
      (w i).toLocalEmbedding.toPoint ⟨((ambientStage M hK).T i).2.proj c.val,
        (nativeStage M hK s).proj_mem i c⟩ :=
  (nativeStage M hK s).square i c ((nativeStage M hK s).proj_mem i c)

/-- FULL native quotient square on the SAME actual chosen strict-window maps. -/
theorem native_full_square (i : (M.windows hK).ι) :
    (nativeStage M hK s).map i ≫ s.projection =
      EmbeddedBlowup.strictTransformMorphism (nextBlowup M hK i) (w i).analytic ≫
        EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding :=
  ((exists_windows M hK s).choose_spec i).2.1

theorem native_scalar (i : (M.windows hK).ι) :
    ((nativeStage M hK s).map i).hom.left ≫ s.source.obj.hom =
      (ofClosedAnalytic ((nativeStage M hK s).carrier i) ((nativeStage M hK s).analytic i)).obj.hom :=
  Over.w ((nativeStage M hK s).map i).hom

theorem native_range (i : (M.windows hK).ι) :
    range (((nativeStage M hK s).map i).hom.left.base) =
      s.projection.hom.left.base ⁻¹' range (w i).toLocalEmbedding.toPoint :=
  (nativeStage M hK s).range_map i

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstStage
