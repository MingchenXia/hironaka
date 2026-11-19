import Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstBlowup
import Hironaka.Analytic.Unibranch.HironakaG11GluedWindowSteps

/-! Actual first canonical ambient prefixes and full strict-window squares
for the SAME actual native first-step projection. Blueprint FIRST:
original-native-shadow-first-prefix.tex. The retained input record is
literally the chosen native record/power; stronger weighted-HS source
witnesses are not reconstructed from IsNativeWindowRecord. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstPrefix
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS HironakaIntrinsicComplexAnalyticRegularLocus
  OriginalNativeHSCompactShadowWindows HironakaG11CompatibleAnalyticCover
  HironakaG11ManifoldWindowCentres HironakaG11WindowTowers
  HironakaG11BlowupLocality SmoothCentreModification
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal ResolutionInvariantSeq ResolutionInvariantSegments
  HironakaActualPowerBoundaryExponents CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
local notation "d" => originalStalkHS X M.point 1 - 1
local notation "F₀" => OriginalNativeShadowInvariantCentre.centres M hK
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
private abbrev resolutionInvariant := (OriginalNativeShadowInvariantCentre.invariant M).toResolutionInvariant
local notation "R" => resolutionInvariant M
local notation "l" => OriginalNativeShadowInvariantCentre.level M hK

@[reducible] private instance goodCharted (i : (M.windows hK).ι) :
    ChartedSpace (ComplexModel d) ((F₀).window i) := by
  change ChartedSpace (ComplexModel ((F₀).emb i).dim) ((F₀).window i)
  infer_instance

private instance goodManifold (i : (M.windows hK).ι) :
    IsComplexManifold d ((F₀).window i) := by
  change IsComplexManifold ((F₀).emb i).dim ((F₀).window i)
  infer_instance

@[reducible] private instance finalCharted (i : (M.windows hK).ι) :
    ChartedSpace (ComplexModel d) ((F).window i) := by
  change ChartedSpace (ComplexModel ((F).emb i).dim) ((F).window i)
  infer_instance

private instance finalManifold (i : (M.windows hK).ι) :
    IsComplexManifold d ((F).window i) := by
  change IsComplexManifold ((F).emb i).dim ((F).window i)
  infer_instance

private abbrev goodAmbient (i : (M.windows hK).ι) : CMfd.{0} d := CMfd.of (n := d) (OriginalNativeShadowInvariantCentre.goodOpen M hK i)
private abbrev traceAmbient (i : (M.windows hK).ι) : CMfd.{0} d := CMfd.of (n := d)
  (OriginalNativeCentreOpenPullback.oldWindowTrace F₀ (N).inclusion (N).inclusion_isOpenImmersion i)
private abbrev base (i : (M.windows hK).ι) : CMfd.{0} d := CMfd.of (n := d) ((F).window i)

def goodRecord (i : (M.windows hK).ι) : MarkedIdeal d (goodAmbient M hK i) :=
  pullback (Subtype.val : OriginalNativeShadowInvariantCentre.goodOpen M hK i → ((M.windows hK).window i).ambient)
    (OriginalNativeShadowInvariantCentre.record M hK i)

def traceRecord (i : (M.windows hK).ι) : MarkedIdeal d (traceAmbient M hK i) :=
  pullback (M := goodAmbient M hK i) (M' := traceAmbient M hK i) Subtype.val (goodRecord M hK i)

/-- Literal two open pullbacks followed by the ACTUAL window biholomorphism. -/
def record (i : (M.windows hK).ι) : MarkedIdeal d (base M hK i) :=
  pullback (M := traceAmbient M hK i) (M' := base M hK i) (OriginalNativeCentreOpenPullback.windowEquiv F₀ (N).inclusion (N).inclusion_isOpenImmersion i)
    (traceRecord M hK i)

private theorem good_domain (i : (M.windows hK).ι) : IsInvDomain d (goodRecord M hK i) :=
  InvDomainTowerAlong.isInvDomain_pullback_val (OriginalNativeShadowInvariantCentre.goodOpen M hK i) (OriginalNativeShadowInvariantCentre.domain M hK i)

private theorem trace_domain (i : (M.windows hK).ι) : IsInvDomain d (traceRecord M hK i) :=
  @InvDomainTowerAlong.isInvDomain_pullback_val d (goodAmbient M hK i).carrier
    (goodAmbient M hK i).topologicalSpace (goodAmbient M hK i).chartedSpace
    (goodAmbient M hK i).isComplexManifold
    (OriginalNativeCentreOpenPullback.oldWindowTrace F₀ (N).inclusion (N).inclusion_isOpenImmersion i)
    (goodRecord M hK i) d (good_domain M hK i)

theorem domain (i : (M.windows hK).ι) : IsInvDomain d (record M hK i) :=
  InvDomainTowerAlong.isInvDomain_pullback
    (OriginalNativeCentreOpenPullback.windowEquiv F₀ (N).inclusion (N).inclusion_isOpenImmersion i)
    (trace_domain M hK i)

private theorem good_cosupp (i : (M.windows hK).ι) : (goodRecord M hK i).cosupp =
    (Subtype.val : (F₀).window i → ((M.windows hK).window i).ambient) ⁻¹'
      (OriginalNativeShadowInvariantCentre.record M hK i).cosupp :=
  MarkedIdealRestrictOpen.cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (OriginalNativeShadowInvariantCentre.domain M hK i).isWellFormed.isCoherent hg) _

private theorem trace_cosupp (i : (M.windows hK).ι) : (traceRecord M hK i).cosupp =
    (Subtype.val : OriginalNativeCentreOpenPullback.oldWindowTrace F₀ (N).inclusion
      (N).inclusion_isOpenImmersion i → (F₀).window i) ⁻¹' (goodRecord M hK i).cosupp :=
  MarkedIdealRestrictOpen.cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (good_domain M hK i).isWellFormed.isCoherent hg) _

theorem cosupp (i : (M.windows hK).ι) : (record M hK i).cosupp =
    (fun y : (F).window i =>
      (OriginalNativeCentreOpenPullback.windowInclusion F₀ (N).inclusion (N).inclusion_isOpenImmersion i y).val) ⁻¹'
        (OriginalNativeShadowInvariantCentre.record M hK i).cosupp := by
  let e := OriginalNativeCentreOpenPullback.windowEquiv F₀ (N).inclusion (N).inclusion_isOpenImmersion i
  have he := cosupp_pullback e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply
    (traceRecord M hK i) (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (trace_domain M hK i).isWellFormed.isCoherent hg)
  exact he.trans ((congrArg (fun A => e ⁻¹' A) (trace_cosupp M hK i)).trans
    (congrArg (fun A => e ⁻¹' (Subtype.val ⁻¹' A)) (good_cosupp M hK i)))

theorem value (i : (M.windows hK).ι) (y : (F).window i) (hy : y ∈ (record M hK i).cosupp) :
    (R).inv (X := base M hK i) (record M hK i) BlowupTower.refl y =
      OriginalNativeShadowInvariantCentre.value M hK i
        (OriginalNativeCentreOpenPullback.windowInclusion F₀ (N).inclusion (N).inclusion_isOpenImmersion i y).val := by
  let e := OriginalNativeCentreOpenPullback.windowEquiv F₀ (N).inclusion (N).inclusion_isOpenImmersion i
  have hyt : e y ∈ (traceRecord M hK i).cosupp := by
    have he := cosupp_pullback e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply
      (traceRecord M hK i) (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (trace_domain M hK i).isWellFormed.isCoherent hg)
    exact (Set.ext_iff.mp he y).mp hy
  have hyg : (e y).val ∈ (goodRecord M hK i).cosupp := (Set.ext_iff.mp (trace_cosupp M hK i) _).mp hyt
  have hyo := (Set.ext_iff.mp (good_cosupp M hK i) _).mp hyg
  have h1 := (R).isInvValue.towerIso (X := traceAmbient M hK i) (X' := base M hK i)
    e (traceRecord M hK i) (trace_domain M hK i)
    BlowupTower.refl BlowupTower.refl e IsTowerIso.refl trivial y hyt
  have h2 := (R).isInvValue.restrictOpen (goodRecord M hK i) (good_domain M hK i)
    (OriginalNativeCentreOpenPullback.oldWindowTrace F₀ (N).inclusion (N).inclusion_isOpenImmersion i)
    BlowupTower.refl trivial (e y) hyg
  have h3 := (R).isInvValue.restrictOpen (OriginalNativeShadowInvariantCentre.record M hK i)
    (OriginalNativeShadowInvariantCentre.domain M hK i) ((F₀).window i)
    BlowupTower.refl trivial (e y).val hyo
  exact h1.trans (h2.trans h3)

theorem record_mark (i : (M.windows hK).ι) :
    (record M hK i).d = OriginalNativeShadowInvariantCentre.commonMark M hK := by
  change (OriginalNativeShadowInvariantCentre.record M hK i).d = _
  exact OriginalNativeShadowInvariantCentre.record_mark M hK i

/-- Fresh phase input has a PROVED empty boundary; no transformed record is reset. -/
theorem record_boundary (i : (M.windows hK).ι) : (record M hK i).E = [] := by
  have he := (OriginalNativeShadowInvariantCentre.record_hs M hK i).2.2.1
  simp only [record, traceRecord, goodRecord, pullback, he, List.map_nil]


theorem centre_dictionary (i : (M.windows hK).ι) :
    (F).centre i = {y | y ∈ (record M hK i).cosupp ∧ (R).inv (X := base M hK i) (record M hK i) BlowupTower.refl y = l} := by
  ext y
  have hc := Set.ext_iff.mp (cosupp M hK i) y
  constructor
  · intro hy
    have hcos : y ∈ (record M hK i).cosupp := hc.mpr hy.1
    exact ⟨hcos, (value M hK i y hcos).trans hy.2⟩
  · intro hy
    exact ⟨hc.mp hy.1, (value M hK i y hy.1).symm.trans hy.2⟩

theorem value_bound (i : (M.windows hK).ι) (y : (F).window i)
    (hy : y ∈ (record M hK i).cosupp) : (R).inv (X := base M hK i) (record M hK i) BlowupTower.refl y ≤ l := by
  rw [value M hK i y hy]
  exact OriginalNativeShadowInvariantCentre.goodOpen_bounds M hK i _
    (OriginalNativeCentreOpenPullback.windowInclusion F₀ (N).inclusion (N).inclusion_isOpenImmersion i y).property
    ((Set.ext_iff.mp (cosupp M hK i) y).mp hy)

theorem centre_max (i : (M.windows hK).ι) : (F).centre i = ∅ ∨
    (F).centre i = ResolutionDriver.maxLocus ((R).inv (X := base M hK i) (record M hK i) BlowupTower.refl) (record M hK i).cosupp := by
  rw [centre_dictionary M hK i]
  exact HironakaG11CompatibleLevelSets.levelSet_eq_empty_or_eq_maxLocus _ _ _ (value_bound M hK i)

/-- The SAME actual family viewed on its genuine manifold windows. -/
def manifoldCentres : ManifoldSmoothCentres (N).source (M.windows hK).ι where
  dim _ := d
  ambient := base M hK
  carrier i := (F).windowCarrier i
  analytic i := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val ((F).emb i).analytic ((F).window i)
  map := (F).windowMap
  isOpenImmersion := (F).windowMap_isOpenImmersion
  centre := (F).centre
  isClosedSubmanifold := (F).isClosedSubmanifold
  centre_subset := (F).centre_subset

private theorem manifold_compatible : (manifoldCentres M hK).Compatible :=
  OriginalNativeShadowFirstBlowup.centres_compatible M hK

private theorem manifold_singular : (manifoldCentres M hK).support ⊆
    intrinsicSingularLocus (N).source.obj :=
  OriginalNativeShadowFirstBlowup.centres_singular M hK

private theorem ambient_exists (i : (M.windows hK).ι) :
    ∃ (Z : CMfd.{0} d) (p : Z → base M hK i), IsBlowupAlong d ((F).centre i) p :=
  ResolutionDriver.exists_blowup _ ((F).isClosedSubmanifold i)
    (ManifoldSmoothCentres.interior_centre_eq_empty (manifoldCentres M hK) (manifold_singular M hK) i)

def ambient (i : (M.windows hK).ι) : CMfd.{0} d := (ambient_exists M hK i).choose

def projection (i : (M.windows hK).ι) : ambient M hK i → base M hK i :=
  (ambient_exists M hK i).choose_spec.choose

theorem isBlowup (i : (M.windows hK).ι) : IsBlowupAlong d ((F).centre i) (projection M hK i) :=
  (ambient_exists M hK i).choose_spec.choose_spec

/-- A literal physical head, including genuine empty and nonempty Cartier centres. -/
def tower (i : (M.windows hK).ι) : BlowupTower (base M hK i) (ambient M hK i) :=
  .step .refl ((F).centre i) (projection M hK i) (isBlowup M hK i)

theorem canonical (i : (M.windows hK).ι) :
    IsCanonical (record M hK i) ((R).inv (record M hK i)) (tower M hK i) :=
  ⟨trivial, centre_max M hK i⟩

theorem length (i : (M.windows hK).ι) : (tower M hK i).length = 1 := rfl

def transformedRecord (i : (M.windows hK).ι) : MarkedIdeal d (ambient M hK i) :=
  geoTransformAlong (record M hK i) (tower M hK i)

theorem transformed_boundary (i : (M.windows hK).ι) :
    (transformedRecord M hK i).E =
      (record M hK i).E.map (BlowupStrictSubmanifold.geoStrictTransform (projection M hK i) ((F).centre i)) ++
        [(projection M hK i) ⁻¹' (F).centre i] := rfl

theorem transformed_mark (i : (M.windows hK).ι) :
    (transformedRecord M hK i).d = OriginalNativeShadowInvariantCentre.commonMark M hK :=
  record_mark M hK i

/-- STRICT drop on the SAME whole surviving transformed cosupport, without a global cover. -/
theorem surviving_value_lt (i : (M.windows hK).ι) (z : ambient M hK i)
    (hz : z ∈ (transformedRecord M hK i).cosupp) :
    (R).inv (record M hK i) (tower M hK i) z < l := by
  have htest := (R).isInvValue.isGeoTestTower_of_isCanonical (domain M hK i) _ (canonical M hK i)
  have hpz : projection M hK i z ∈ (record M hK i).cosupp :=
    StepOneWellFounded.proj_mem_cosupp_step (domain M hK i).isWellFormed.isClosedSubmanifold_N
      (domain M hK i).isWellFormed.isCoherent BlowupTower.refl _ _ (isBlowup M hK i) htest hz
  have hle := value_bound M hK i (projection M hK i z) hpz
  by_cases hc : projection M hK i z ∈ (F).centre i
  · have hne : ((F).centre i).Nonempty := ⟨_, hc⟩
    have hmax := (centre_max M hK i).resolve_left hne.ne_empty
    exact ((R).isInvValue.decrease (record M hK i) (domain M hK i)
      BlowupTower.refl _ _ (isBlowup M hK i) trivial hne hmax z hz).1 hc |>.trans_le hle
  · have hlt : (R).inv (X := base M hK i) (record M hK i) BlowupTower.refl (projection M hK i z) < l := by
      apply lt_of_le_of_ne hle
      intro heq
      exact hc ((Set.ext_iff.mp (centre_dictionary M hK i) _).mpr ⟨hpz, heq⟩)
    have heq : (R).inv (record M hK i) (tower M hK i) z =
        (R).inv (X := base M hK i) (record M hK i) BlowupTower.refl (projection M hK i z) := by
      by_cases hne : ((F).centre i).Nonempty
      · have hmax := (centre_max M hK i).resolve_left hne.ne_empty
        exact ((R).isInvValue.decrease (record M hK i) (domain M hK i)
          BlowupTower.refl _ _ (isBlowup M hK i) trivial hne hmax z hz).2 hc
      · exact (R).isInvValue.emptyStep (record M hK i) (domain M hK i)
          BlowupTower.refl _ _ (isBlowup M hK i) (not_nonempty_iff_eq_empty.mp hne) trivial z hz
    exact heq ▸ hlt

/-- The WHOLE actual native strict carrier of the same ambient head. -/
def strictSource (i : (M.windows hK).ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictTransform d (projection M hK i) ((manifoldCentres M hK).carrier i))
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (isBlowup M hK i) ((manifoldCentres M hK).analytic i))

def strictProjection (i : (M.windows hK).ι) : strictSource M hK i ⟶ (F).windowSpace i :=
  EmbeddedBlowup.strictTransformMorphism (isBlowup M hK i) ((manifoldCentres M hK).analytic i)

variable (s : OriginalNativeShadowFirstBlowup.Step M hK)

private theorem strict_ideal (i : (M.windows hK).ι) :
    IsIdealBlowup (strictProjection M hK i)
      (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealModule ((F).windowSpace i).obj.left
        (((F).windowMap i).hom.left.base ⁻¹' range
          (OriginalAnalyticClosedSubspace.inclusion (N).source (F).support s.centre_analytic).hom.left.base))
      (HironakaIntrinsicReducedCentreIdealSheaf.intrinsicReducedCentreIdealInclusion ((F).windowSpace i).obj.left
        (((F).windowMap i).hom.left.base ⁻¹' range
          (OriginalAnalyticClosedSubspace.inclusion (N).source (F).support s.centre_analytic).hom.left.base)) := by
  rw [OriginalAnalyticClosedSubspace.inclusion_range]
  rw [(F).preimage_support (OriginalNativeShadowFirstBlowup.centres_compatible M hK) i]
  exact strictTransformMorphism_isIdealBlowup (isBlowup M hK i) ((manifoldCentres M hK).analytic i)
    ((F).centre_subset i)
    (ManifoldSmoothCentres.carrier_subset_closure_diff (manifoldCentres M hK) (manifold_singular M hK) i)

private theorem exists_nativeWindow (i : (M.windows hK).ι) :
    ∃ L : strictSource M hK i ⟶ s.source,
      (L ≫ s.projection = strictProjection M hK i ≫ (F).windowMap i ∧
        ∀ L₁, L₁ ≫ s.projection = strictProjection M hK i ≫ (F).windowMap i → L₁ = L) ∧
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      range L.hom.left.base = s.projection.hom.left.base ⁻¹' range ((F).windowMap i).hom.left.base :=
  exists_openImmersion_of_isSmoothCentreBlowup s.blowup ((F).windowMap_isOpenImmersion i)
    (strict_ideal M hK s i)

def nativeWindow (i : (M.windows hK).ι) : strictSource M hK i ⟶ s.source :=
  (exists_nativeWindow M hK s i).choose

theorem nativeWindow_isOpenImmersion (i : (M.windows hK).ι) :
    LocallyRingedSpace.IsOpenImmersion (nativeWindow M hK s i).hom.left :=
  (exists_nativeWindow M hK s i).choose_spec.2.1

theorem nativeWindow_square (i : (M.windows hK).ι) :
    nativeWindow M hK s i ≫ s.projection = strictProjection M hK i ≫ (F).windowMap i :=
  (exists_nativeWindow M hK s i).choose_spec.1.1

theorem nativeWindow_range (i : (M.windows hK).ι) :
    range (nativeWindow M hK s i).hom.left.base =
      s.projection.hom.left.base ⁻¹' range ((F).windowMap i).hom.left.base :=
  (exists_nativeWindow M hK s i).choose_spec.2.2

theorem nativeWindow_scalar (i : (M.windows hK).ι) :
    (nativeWindow M hK s i).hom.left ≫ s.source.obj.hom = (strictSource M hK i).obj.hom :=
  Over.w (nativeWindow M hK s i).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstPrefix
