import Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstPrefix

/-! Genuine native HS states of the SAME restricted raw and chosen phase
records, and the SAME actual first head. Blueprint FIRST:
original-native-shadow-restricted-state.tex. No new raw PHS factory,
post-blowup boundary reset, or dynamic phase completion is asserted. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowRestrictedState
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS HironakaIntrinsicComplexAnalyticRegularLocus
  OriginalNativeHSCompactShadowWindows HironakaG11PresLineState HironakaG11PresTowerState
  HironakaG11PresWindows HironakaG11PresPresentation HironakaG11PresReduction HironakaG11HSPhaseInduction
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  HironakaActualPowerBoundaryExponents MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  HironakaG11VanishingPrincipalization
open ResolutionInvariantSpec (IsInvDomain)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
local notation "H" => originalStalkHS X M.point
local notation "d" => H 1 - 1
local notation "F₀" => OriginalNativeShadowInvariantCentre.centres M hK
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
private abbrev goodAmbient (i : (M.windows hK).ι) : CMfd.{0} d :=
  CMfd.of (n := d) (OriginalNativeShadowInvariantCentre.goodOpen M hK i)
private abbrev traceOpen (i : (M.windows hK).ι) : Opens (goodAmbient M hK i) :=
  OriginalNativeCentreOpenPullback.oldWindowTrace F₀ (N).inclusion (N).inclusion_isOpenImmersion i
private abbrev traceAmbient (i : (M.windows hK).ι) : CMfd.{0} d :=
  CMfd.of (n := d) (traceOpen M hK i)
private abbrev base (i : (M.windows hK).ι) : CMfd.{0} d :=
  (OriginalNativeShadowFirstPrefix.manifoldCentres M hK).ambient i
private abbrev equiv (i : (M.windows hK).ι) :
    base M hK i ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ traceAmbient M hK i :=
  OriginalNativeCentreOpenPullback.windowEquiv F₀ (N).inclusion (N).inclusion_isOpenImmersion i

def rawGoodRecord (i : (M.windows hK).ι) : MarkedIdeal d (goodAmbient M hK i) :=
  pullback (M := Amb (M.windows hK).window i) (M' := goodAmbient M hK i) Subtype.val ((M.windows hK).record i)

def rawTraceRecord (i : (M.windows hK).ι) : MarkedIdeal d (traceAmbient M hK i) :=
  pullback (M := goodAmbient M hK i) (M' := traceAmbient M hK i) Subtype.val (rawGoodRecord M hK i)

def rawRecord (i : (M.windows hK).ι) : MarkedIdeal d (base M hK i) :=
  pullback (equiv M hK i) (rawTraceRecord M hK i)

private theorem good_domain (i : (M.windows hK).ι) : IsInvDomain d (rawGoodRecord M hK i) :=
  InvDomainTowerAlong.isInvDomain_pullback_val (OriginalNativeShadowInvariantCentre.goodOpen M hK i)
    ((M.windows hK).native i).1

private theorem trace_domain (i : (M.windows hK).ι) : IsInvDomain d (rawTraceRecord M hK i) :=
  @InvDomainTowerAlong.isInvDomain_pullback_val d (goodAmbient M hK i).carrier
    (goodAmbient M hK i).topologicalSpace (goodAmbient M hK i).chartedSpace
    (goodAmbient M hK i).isComplexManifold (traceOpen M hK i) (rawGoodRecord M hK i) d
    (good_domain M hK i)

theorem raw_domain (i : (M.windows hK).ι) : IsInvDomain d (rawRecord M hK i) :=
  InvDomainTowerAlong.isInvDomain_pullback (equiv M hK i) (trace_domain M hK i)

theorem raw_native (i : (M.windows hK).ι) :
    NativeHSState (rawRecord M hK i) ((F).windowCarrier i) H := by
  have h0 := ((M.windows hK).native i).2.2
  have h1 := h0.restrict (OriginalNativeShadowInvariantCentre.goodOpen M hK i)
  have h2 := h1.restrict (traceOpen M hK i)
  exact NativeHSState.pullback (equiv M hK i) h2

theorem raw_boundary (i : (M.windows hK).ι) : (rawRecord M hK i).E = [] := by
  have he := ((M.windows hK).native i).2.1
  simp only [rawRecord, rawTraceRecord, rawGoodRecord, pullback, he, List.map_nil]

/-- ENTIRE marked record equality, including ideal, mark, carrier and ordered boundary. -/
theorem chosen_eq_power (i : (M.windows hK).ι) :
    OriginalNativeShadowFirstPrefix.record M hK i =
      powerMarked (rawRecord M hK i) (OriginalNativeShadowInvariantCentre.exponent M hK i) := by
  have h1 := HironakaG11PresClassTransport.pullback_powerMarked
    (M := Amb (M.windows hK).window i) (M' := goodAmbient M hK i)
    contMDiff_subtype_val ((M.windows hK).record i) ((M.windows hK).native i).1.isWellFormed.isCoherent
    (OriginalNativeShadowInvariantCentre.exponent M hK i)
  have h2 := HironakaG11PresClassTransport.pullback_powerMarked
    (M := goodAmbient M hK i) (M' := traceAmbient M hK i)
    contMDiff_subtype_val (rawGoodRecord M hK i) (good_domain M hK i).isWellFormed.isCoherent
    (OriginalNativeShadowInvariantCentre.exponent M hK i)
  have h3 := HironakaG11PresClassTransport.pullback_powerMarked
    (equiv M hK i).contMDiff (rawTraceRecord M hK i) (trace_domain M hK i).isWellFormed.isCoherent
    (OriginalNativeShadowInvariantCentre.exponent M hK i)
  exact (congrArg (fun Q => pullback (equiv M hK i)
    (pullback (M := goodAmbient M hK i) (M' := traceAmbient M hK i) Subtype.val Q)) h1).trans
    ((congrArg (fun Q => pullback (equiv M hK i) Q) h2).trans h3)

theorem chosen_weak_equiv (i : (M.windows hK).ι) :
    WEquiv (rawRecord M hK i) (OriginalNativeShadowFirstPrefix.record M hK i) := by
  rw [chosen_eq_power M hK i]
  exact HironakaG11InvCommonMark.wEquiv_powerMarked _ (raw_domain M hK i)
    (OriginalNativeShadowInvariantCentre.exponent_pos M hK i)

theorem chosen_hs_state (i : (M.windows hK).ι) :
    HSTowerState (OriginalNativeShadowFirstPrefix.record M hK i) ((F).windowCarrier i) H :=
  HSTowerState.of_wEquiv (chosen_weak_equiv M hK i) (raw_native M hK i).hsTowerState

/-- Actual transformed raw record on precisely the chosen physical ambient first head. -/
def rawTransformedRecord (i : (M.windows hK).ι) : MarkedIdeal d (OriginalNativeShadowFirstPrefix.ambient M hK i) :=
  (rawRecord M hK i).geoTransform ((F).centre i) (OriginalNativeShadowFirstPrefix.projection M hK i)

theorem transformed_native (i : (M.windows hK).ι) :
    NativeHSState (rawTransformedRecord M hK i)
      (strictTransform d (OriginalNativeShadowFirstPrefix.projection M hK i) ((F).windowCarrier i)) H := by
  apply (raw_native M hK i).geoTransform ((F).isClosedSubmanifold i) _ (OriginalNativeShadowFirstPrefix.isBlowup M hK i)
  intro y hy
  have hc := ((Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.centre_dictionary M hK i) y).mp hy).1
  exact (Set.ext_iff.mp (chosen_weak_equiv M hK i).cosupp_eq y).mpr hc

theorem transformed_raw_boundary (i : (M.windows hK).ι) :
    (rawTransformedRecord M hK i).E =
      [(OriginalNativeShadowFirstPrefix.projection M hK i) ⁻¹' (F).centre i] := by
  change (rawRecord M hK i).E.map _ ++ [_] = _
  rw [raw_boundary M hK i, List.map_nil, List.nil_append]
  rfl

theorem transformed_cosupp (i : (M.windows hK).ι) :
    (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp =
      (rawTransformedRecord M hK i).cosupp := by
  have ht := (OriginalNativeShadowInvariantCentre.invariant M).toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
    (OriginalNativeShadowFirstPrefix.domain M hK i) _ (OriginalNativeShadowFirstPrefix.canonical M hK i)
  exact ((chosen_weak_equiv M hK i).2 (OriginalNativeShadowFirstPrefix.tower M hK i)).2
    (((chosen_weak_equiv M hK i).2 _).1.mpr ht) |>.symm

private theorem strict_analytic (i : (M.windows hK).ι) :
    IsComplexAnalyticSubset (n := d)
      (strictTransform d (OriginalNativeShadowFirstPrefix.projection M hK i) ((F).windowCarrier i)) :=
  HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (OriginalNativeShadowFirstPrefix.isBlowup M hK i)
    ((OriginalNativeShadowFirstPrefix.manifoldCentres M hK).analytic i)

theorem strict_hs_bound (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left) :
    originalStalkHS (OriginalNativeShadowFirstPrefix.strictSource M hK i) c ≤ H := by
  have hs := (transformed_native M hK i).hsTowerState BlowupTower.refl trivial
  intro ℓ
  exact (originalStalkHS_ofClosedAnalytic (strict_analytic M hK i) c ℓ).trans_le (hs.2.2.1 c.val ℓ)

theorem strict_cosupp_iff (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left) :
    c.val ∈ (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp ↔
      originalStalkHS (OriginalNativeShadowFirstPrefix.strictSource M hK i) c = H := by
  rw [transformed_cosupp M hK i]
  have hs := (transformed_native M hK i).hsTowerState BlowupTower.refl trivial
  constructor
  · intro hc
    funext ℓ
    exact (originalStalkHS_ofClosedAnalytic (strict_analytic M hK i) c ℓ).trans
      ((hs.2.2.2.1 c.val).mp hc ℓ)
  · intro heq
    apply (hs.2.2.2.1 c.val).mpr
    intro ℓ
    exact (originalStalkHS_ofClosedAnalytic (strict_analytic M hK i) c ℓ).symm.trans (congrFun heq ℓ)

theorem strict_cosupp_singular (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left)
    (hc : c.val ∈ (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp) :
    c ∈ intrinsicSingularLocus (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj := by
  have hs := (transformed_native M hK i).hsTowerState BlowupTower.refl trivial
  exact (mem_intrinsicSingularLocus_ofClosedAnalytic_iff (strict_analytic M hK i) c).mpr
    (hs.2.2.2.2 ((Set.ext_iff.mp (transformed_cosupp M hK i) c.val).mp hc))

variable (s : OriginalNativeShadowFirstBlowup.Step M hK)

theorem native_hs_bound (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left) :
    originalStalkHS s.source ((OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base c) ≤ H := by
  have he := originalStalkHS_openImmersion (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i)
    (OriginalNativeShadowFirstPrefix.nativeWindow_isOpenImmersion M hK s i) c
  intro ℓ
  exact (congrFun he ℓ).trans_le (strict_hs_bound M hK i c ℓ)

theorem native_cosupp_iff (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left) :
    c.val ∈ (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp ↔
      originalStalkHS s.source ((OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base c) = H := by
  have he := originalStalkHS_openImmersion (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i)
    (OriginalNativeShadowFirstPrefix.nativeWindow_isOpenImmersion M hK s i) c
  exact ⟨fun hc => he.trans ((strict_cosupp_iff M hK i c).mp hc),
    fun hc => (strict_cosupp_iff M hK i c).mpr (he.symm.trans hc)⟩

theorem native_cosupp_singular (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left)
    (hc : c.val ∈ (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp) :
    (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base c ∈ intrinsicSingularLocus s.source.obj := by
  have he := HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
    (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i)
    (OriginalNativeShadowFirstPrefix.nativeWindow_isOpenImmersion M hK s i)
  exact (Set.ext_iff.mp he c).mpr (strict_cosupp_singular M hK i c hc)

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowRestrictedState
