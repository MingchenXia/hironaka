import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep
import Hironaka.Resolution.StrictTransformComposition

/-! Propagation through the GIVEN full native marked-Q test tower, with
the literal whole differential strictTransform of its actual projection.
Only SOURCE upper/cut/five-law data is input; every target field and actual
whole-singular centre inclusion is derived. Terminal resolution gives true
strict lex HS drop for this SAME Q/T. Extra original function/unit history
and final many-phase/smooth assembly are separate. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeGivenTower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalOriginalSingularReference
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualWeightedCoefficientCompression HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  StrictTransformComposition

variable {m n : ℕ} {X₀ : Type} [TopologicalSpace X₀]
  [ChartedSpace (ComplexModel m) X₀] [IsComplexManifold m X₀]

/-- Every actual given centre lies in the singular locus of the WHOLE
actual differential strict transform at its own actual prefix. -/
def ActualHistoricalNativeTowerCentres {X : CMfd.{0} n} (W : Set X) :
    {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | _,.refl=>True
  | _,.step T C _ _=>ActualHistoricalNativeTowerCentres W T ∧
      C⊆singularSet (n:=n) (strictTransform n T.proj W)

/-- The GIVEN actual full-Q test tower derives ALL target fields and
every whole-current-singular centre from the genuine SOURCE invariant. -/
theorem actual_native_given_test_tower_state
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    {k : ℕ} (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ)
    (hAt : ∀x∈Q.cosupp,ActualHistoricalNativePointPresentation S a w W Q x)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hTest : IsGeoTestTower Q T) :
    (IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj W) ∧
      (geoTransformAlong Q T).N=univ ∧ (geoTransformAlong Q T).ideal.IsCoherent ∧
      (geoTransformAlong Q T).d=weightedCommonMark (fun v : V=>normalExponentDegree v.val) ∧
      (∀z ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj W)) z ℓ≤
        hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ) ∧
      (geoTransformAlong Q T).cosupp={z | ∀ℓ,
        hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ} ∧
      (∀z∈(geoTransformAlong Q T).cosupp,ActualHistoricalNativePointPresentation S a w
        (strictTransform n T.proj W) (geoTransformAlong Q T) z) ∧
      (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) (strictTransform n T.proj W)) ∧
      ActualHistoricalNativeTowerCentres W T := by
  revert hTest
  induction T with
  | refl =>
    intro _hTest
    have hid : strictTransform n (id : X → X) W=W := by
      rw [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hW.isClosed.closure_eq]
    simp only [BlowupTower.proj_refl,geoTransformAlong_refl,hid,ActualHistoricalNativeTowerCentres]
    refine ⟨⟨hW,hQN,hQI,hQMark,hUpper,hCut,hAt,?_⟩,trivial⟩
    intro x hx
    rw [hCut] at hx
    exact actual_original_singular_profile_locus_subset_current_singular W₀ hW₀ a₀ ha₀ W hW hx
  | @step Y Z T C π hπ ih =>
    intro hTest
    obtain ⟨hPrevTest,hCentre⟩:=hTest
    obtain ⟨⟨hPrevW,hPrevN,hPrevI,hPrevMark,hPrevUpper,hPrevCut,hPrevAt,hPrevSing⟩,hHistory⟩:=ih hPrevTest
    have hNext:=actual_native_all_point_stage_step W₀ hW₀ a₀ ha₀
      (strictTransform n T.proj W) hPrevW (geoTransformAlong Q T) hPrevN hPrevI
      S a w hw hPositive hOwn hPrevMark hPrevCut hPrevUpper hPrevAt
      hCentre.1 hCentre.2.1 hπ
    refine ⟨?_,hHistory,hCentre.2.1.trans hPrevSing⟩
    simpa only [BlowupTower.proj_step,geoTransformAlong_step,
      strictTransform_comp T.contMDiff_proj hπ.contMDiff W] using hNext

/-- The GIVEN resolution of the SAME actual full Q strictly lowers the
whole native terminal HS profile. No desired terminal HS/cut is assumed. -/
theorem actual_native_given_resolution_terminal_hs_drop
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    {k : ℕ} (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ)
    (hAt : ∀x∈Q.cosupp,ActualHistoricalNativePointPresentation S a w W Q x)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hResolution : IsGeoResolution Q T) :
    ActualHistoricalNativeTowerCentres W T ∧
      ∀z : Y,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj W)) z)<
        toLex (hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀) := by
  obtain ⟨⟨_hW,_hN,_hI,_hMark,hUpperT,hCutT,_hAt,_hSing⟩,hHistory⟩:=
    actual_native_given_test_tower_state W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPositive
      hOwn hQMark hCut hUpper hAt T hResolution.1
  refine ⟨hHistory,?_⟩
  intro z
  apply lt_of_le_of_ne (Pi.toLex_monotone (hUpperT z))
  intro hEq
  have hProfiles:=congrArg ofLex hEq
  have hz : z∈(geoTransformAlong Q T).cosupp := by
    rw [hCutT]
    exact fun ℓ=>congrFun hProfiles ℓ
  rw [hResolution.2] at hz
  exact notMem_empty z hz

end
end Hironaka.HironakaActualHistoricalNativeGivenTower
