import Hironaka.Resolution.HironakaActualHistoricalNativeFunctionSuccessor
import Hironaka.Resolution.HironakaActualHistoricalNativeGivenTower

/-! SAME original functions at EVERY literal given prefix, with actual
rho0 composed T.proj and common nonzero denominator equations, coupled to
ALL FIVE laws and BOTH whole native W/Q ideals. No future target data and
no new canonical family/tower. Uniform successor windows stay separate. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeFunctionTower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualHistoricalNativeFunctionSuccessor HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualFixedInheritedSelector HironakaActualHistoricalWholeJetFrames
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedCoefficientCompression
  HironakaHolomorphicJetChartInvariance HironakaEmbeddedAnalytic
  HironakaSmoothSubmersionGermIdealColon BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  StrictTransformComposition

variable {m n k : ℕ} {Xref : Type} [TopologicalSpace Xref]
  [ChartedSpace (ComplexModel m) Xref] [IsComplexManifold m Xref]
  {B : Type} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]

/-- Actual original-function data at EVERY literal given prefix and EVERY
actual whole-Q cut point, with the exact actual composed history map. -/
def ActualNativeOriginalFunctionTowerHistory {X : CMfd.{0} n}
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (Q : MarkedIdeal n X)
    (F₀ : V → B → ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ₀ : X → B) (hρ₀ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ₀) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → Prop
  | _,T=>(∀z∈(geoTransformAlong Q T).cosupp,
      ActualHistoricalNativeFunctionPresentation S a w (strictTransform n T.proj W)
        (geoTransformAlong Q T) F₀ hF₀ (ρ₀∘T.proj) (hρ₀.comp T.contMDiff_proj) z) ∧
      match T with
      | .refl=>True
      | .step T _ _ _=>ActualNativeOriginalFunctionTowerHistory S a w W Q F₀ hF₀ ρ₀ hρ₀ T

private theorem history_endpoint {X : CMfd.{0} n}
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (Q : MarkedIdeal n X)
    (F₀ : V → B → ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ₀ : X → B) (hρ₀ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ₀)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (h : ActualNativeOriginalFunctionTowerHistory S a w W Q F₀ hF₀ ρ₀ hρ₀ T) :
    ∀z∈(geoTransformAlong Q T).cosupp,
      ActualHistoricalNativeFunctionPresentation S a w (strictTransform n T.proj W)
        (geoTransformAlong Q T) F₀ hF₀ (ρ₀∘T.proj) (hρ₀.comp T.contMDiff_proj) z := by
  cases T <;> exact h.1

/-- The GIVEN full-Q test tower derives the anchored SAME original
function data at EVERY actual prefix from the genuine SOURCE invariant. -/
theorem actual_native_given_test_tower_original_functions
    (W₀ : Set Xref) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : Xref)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ)
    (F₀ : V → B → ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ₀ : X → B) (hρ₀ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ₀)
    (hAt : ∀x∈Q.cosupp,ActualHistoricalNativeFunctionPresentation S a w W Q F₀ hF₀ ρ₀ hρ₀ x)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hTest : IsGeoTestTower Q T) :
    ActualNativeOriginalFunctionTowerHistory S a w W Q F₀ hF₀ ρ₀ hρ₀ T := by
  have hPoint (x : X) (hx : x∈Q.cosupp) : ActualHistoricalNativePointPresentation S a w W Q x := by
    obtain ⟨Φ,hΦsrc,hΦ0,Γ,_d,hFive,hSpan,hCompression,_hd,_hEq⟩:=hAt x hx
    exact ⟨Φ,hΦsrc,hΦ0,Γ,hFive,hSpan,hCompression⟩
  revert hTest
  induction T with
  | refl =>
    intro _hTest
    have hid : strictTransform n (id : X → X) W=W := by
      rw [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hW.isClosed.closure_eq]
    refine ⟨?_,trivial⟩
    simpa only [BlowupTower.proj_refl,geoTransformAlong_refl,hid,Function.comp_id] using hAt
  | @step Y Z T C π hπ ih =>
    intro hTest
    obtain ⟨hPrevTest,hCentre⟩:=hTest
    have hHistory:=ih hPrevTest
    obtain ⟨⟨hPrevW,hPrevN,hPrevI,hPrevMark,_hPrevUpper,hPrevCut,_hPrevAt,_hPrevSing⟩,_hCentres⟩:=
      actual_native_given_test_tower_state W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPositive
        hOwn hQMark hCut hUpper hPoint T hPrevTest
    refine ⟨?_,hHistory⟩
    intro z hz
    have hSubset : ((geoTransformAlong Q T).geoTransform C π).cosupp⊆
        π ⁻¹' (geoTransformAlong Q T).cosupp:=
      TransformOffCentre.cosupp_geoTransform_subset_preimage (geoTransformAlong Q T)
        (hPrevN ▸ isClosed_univ) (fun _ _ hg=>holomorphicAt_of_mem_coherent _ hPrevI hg) hπ hCentre.2.1
    have hzSource:=hSubset hz
    have hSource:=history_endpoint S a w W Q F₀ hF₀ ρ₀ hρ₀ T hHistory (π z) hzSource
    have hNext:=(actual_native_original_function_successor W₀ hW₀ a₀ ha₀
      (strictTransform n T.proj W) hPrevW (geoTransformAlong Q T) hPrevN hPrevI S a w hw hPositive
      hOwn hPrevMark hPrevCut hCentre.1 hCentre.2.1 hπ z hzSource F₀ hF₀
      (ρ₀∘T.proj) (hρ₀.comp T.contMDiff_proj) hSource).2 hz
    simpa only [BlowupTower.proj_step,geoTransformAlong_step,
      strictTransform_comp T.contMDiff_proj hπ.contMDiff W,Function.comp_assoc] using hNext

end
end Hironaka.HironakaActualHistoricalNativeFunctionTower
