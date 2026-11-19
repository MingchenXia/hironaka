import Hironaka.Resolution.HironakaActualHistoricalFunctionEquations
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep
import Hironaka.Resolution.HironakaActualHistoricalNativeOpenRestriction

/-! SAME ORIGINAL native functions and literal current map are retained by
the actual historical successor. ONE nonzero common analytic denominator
records controlled exceptional division; it is not called an invertible unit.
The native source-compatible chart and SAME normalized N produce all five
laws, both whole W/Q ideals and exact original function equations together. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeFunctionSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalFunctionEquations HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNativeOpenRestriction
  HironakaActualHistoricalNativeCompatibleSource HironakaActualHistoricalNativeControlledSuccessor
  HironakaActualHistoricalOffCentreSuccessor HironakaActualHistoricalOriginalSingularReference
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalMovingCentreChart
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedCoefficientCompression
  HironakaActualOriginalFormalHSTransfer HironakaActualAnalyticBlowupTaylor
  HironakaSmoothSubmersionGermIdealColon HironakaActualNativeSourceChartComposition
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic MarkedIdeals

variable {n k : ℕ} {B X Y : Type}
  [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Real native five-law/whole-ideal data anchored to ONE fixed original
function family and the actual current projection, with one nonzero
common analytic denominator and exact WHOLE equations for EVERY label. -/
def ActualHistoricalNativeFunctionPresentation
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (Q : MarkedIdeal n X)
    (F₀ : V → B → ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ : X → B) (hρ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ) (x : X) : Prop :=
  ∃(Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (_hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (Γ : V → HolGerm (ComplexModel n)) (d : HolGerm (ComplexModel n)),
    ActualHistoricalFivePointLaws S a w Γ ∧
    Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0) ∧
    adaptedIdeal Q.ideal x Φ hΦ0=weightedCompression (fun v : V=>normalExponentDegree v.val) Γ ∧
    d≠0 ∧ ∀v,adaptedGerm x Φ hΦ0 (F₀ v∘ρ)
      ((hF₀ v (ρ x)).comp_contMDiff (Filter.Eventually.of_forall fun _=>hρ.contMDiffAt))=
        d^normalExponentDegree v.val*Γ v

/-- A genuine actual successor retains the SAME original functions and
composes the actual map, with its one common denominator derived internally. -/
theorem actual_native_original_function_successor
    {m : ℕ} {Xref : Type} [TopologicalSpace Xref]
    [ChartedSpace (ComplexModel m) Xref] [IsComplexManifold m Xref]
    (W₀ : Set Xref) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : Xref)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    {C : Set X} (hC : IsClosedSubmanifold n C) (hCcut : C⊆Q.cosupp)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hzSource : π z∈Q.cosupp)
    (F₀ : V → B → ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ : X → B) (hρ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ)
    (hAt : ActualHistoricalNativeFunctionPresentation S a w W Q F₀ hF₀ ρ hρ (π z)) :
    (z∈(Q.geoTransform C π).cosupp ↔
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
    (z∈(Q.geoTransform C π).cosupp →
      ActualHistoricalNativeFunctionPresentation S a w (strictTransform n π W) (Q.geoTransform C π)
        F₀ hF₀ (ρ∘π) (hρ.comp hπ.contMDiff) z) := by
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,d,hFive,hSpan,hCompression,hd,hEq⟩:=hAt
  let F:=fun v=>F₀ v∘ρ
  have hF (v : V) : HolomorphicAt n (F v) (π z):=
    (hF₀ v (ρ (π z))).comp_contMDiff (Filter.Eventually.of_forall fun _=>hρ.contMDiffAt)
  by_cases hzC : π z∈C
  · obtain ⟨c,hReg⟩:=hC.2 (π z) hzC
    obtain ⟨_hSing,hCodim,hHSConst⟩:=actual_original_reference_current_cut_centre_geometry
      W₀ hW₀ a₀ ha₀ W hW Q hCut C hCcut (π z) c hReg
    choose f hf hRep using fun v=>HolGerm.exists_eq_mk (Γ v)
    obtain ⟨U,_h0U,_hUT,_hfU,_hRecord,O,_hO,_h0O,_hOU,hSources⟩:=
      exists_actual_native_historical_compatible_source_chart (π z) Φ hΦsrc hΦ0 W
        (CartanIrreducible.cartanCoherence W hW) S Γ a w hw hPositive hFive hSpan
        Q hQN hQI hCompression hQMark f hf hRep
    obtain ⟨D,hΨsrc,hFlat,hFiveD,_hJacD,hSpanD,hCompD,hHeadsD,hCentreD⟩:=hSources C c hReg hCcut
    let Ψ:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D.chart hΦ0
    let hΨ0:=(actual_native_source_chart_comp_geometry (π z) Φ hΦsrc hΦ0 D.chart D.chart_zero).2
    let E:=(localGermAlgEquiv D.chart D.chart_zero).symm
    let p:=D.priorityPermutation.trans (finCongr D.dimension)
    have hEqD:=actual_function_equations_compose_source_chart (π z) Φ hΦsrc hΦ0 D.chart D.chart_zero
      (fun v : V=>normalExponentDegree v.val) F hF Γ d hd hEq
    obtain ⟨e,b,Θ,hΘ0,N,_he,hΘsrc,_hbT,_hbe,_hBound,hSquare,hProduct,_hLe,_hDrop,
      _hCoherent,hTargetCompression,hCutLocal,hPoint,_hWindow⟩:=
      exists_actual_native_same_historical_controlled_successor hπ z c hCodim p Ψ hΨsrc hΨ0 hFlat W hC hW
        hHSConst S (fun v=>E (Γ v)) a w hw hPositive hOwn hSpanD hFiveD hHeadsD hCentreD
          Q hQN hQI hCompD hQMark
    have hEqN:=actual_function_equations_blowup_square π hπ.contMDiff z
      {i : Fin n | c≤(p i).val} e b Ψ hΨsrc hΨ0 Θ hΘsrc hΘ0 hSquare
      (fun v : V=>normalExponentDegree v.val) F hF (fun v=>E (Γ v)) N (E d) hEqD.1 hEqD.2 hProduct
    refine ⟨hCutLocal,?_⟩
    intro hz
    have hPointAt:=hPoint hz
    refine ⟨Θ,hΘsrc,hΘ0,N,actualAnalyticBlowupPullback {i : Fin n | c≤(p i).val} e b (E d)*
      HironakaHolomorphicJetMonomialSpan.coordinateGerm e,hPointAt.2.2.1,?_,hTargetCompression,hEqN.1,hEqN.2⟩
    exact (congrArg Ideal.span (a.surjective.range_comp N)).trans hPointAt.2.2.2.2.symm
  · obtain ⟨Θ,hΘ0,hΘsrc,hSquare,_hCoherent,hTargetCompression,hHS,hOffCut,hFiveSame,hStrictSpan,_hWindow⟩:=
      exists_actual_native_same_historical_off_centre_successor hπ z hzC Φ hΦsrc hΦ0 W hW S Γ a w
        hFive hSpan Q hQN hQI hCompression hQMark
    have hIdSquare:=fun y hy hyΘ=>(hSquare y hy hyΘ).2
    have hEqSame:=actual_function_equations_identity_square π hπ.contMDiff z Φ hΦ0 Θ hΘsrc hΘ0
      hIdSquare (fun v : V=>normalExponentDegree v.val) F hF Γ d hEq
    refine ⟨⟨fun _=>hHS,fun _=>hOffCut.mpr hzSource⟩,?_⟩
    intro _hz
    exact ⟨Θ,hΘsrc,hΘ0,Γ,d,hFiveSame,
      (congrArg Ideal.span (a.surjective.range_comp Γ)).trans hStrictSpan.symm,
      hTargetCompression,hd,hEqSame⟩

/-- The LITERAL phase-open restriction keeps the SAME original functions
and common denominator, with the actual source map composed by inclusion. -/
theorem actual_native_original_function_open_restriction
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (hW : (vanishingIdeal (n:=n) W).IsCoherent)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent) (O : TopologicalSpace.Opens X) (x : O)
    (F₀ : V → B → ℂ) (hF₀ : ∀v y,HolomorphicAt n (F₀ v) y)
    (ρ : X → B) (hρ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ)
    (hAt : ActualHistoricalNativeFunctionPresentation S a w W Q F₀ hF₀ ρ hρ x.val) :
    ActualHistoricalNativeFunctionPresentation S a w ((Subtype.val : O → X) ⁻¹' W)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) Q)
      F₀ hF₀ (ρ∘(Subtype.val : O → X)) (hρ.comp contMDiff_subtype_val) x := by
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,d,hFive,hSpan,hCompression,hd,hEq⟩:=hAt
  let Θ:=actualNativeOpenChart O x Φ
  have hΘsrc:=(actual_native_open_chart_geometry O x Φ hΦ0).1
  have hΘ0:=(actual_native_open_chart_geometry O x Φ hΦ0).2
  have hWOpen : (vanishingIdeal (n:=n) ((Subtype.val : O → X) ⁻¹' W)).IsCoherent := by
    rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hW
  have hWhole:=actual_native_open_adapted_ideal (vanishingIdeal (n:=n) W) hW O x Φ hΦ0
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hWhole
  have hOldOrigin:=actual_original_translated_flattened_vanishing_origin_eq_adapted
    x.val Φ hΦsrc hΦ0 W hW
  have hNewOrigin:=actual_original_translated_flattened_vanishing_origin_eq_adapted
    x Θ hΘsrc hΘ0 ((Subtype.val : O → X) ⁻¹' W) hWOpen
  refine ⟨Θ,hΘsrc,hΘ0,Γ,d,hFive,?_,?_,hd,?_⟩
  · exact hSpan.trans (hOldOrigin.trans (hWhole.symm.trans hNewOrigin.symm))
  · exact (actual_native_open_adapted_ideal Q.ideal hQI O x Φ hΦ0).trans hCompression
  · intro v
    have hF : HolomorphicAt n (F₀ v∘ρ) x.val:=
      (hF₀ v (ρ x.val)).comp_contMDiff (Filter.Eventually.of_forall fun _=>hρ.contMDiffAt)
    exact (actual_native_open_adapted_germ O x Φ hΦ0 (F₀ v∘ρ) hF).trans (hEq v)

end
end Hironaka.HironakaActualHistoricalNativeFunctionSuccessor
