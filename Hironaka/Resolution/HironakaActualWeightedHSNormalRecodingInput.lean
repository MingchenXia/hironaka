import Hironaka.Resolution.HironakaActualWeightedHSNormalInput
import Hironaka.Resolution.HironakaActualWeightedNormalContact
import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary

/-! Entire first recodings and original-source nonzero for the SAME literal
weighted HS normal padding. No composite recoding or CAN is assumed.
Blueprint: hironaka-actual-weighted-hs-normal-recoding-input-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualWeightedHSNormalRecodingInput
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  GermIdealOrder IdealWeightPowers IdealOrderArithmetic DerivativeIdeal BlowupDerivativeIdeal
  DerivativeIdealAlong HomogenizedGlueing HomogenizedEquivalence HomogenizedIdealAlong CoefficientIdeal
  MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalContact
  HironakaActualWeightedHSNormalInput HironakaActualWeightedNormalPadding
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualZeroCoordinateContactSeed HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalInitialAffineDictionary HironakaActualHistoricalHSMarkedDomain
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  OkaIdealOperations ResolutionInvariantSpec DivisorExponentAlong

variable {n : ℕ}

private theorem normal_padding_coherent {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    (normalPaddingIdeal I d).IsCoherent :=
  RestrictedIdealExtension.isCoherent_sumIdeal
    (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _ => (normalCoordinate_mdifferentiable U).pow d))

/-- ENTIRE homogenized trace at the SAME positive original mark. -/
theorem normal_padding_homogenized_trace {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) {d : ℕ} (hd : 0<d) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (HomogenizedIdeal.homogenizedIdeal (normalPaddingIdeal I d) d)=
      HomogenizedIdeal.homogenizedIdeal I d := by
  have hJ:=normal_padding_coherent hI d
  rw [homogenizedIdeal_eq_homSum,homogenizedIdeal_eq_homSum]
  unfold homSum
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal (zeroSection_contMDiff U)
    _ d (fun i _ => isCoherent_mul (isCoherent_iterDerivIdeal hJ i)
      (isCoherent_idealPow (isCoherent_iterDerivIdeal hJ (d-1)) i))]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdeal hJ i) (isCoherent_idealPow (isCoherent_iterDerivIdeal hJ (d-1)) i),
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
      (isCoherent_iterDerivIdeal hJ (d-1)),
    entire_ambient_derivative_trace hI hi,
    entire_ambient_derivative_trace hI (show d-1<d by omega)]

/-- ENTIRE coefficient trace of the ORIGINAL padded ideal, including d=0. -/
theorem normal_padding_coefficient_trace {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdeal (normalPaddingIdeal I d) i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdeal I i) (sumExp (fun j => d-j) d i)) d := by
  have hJ:=normal_padding_coherent hI d
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal (zeroSection_contMDiff U)
    _ d (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdeal hJ i) _)]
  apply finSumIdeal_congr
  intro i hi
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
    (isCoherent_iterDerivIdeal hJ i),entire_ambient_derivative_trace hI hi]

variable {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

private theorem presentation_functions_mdifferentiable
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS => PHS.representatives i z.val) := by
  intro z
  have h:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (h.comp_contMDiff (Eventually.of_forall fun _ =>
    (contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

/-- All four homogenized fields restrict to the literal ORIGINAL weighted Q. -/
theorem phase_normal_homogenized_record
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    markedPullback (m:=n) (zeroSection (presentationOpen PHS))
      (homMarkedAlong (phaseNormalMarked PHS η E))=
      homMarkedAlong (initialWeightedRecord PHS η E) := by
  let Q:=initialWeightedRecord PHS η E
  have hQ : Q.ideal.IsCoherent:=
    isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hJ : (phaseNormalMarked PHS η E).ideal.IsCoherent:=
    normal_padding_coherent hQ Q.d
  rw [homMarkedAlong_eq_homMarked rfl (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hJ h),
    homMarkedAlong_eq_homMarked rfl (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hQ h)]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_
    (normal_padding_homogenized_trace hQ (weightedCommonMark_pos _ hw)) rfl
  change (markedPullback (m:=n) (zeroSection (presentationOpen PHS))
    (phaseNormalMarked PHS η E)).E=(initialWeightedRecord PHS η E).E
  exact congrArg (fun K : MarkedIdeal n (presentationOpen PHS) => K.E)
    (phase_normal_zero_section_record PHS hw η E)

/-- All original slots and the literal coefficient product mark are retained. -/
theorem phase_normal_coefficient_record
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    markedPullback (m:=n) (zeroSection (presentationOpen PHS))
      (coeffMarkedAlong (phaseNormalMarked PHS η E))=
      coeffMarkedAlong (initialWeightedRecord PHS η E) := by
  let Q:=initialWeightedRecord PHS η E
  have hQ : Q.ideal.IsCoherent:=
    isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hJ : (phaseNormalMarked PHS η E).ideal.IsCoherent:=
    normal_padding_coherent hQ Q.d
  rw [coeffMarkedAlong_eq_coeffMarked rfl (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hJ h),
    coeffMarkedAlong_eq_coeffMarked rfl (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hQ h)]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_
    (normal_padding_coefficient_trace hQ Q.d) rfl
  change (markedPullback (m:=n) (zeroSection (presentationOpen PHS))
    (phaseNormalMarked PHS η E)).E=(initialWeightedRecord PHS η E).E
  exact congrArg (fun K : MarkedIdeal n (presentationOpen PHS) => K.E)
    (phase_normal_zero_section_record PHS hw η E)

/-- The SAME actual phase padding has genuine contact at its original mark. -/
theorem phase_normal_contact (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    TangentDirectionAlong.IsTangentDirectionAlong univ (phaseNormalMarked PHS η E).ideal
      (phaseNormalMarked PHS η E).d univ (relativeNormalCoordinate (presentationOpen PHS)) := by
  rw [←phase_normal_weighted_record PHS η E]
  exact weighted_padding_contact _ _ hw _ (presentation_functions_mdifferentiable PHS) _

private theorem weighted_function_ideal_le {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type*} [Fintype ι] (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→X→ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    {J : GermIdeal n X} (hJ : J.IsCoherent) (hMem : ∀x i,J.mem x (c i)) :
    (weightedFunctionIdeal w c).Le J := by
  intro x F hF
  apply HomogenizedIdeal.mem_of_isInSpanAt hJ
  refine IsInSpanAt.trans ?_ hF
  rintro _ ⟨i,rfl⟩
  have hHol : HolomorphicAt n (c i) x:=Eventually.of_forall (fun y => hc i y)
  have he:=compressionExponent_pos w hw i
  apply isInSpanAt_of_eq_mul (hMem x i) (holomorphicAt_pow hHol _)
    (holomorphicAt_pow hHol (weightedCommonMark w/w i-1))
  exact Eventually.of_forall (fun z => by
    change c i z^(weightedCommonMark w/w i)=c i z^(weightedCommonMark w/w i-1)*c i z
    rw [←pow_succ,show weightedCommonMark w/w i-1+1=weightedCommonMark w/w i by omega])

/-- The whole literal powered ideal lies in the SAME entire native source ideal. -/
theorem phase_ideal_le_native_source
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    (initialWeightedRecord PHS η E).ideal.Le
      (GermIdeal.pullback (m:=n) (Subtype.val : presentationOpen PHS→ComplexModel n) A) := by
  apply weighted_function_ideal_le _ hw _ (presentation_functions_mdifferentiable PHS)
    (actual_initial_presentation_native_coherent PHS)
  intro x i
  have hRep : A.mem x.val (PHS.representatives i):=
    (PHS.wholeGeneration x.val x.property _).mpr
      (inSpanAt_self (PHS.holomorphicAt x.val x.property) i)
  have hHol : HolomorphicAt n (fun z : presentationOpen PHS => PHS.representatives i z.val) x:=
    Eventually.of_forall (fun y => presentation_functions_mdifferentiable PHS i y)
  exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨PHS.representatives i,hRep,rfl⟩ hHol)

/-- Original domain nonzero supplies the SAME actual native nonzero witness. -/
theorem phase_native_source_nonzero
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) {k : ℕ}
    (hQ : IsInvDomain k (initialWeightedRecord PHS η E)) :
    ∀x : presentationOpen PHS,IsNonzeroAlongAt (n:=n) univ
      (GermIdeal.pullback (m:=n) (Subtype.val : presentationOpen PHS→ComplexModel n) A) x := by
  intro x
  obtain ⟨g,hg,hFreq⟩:=hQ.isNonzeroAlongAt x (mem_univ _)
  exact ⟨g,phase_ideal_le_native_source PHS hw η E x g hg,hFreq⟩

end
end Hironaka.HironakaActualWeightedHSNormalRecodingInput
