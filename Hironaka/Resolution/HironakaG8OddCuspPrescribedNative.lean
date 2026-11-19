import Hironaka.Resolution.HironakaG8OddCuspPrescribedFamily
import Hironaka.Resolution.HironakaActualHistoricalInitialNativePointWindow

/-! Actual historical native state for prescribed cusp polynomial generators. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology MonomialOrder Manifold ContDiff
namespace Hironaka.HironakaG8OddCuspPrescribedNative
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HolGerm OkaRelationSheaf OkaIdealOperations RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient HadamardBridge
  GermIdealOrder IdealWeightPowers OrderTaylor MarkedIdealRestrictOpen
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalInitialNativePointWindow
  HironakaActualHistoricalInitialAffineDictionary HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNativeOpenRestriction HironakaActualHistoricalSortedPrefixFrames
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalHSMarkedDomain
  HironakaActualCompactHSMaximalProfile HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedSmallTails
  HironakaActualOriginalScaledAnalyticDivision HironakaActualInheritedNeighborhoodMarkedHS
  ResolutionInvariantSpec InvDomainTowerAlong NormalCrossings HomogenizedGlueingTower
  HironakaEmbeddedAnalytic SimultaneousNormalCrossings HironakaActualHistoricalPrefixJetFrames
  HironakaActualFixedInheritedSelector HironakaRelativeNormalMonomialBasis
  HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression HironakaActualWeightedNormalPadding
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothSubmersionGermIdealColon
  HironakaG11PresLineState HironakaG8OddCuspPrescribedFamily HironakaG8NativeCuspDiagram
  HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource HironakaG8SameHSCuspContact

/-- Prescribed polynomial weighted record on an open of the displayed
three-dimensional model. -/
def polynomialCuspRecord {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 3) X]
    (p : ℕ) (f : X → ComplexModel 3) : MarkedIdeal 3 X :=
  ⟨univ, [], weightedFunctionIdeal (fun a : cuspV p => normalExponentDegree a.val)
    (fun a x => cuspRepresentative p a (f x)), 2⟩

private theorem positive_labels (p : ℕ) (hp : 2 < p) (a : cuspV p) :
    0 < normalExponentDegree a.val := by
  rcases cuspV_cases hp a with h | h <;> simp [h,normalExponentDegree,Finsupp.single_apply]

private theorem literal_weighted_cosupport {p : ℕ} (hp : 2 < p)
    {A : GermIdeal 3 (ComplexModel 3)} {G : ActualAnalyticInheritedFamily 3 0 (cuspJ p)}
    {R : ℕ → ℕ} (PHS : ActualGeometricInheritedNeighborhoodHS A (embeddedCuspIdeal p) G R)
    (x : presentationOpen PHS) :
    x ∈ (initialWeightedRecord PHS (Subtype.val : presentationOpen PHS → ComplexModel 3) []).cosupp ↔
      ∀ l, hilbertSamuelAt A x.val l = R l := by
  let U := presentationOpen PHS
  let μ := fun a : cuspV p => normalExponentDegree a.val
  let f := fun a (z : U) => PHS.representatives a z.val
  have hf (a) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) (f a) := by
    intro z
    have hh := holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
      (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn a)) z.property
    exact (hh.comp_contMDiff
      (Eventually.of_forall fun _ => (contMDiff_subtype_val (U := U)).contMDiffAt)).mdifferentiableAt
  have hhol (a) : HolomorphicAt 3 (f a) x :=
    holomorphicAt_of_mdifferentiableOn isOpen_univ (hf a).mdifferentiableOn (mem_univ _)
  change x ∈ cosupport 3 univ (weightedFunctionIdeal μ f) (weightedCommonMark μ) ↔ _
  rw [cosupport_weightedFunctionIdeal μ (positive_labels p hp) f hf]
  simp only [mem_iInter]
  constructor
  · intro hx
    apply (PHS.wholeHS x.val x.property).mp
    intro a
    have hv := ((mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit => f a) x (μ a)
      (fun _ => hhol a)).mp (hx a)) ()
    apply (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal x.val _
      (PHS.holomorphicAt _ x.property a) (μ a)).mpr
    have hPow := mem_idealPow_of_vanishesToOrderOn_univ hv
    have hExt := mem_idealPow_pointIdeal_extendOpens U (μ a) hPow
    apply mem_idealPow_congr hExt
    filter_upwards [U.isOpen.mem_nhds x.property] with z hz
    change extendOpens U (f a) (⟨z,hz⟩ : U).val = PHS.representatives a z
    rw [extendOpens_val]
  · intro hHS a
    apply (mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit => f a) x (μ a)
      (fun _ => hhol a)).mpr
    intro _
    have hGerm := ((PHS.wholeHS x.val x.property).mpr hHS) a
    have hPoint := (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal x.val _
      (PHS.holomorphicAt _ x.property a) (μ a)).mp hGerm
    have hPulled := comp_mem_idealPow_pointIdeal
      (φ := (Subtype.val : U → ComplexModel 3)) (u := x)
      (Eventually.of_forall fun z => (contMDiff_subtype_val (U := U) (n := ∞) z).mdifferentiableAt
        (by simp)) (μ a) hPoint
    exact ⟨f a,hPulled,Eventually.of_forall fun _ _ => rfl⟩

/-- The literal polynomial record has one set of standard-basis words,
whole point presentations everywhere on its cosupport and pointwise
upper bounds for the full HS profile. -/
theorem exists_prescribed_polynomial_cusp_native (p : ℕ) (hp : Odd p) (hp2 : 2 < p)
    (B : Opens (ComplexModel 3)) (hB : (0 : ComplexModel 3) ∈ B) :
    ∃ (U : Opens (ComplexModel 3)) (O : Opens U) (x : O),
      x.val.val = 0 ∧ (∀ y : O, y.val.val ∈ B) ∧
      IsInvDomain 3 (polynomialCuspRecord p (fun z : O => z.val.val)) ∧
      NativeHSState (X := CMfd.of (n := 3) O)
        (polynomialCuspRecord p (fun z : O => z.val.val))
        ((fun z : O => z.val.val) ⁻¹' embeddedCuspSet p)
        (hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0) ∧
      x ∈ (polynomialCuspRecord p (fun z : O => z.val.val)).cosupp := by
  let W := embeddedCuspSet p
  let A := vanishingIdeal (n := 3) W
  let R := hilbertSamuelAt A 0
  have hW := embedded_cusp_isAnalytic p
  have hA := CartanIrreducible.cartanCoherence W hW
  obtain ⟨V,hV,hUpper,_⟩ := exists_actual_entire_hs_pointwise_upper_window A hA 0
  let B' : Opens (ComplexModel 3) := ⟨B ∩ V,B.isOpen.inter V.isOpen⟩
  obtain ⟨G,PHS,hSpan,hRed,hContact,hRep,hSub⟩ :=
    exists_cusp_prescribed_family_hs_window p hp hp2 B' ⟨hB,hV⟩
  let U := presentationOpen PHS
  let WU := (Subtype.val : U → ComplexModel 3) ⁻¹' W
  let Q := initialWeightedRecord PHS (Subtype.val : U → ComplexModel 3) []
  let S := actualInitialFixedInheritedSelector (cuspJ p)
  obtain ⟨P,s,hs0,_hs,δ,hBound,_hδ,hOpen,hZero,_hWinSub,hWords,hOwn,hPoints⟩ :=
    exists_actual_initial_native_point_window W hSpan PHS S hRed hContact
      (Subtype.val : U → ComplexModel 3) []
  let O : Opens U := ⟨(Subtype.val : U → ComplexModel 3) ⁻¹' historicalNativeJetWindow P s hs0 δ,
    hOpen.preimage continuous_subtype_val⟩
  let x : O := ⟨⟨0,PHS.zero_mem⟩,hZero⟩
  have hWU : IsComplexAnalyticSubset (n := 3) WU :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
  have hf (a : cuspV p) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ)
      (fun z : U => PHS.representatives a z.val) := by
    rw [hRep]
    exact (cuspRepresentative_differentiable p a).mdifferentiable.comp
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp))
  have hQ : Q.ideal.IsCoherent := isCoherent_weightedFunctionIdeal _ _ hf
  have hNonzero := presentation_weighted_nonzero hW
    (embedded_odd_cusp_singular_at_zero p hp hp2) PHS (positive_labels p hp2)
  have hSNC := isSNCDivisor_nil (n := 3) (M := U)
  have hDomain : IsInvDomain 3 Q := by
    refine ⟨⟨isClosedSubmanifold_univ,hQ,hSNC,isTransverse_univ_of_isSNCDivisor hSNC⟩,
      ?_,hNonzero.1,?_⟩
    · intro z _
      exact ⟨3,le_rfl,EmbeddedFromResolution.regularAtDim_of_mem_nhds (by
        change (univ : Set U) ∈ 𝓝 z
        exact Filter.univ_mem)⟩
    · intro z _
      exact hNonzero.2 z
  have hCut : Q.cosupp = {z : U | ∀ l, hilbertSamuelAt (vanishingIdeal (n := 3) WU) z l = R l} := by
    apply Set.ext
    intro z
    simp only [WU,hilbertSamuelAt_vanishing_actual_open_any]
    exact literal_weighted_cosupport hp2 PHS z
  let QT := MarkedIdeal.pullback (Subtype.val : O → U) Q
  have hQT := GermIdealPullbackCalculus.isCoherent_pullback
    (contMDiff_subtype_val (U := O) (n := ∞)) hQ
  have hCosT : QT.cosupp = (Subtype.val : O → U) ⁻¹' Q.cosupp :=
    cosupp_pullback_val Q (fun _ _ hg => holomorphicAt_of_mem_coherent Q.ideal hQ hg) O
  let aFull := (historicalDegreeFullLabelEquiv (actualVertexWords 3 (embeddedCuspIdeal p))
    P.germs.degreeBound hBound).trans (actualVertexEnumeration 3 (embeddedCuspIdeal p))
  let wFull := historicalDegreePrefixWords (actualVertexWords 3 (embeddedCuspIdeal p)) P.germs.degreeBound
  have hState : NativeHSState (X := CMfd.of (n := 3) O) QT ((Subtype.val : O → U) ⁻¹' WU) R := by
    refine ⟨⟨3, CMfd.of (n := 3) (ComplexModel 3), W, 0, hW,
      embedded_odd_cusp_singular_at_zero p hp hp2, rfl⟩,
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWU,
      preimage_univ, hQT, cuspV p, S, _, aFull, wFull, hWords, positive_labels p hp2,
      hOwn, rfl, ?_, ?_, ?_⟩
    · rw [hCosT,hCut]
      ext z
      simp only [mem_preimage,mem_ofPred_eq,hilbertSamuelAt_vanishing_actual_open_any]
    · intro z l
      rw [hilbertSamuelAt_vanishing_actual_open_any, hilbertSamuelAt_vanishing_actual_open_any]
      exact hUpper _ (hSub z.val.property).2 l
    · intro z hz
      have hBase : z.val ∈ Q.cosupp := by
        rw [hCosT] at hz
        exact hz
      have hEq : ∀ l, hilbertSamuelAt (vanishingIdeal (n := 3) WU) z.val l = R l := by
        rw [hCut] at hBase
        exact hBase
      exact actual_native_point_presentation_open_restriction S aFull wFull WU
        (CartanIrreducible.cartanCoherence WU hWU) Q hQ O z (hPoints z.val z.property hEq)
  have hExact : QT = polynomialCuspRecord p (fun z : O => z.val.val) := by
    have hIdeal : QT.ideal = (polynomialCuspRecord p (fun z : O => z.val.val)).ideal := by
      change GermIdeal.pullback (m := 3) (Subtype.val : O → U)
        (weightedFunctionIdeal _ (fun a (z : U) => PHS.representatives a z.val)) = _
      let μ := fun a : cuspV p => normalExponentDegree a.val
      let c := fun (a : cuspV p) (z : U) =>
        PHS.representatives a z.val ^ (weightedCommonMark μ / μ a)
      change GermIdeal.pullback (m := 3) (Subtype.val : O → U) (finiteFunctionIdeal c) = _
      have hC (a : cuspV p) : MDifferentiable 𝓘(ℂ,ComplexModel 3) 𝓘(ℂ,ℂ) (c a) :=
        (hf a).pow _
      rw [finiteFunctionIdeal_pullback c hC _ contMDiff_subtype_val]
      simp only [c,hRep]
      rfl
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl hIdeal
      (embedded_cusp_native_mark p hp2)
  have hxQ : x ∈ QT.cosupp := by
    rw [hCosT]
    exact (literal_weighted_cosupport hp2 PHS x.val).mpr (fun _ => rfl)
  exact ⟨U,O,x,rfl,fun y => (hSub y.val.property).1,hExact ▸ isInvDomain_pullback_val O hDomain,
    hExact ▸ hState,hExact ▸ hxQ⟩

end
end Hironaka.HironakaG8OddCuspPrescribedNative
