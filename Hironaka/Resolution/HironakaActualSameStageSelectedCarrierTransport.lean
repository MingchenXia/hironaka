import Hironaka.Resolution.HironakaActualSelectedContactCarriers

/-! Recover original marked orders from the SAME actual current square,
then transport actual selected derivative carriers under its SAME chart.
No old-order or desired contact-carrier comparison certificate is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSameStageSelectedCarrierTransport
noncomputable section
open HolGerm HironakaActualCurrentMarkedFunctionSquares
 HironakaActualSelectedContactCarriers HironakaHolomorphicJetChartInvariance
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualOriginalAdaptedMarkedTransport HironakaActualCoefficientPresentationCentrePower
 HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
 HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaRelativeNormalMonomialBasis HironakaActualInheritedSourcePermutationFamily
 HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualInheritedAnalyticBlockJacobian HironakaHolomorphicJetMonomialSpan
 HironakaActualAnalyticBlowupTaylor
 HironakaActualInheritedSourceOwnerPermutation
variable {n : ℕ}

theorem actual_square_member_covariance {ι κ : Type} [Fintype ι] [Fintype κ]
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)} {current : κ → HolGerm (ComplexModel n)}
    {labels : ι≃κ} {C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)}
    {u : HolGerm (ComplexModel n)} (P : ActualMarkedFunctionSquare w old current labels C u) :
    ∀i,C (old i)=u^(w i)*current (labels i) := by
  intro i
  let hComp:=holomorphic_comp P.chart.toFun (local_toFun_holomorphic P.chart)
    P.chart_zero (P.oldHolomorphicAtZero i)
  let hPow:=eventually_differentiableAt_pow P.unitHolomorphicAtZero (w i)
  let hProd:=eventually_differentiableAt_mul hPow (P.currentHolomorphicAtZero (labels i))
  calc
    C (old i)=localGermAlgEquiv P.chart P.chart_zero (old i):=
      congrArg (fun E=>E (old i)) P.chart_germs.symm
    _=HolGerm.mk (P.oldFunctions i ∘ P.chart.toFun) hComp :=
      (congrArg (localGermAlgEquiv P.chart P.chart_zero) (P.oldGerms i)).trans
        (localGermAlgEquiv_mk P.chart P.chart_zero _ _)
    _=HolGerm.mk (fun z=>P.unitFunction z^(w i)*P.currentFunctions (labels i) z) hProd := by
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [P.currentDomain.isOpen.mem_nhds P.zero_mem_current] with z hz
      exact P.memberSquare i z hz
    _=(HolGerm.mk P.unitFunction P.unitHolomorphicAtZero)^(w i)*
        HolGerm.mk (P.currentFunctions (labels i)) (P.currentHolomorphicAtZero (labels i)) := by
      exact (HolGerm.mk_mul _ _ hPow _).trans
        (congrArg (fun a=>a*HolGerm.mk (P.currentFunctions (labels i))
          (P.currentHolomorphicAtZero (labels i))) (HolGerm.mk_pow _ _ _))
    _=u^(w i)*current (labels i):=
      congrArg₂ (·*·) (congrArg (fun a=>a^(w i)) P.unitGerm.symm) (P.currentGerms (labels i)).symm

theorem actual_square_normalized_old_orders
    {m : ℕ} {I : Ideal (HolGerm (ComplexModel (m+1)))}
    {G : ActualAnalyticInheritedFamily (m+1) 0 (analyticZeroTaylorIdeal (m+1) I)}
    {q e f : Fin (m+1)} {b : Fin (m+1) → ℂ} {he : q≤e}
    {hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I))}
    (D : ActualAdaptedCurrentSelectorData I G q e f b S)
    {C : HolGerm (ComplexModel (m+1))≃ₐ[ℂ]HolGerm (ComplexModel (m+1))}
    {u : HolGerm (ComplexModel (m+1))}
    (P : ActualMarkedFunctionSquare (fun a=>normalExponentDegree a.val)
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp)
      D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u) :
    ∀a,sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1)))^normalExponentDegree a.val := by
  intro a
  have hDegree : normalExponentDegree (D.sourceVertexEquiv a).val=normalExponentDegree a.val := by
    rw [D.sourceLabels]
    exact sourceExponentPermutation_degree (normalPivotEquiv q f) a.val
  have hCurrent : D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1)))^normalExponentDegree a.val := by
    change D.targetFamily.germs (sourceVertexSetCast D.targetVertexSet (D.sourceVertexEquiv a))∈_
    rw [D.targetLiterals]
    simpa only [hDegree] using D.sourceOrder (D.sourceVertexEquiv a)
  have hMapped : C (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1)))^normalExponentDegree a.val := by
    rw [actual_square_member_covariance P a]
    exact Ideal.mul_mem_left _ _ hCurrent
  have h:=Ideal.mem_map_of_mem C.symm.toRingEquiv.toRingHom hMapped
  have hMax : Ideal.map C.symm.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1))))=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1))) :=
    IsLocalRing.map_ringEquiv_maximalIdeal C.symm.toRingEquiv
  rw [Ideal.map_pow,hMax] at h
  change C.symm (C (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp a))∈_ at h
  simpa only [AlgEquiv.symm_apply_apply] using h

open HironakaActualInheritedNextBlockGraph HironakaActualCauchyCoefficientLimits
 HironakaActualFixedInheritedSelectorBlowup HironakaActualOriginalTaylorDerivatives
 HironakaActualNormalAllDirectionGeometricConverse

private theorem normalized_same_historical_selector_contact_and_jacobian
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀a,G.germs a∈I)
    (q e : Fin n) (hqe : q≤e) (b : Fin n → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex n I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let H:=sameAnalyticNormalNormalizedVertex n I G q e hqe b hp
    (∀k,actualFixedSelectorContactAt S H k) ∧
      ∀k,actualFixedSelectorJacobian S H k=actualFixedSelectorJacobian S G.germs k := by
  obtain ⟨hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    q e hqe b hp hOrder S hred hadapt
  let H:=sameAnalyticNormalNormalizedVertex n I G q e hqe b hp
  have hDerivative (k) (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k) :
      actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j))=
        actualNormalizedFixedSelectorDerivative G S k (Set.Ici q) e (Set.mem_Ici.mpr hqe) b hpf j := by
    unfold actualFixedSelectorDerivative actualNormalizedFixedSelectorDerivative
    rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_sameAnalyticNormalNormalizedVertex]
  constructor
  · intro k j
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
    rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor]
    have hm:=(hAll k).2.1 j
    rw [←hDerivative k j] at hm
    exact hm
  · intro k
    ext j i
    have heq:=congrArg (fun A=>A j i) ((hAll k).2.2.1)
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j)))=_
    rw [←actualTaylor_coeff_zero,actualTaylor_actualAnalyticCoordinateDerivative,hDerivative k j]
    exact heq

/-- The actual square and current data, together with the actual common
coordinate-flag window, transport ANY fixed representatives of the true
old and current selected derivatives on ONE common neighborhood, for ALL
historical degree prefixes. Old orders/contact/Jacobians are derived. -/
theorem exists_actual_same_stage_selected_carrier_transport
    {m : ℕ} {I : Ideal (HolGerm (ComplexModel (m+1)))}
    {G : ActualAnalyticInheritedFamily (m+1) 0 (analyticZeroTaylorIdeal (m+1) I)}
    {q e f : Fin (m+1)} {b : Fin (m+1) → ℂ} {he : q≤e}
    {hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I))}
    (hmem : ∀a,G.germs a∈I) (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (D : ActualAdaptedCurrentSelectorData I G q e f b S)
    {C : HolGerm (ComplexModel (m+1))≃ₐ[ℂ]HolGerm (ComplexModel (m+1))}
    {u : HolGerm (ComplexModel (m+1))}
    (P : ActualMarkedFunctionSquare (fun a=>normalExponentDegree a.val)
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp)
      D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u)
    (Ω : Set (ComplexModel (m+1))) (hΩ : IsOpen Ω) (h0Ω : (0 : ComplexModel (m+1))∈Ω)
    (hΩP : Ω⊆P.currentDomain)
    (hFlags : ∀k,∀z∈Ω,
      (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (m+1) I)) k,P.chart.toFun z i=0) ↔
      ∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (m+1) (actualAdaptedHistoricalCurrentSource D).ideal)) k,z i=0)
    (fOld : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (m+1) I)) → ComplexModel (m+1) → ℂ)
    (hfOld : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel (m+1)),DifferentiableAt ℂ (fOld j) z)
    (hRepOld : ∀j,HolGerm.mk (fOld j) (hfOld j)=actualFixedSelectorDerivative S
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp) j)
    (fNew : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (m+1) (actualAdaptedHistoricalCurrentSource D).ideal)) → ComplexModel (m+1) → ℂ)
    (hfNew : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel (m+1)),DifferentiableAt ℂ (fNew j) z)
    (hRepNew : ∀j,HolGerm.mk (fNew j) (hfNew j)=actualFixedSelectorDerivative
      (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs j) :
    ∃U : Set (ComplexModel (m+1)),IsOpen U ∧ (0 : ComplexModel (m+1))∈U ∧ U⊆Ω ∧
      MapsTo P.chart.toFun U P.oldDomain ∧
      (∀j,DifferentiableOn ℂ (fNew j) U) ∧
      ∀k,∀z∈U,
        (∀j : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (m+1) I)),j.val∈fixedSelectorBlock
            (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)) k →
              fOld j (P.chart.toFun z)=0) ↔
        ∀j : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal (m+1) (actualAdaptedHistoricalCurrentSource D).ideal)),
          j.val∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
            (analyticZeroTaylorIdeal (m+1) (actualAdaptedHistoricalCurrentSource D).ideal)) k → fNew j z=0 := by
  have hOrder:=actual_square_normalized_old_orders D P
  obtain ⟨hOldContact,hOldJac⟩:=normalized_same_historical_selector_contact_and_jacobian
    I G hmem q e he b hp hOrder S hred hContact
  have hOldDet (k : ℕ) : (actualFixedSelectorJacobian S
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp) k).det≠0 := by
    rw [hOldJac k]
    exact actualFixedSelectorJacobian_det_ne_zero S G.germs G.monic G.lower k
  obtain ⟨Uold,hUold,h0old,hOldSub,_hOldHol,hOldCarriers⟩:=
    exists_actual_selected_contact_flags_neighborhood_of_det S
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e he b hp)
      hOldDet hOldContact fOld hfOld hRepOld P.oldDomain P.oldDomain.isOpen P.zero_mem_old
  obtain ⟨Unew,hUnew,h0new,hNewSub,hNewHol,hNewCarriers⟩:=
    exists_actual_selected_contact_flags_neighborhood
      (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
      D.targetFamily.monic D.targetFamily.lower D.targetContact fNew hfNew hRepNew Ω hΩ h0Ω
  have hCont : ContinuousOn P.chart.toFun Unew :=
    P.chart.toFun_holomorphic.continuousOn.mono
      (fun z hz=>P.inside_chart (hΩP (hNewSub hz)))
  let U:=Unew∩P.chart.toFun⁻¹' Uold
  have hU : IsOpen U:=hCont.isOpen_inter_preimage hUnew hUold
  have h0U : (0 : ComplexModel (m+1))∈U:=⟨h0new,by
    change P.chart.toFun 0∈Uold
    rw [P.chart_zero]
    exact h0old⟩
  refine ⟨U,hU,h0U,(fun _ hz=>hNewSub hz.1),(fun _ hz=>hOldSub hz.2),
    (fun j=>(hNewHol j).mono inter_subset_left),?_⟩
  intro k z hz
  exact (hOldCarriers k (P.chart.toFun z) hz.2).trans
    ((hFlags k z (hNewSub hz.1)).trans (hNewCarriers k z hz.1).symm)

end
end Hironaka.HironakaActualSameStageSelectedCarrierTransport
