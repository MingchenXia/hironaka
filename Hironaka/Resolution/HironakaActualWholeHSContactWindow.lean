import Hironaka.Resolution.HironakaActualSameStageSelectedCarrierTransport

/-! The SAME actual whole-neighborhood HS presentation puts its ENTIRE true
reference stratum in EVERY actual selected contact carrier, on ONE open.
No desired centre containment, rank or Jacobian certificate is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWholeHSContactWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
 HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
 HironakaActualGeometricCurrentNeighborhoodHS HironakaActualSelectedContactCarriers
 HironakaActualFixedInheritedSelector HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualCauchyCoefficientLimits
 HironakaActualOriginalTaylorDerivatives
 HironakaActualNormalZeroAnalyticSaturation HironakaActualHSConstantCentreJetFrames
 HironakaActualInheritedDiagramJetPivot HolomorphicTaylorTail
 HironakaActualAnalyticFormalNormalPowers HironakaRelativeNormalTaylorCoefficients
 HironakaHolomorphicJetQuotientFrames
variable {n : ℕ}

/-- The literal degree-prefix zero set of one fixed representative family.
When its germs are the historical selected derivatives, this is their actual
selected contact carrier; the functions do not vary with the cutoff. -/
def actualSelectedRepresentativeCarrier {V : Finset (Fin n →₀ ℕ)}
    (F : fixedSelectorEssential V → ComplexModel n → ℂ) (k : ℕ) : Set (ComplexModel n) :=
  {z | ∀j : fixedSelectorEssential V,j.val∈fixedSelectorBlock V k → F j z=0}


/-- A transparent output property for the literal old/current germ families,
selectors, function map and whole-HS domain. All comparisons are conclusions;
this property is never a premise of the geometric producer below. -/
def ActualSelectedContactWindowLaws
    {VO VN : Finset (Fin n →₀ ℕ)}
    (SO : ActualFixedInheritedSelector VO) (GO : VO → HolGerm (ComplexModel n))
    (SN : ActualFixedInheritedSelector VN) (GN : VN → HolGerm (ComplexModel n))
    (A : GermIdeal n (ComplexModel n)) (R : ℕ → ℕ)
    (φ : ComplexModel n → ComplexModel n) (Ω : Set (ComplexModel n)) : Prop :=
  ∀(fOld : fixedSelectorEssential VO → ComplexModel n → ℂ)
    (hfOld : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fOld j) z),
    (∀j,HolGerm.mk (fOld j) (hfOld j)=actualFixedSelectorDerivative SO GO j) →
  ∀(fNew : fixedSelectorEssential VN → ComplexModel n → ℂ)
    (hfNew : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fNew j) z),
    (∀j,HolGerm.mk (fNew j) (hfNew j)=actualFixedSelectorDerivative SN GN j) →
  ∃V : Set (ComplexModel n),IsOpen V ∧ (0 : ComplexModel n)∈V ∧ V⊆Ω ∧
    (∀k,∀z∈V,φ z∈actualSelectedRepresentativeCarrier fOld k ↔
      z∈actualSelectedRepresentativeCarrier fNew k) ∧
    ∀z∈V,(∀ℓ,hilbertSamuelAt A z ℓ=R ℓ) →
      (∀j,fNew j z=0) ∧ (∀k,∀i∈fixedSelectorBlock VN k,z i=0) ∧
      ∀k,φ z∈actualSelectedRepresentativeCarrier fOld k

/-- ANY fixed SAME-germ selected derivative representatives vanish on the
ENTIRE actual whole HS reference stratum on ONE requested common open.
The actual presentation functions, source family and selector are retained. -/
theorem exists_actual_whole_hs_selected_derivative_window
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (f : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) →
      ComplexModel n → ℂ)
    (hf : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (f j) z)
    (hRep : ∀j,HolGerm.mk (f j) (hf j)=actualFixedSelectorDerivative S G.germs j)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆P.neighborhood ∧ U⊆O ∧
      ∀z∈U,(∀ℓ,hilbertSamuelAt A z ℓ=R ℓ) → ∀j,f j z=0 := by
  have hOne (j : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))) :
      ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈P.neighborhood →
        (∀ℓ,hilbertSamuelAt A z ℓ=R ℓ) → f j z=0 := by
    let a:=S.selected j
    let β:=fixedSelectorBeta S j
    have hβ : normalExponentDegree β<normalExponentDegree a.val := by
      have h : normalExponentDegree β+1=normalExponentDegree a.val:=fixedSelector_beta_degree S j
      omega
    obtain ⟨w,hw⟩:=exists_actualJetWordExponent (normalExponentDegree a.val) β hβ
    let L:=(List.ofFn w.2).map (fun i=>EuclideanSpace.single i (1 : ℂ))
    let F:=iterDeriv L (P.representatives a)
    have hF : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F z:=
      eventually_holomorphic_iterDeriv (P.holomorphicAtZero a) L
    have hword : actualAnalyticMultiDerivative β (G.germs a)=
        actualAnalyticWordDerivative (List.ofFn w.2) (G.germs a) := by
      apply actualUnshiftedTaylorAlgHom_injective n
      rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_actualAnalyticWordDerivative,
        show actualCoordinateWordExponent (List.ofFn w.2)=β from hw]
    have hEq : HolGerm.mk (f j) (hf j)=HolGerm.mk F hF := by
      rw [hRep]
      change actualAnalyticMultiDerivative β (G.germs a)=_
      rw [hword,←P.sameGerms a,actualAnalyticWordDerivative,iteratedDerivativeGerm_mk]
    filter_upwards [HolGerm.mk_eq_mk_iff.mp hEq] with z hz hzP hHS
    have hOrder:=(P.wholeHS z hzP).mpr hHS a
    have hJet : scalarJet (normalExponentDegree a.val)
        (translatedGerm z (P.representatives a) (P.holomorphicAt z hzP a))=0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_scalarJet]
      exact hOrder
    have hEntry:=congrFun hJet w
    rw [scalarJet_translatedGerm_eq_iterDeriv] at hEntry
    exact hz.trans hEntry
  have hAll:=eventually_all.mpr hOne
  obtain ⟨B,hBsub,hB,h0B⟩:=mem_nhds_iff.mp hAll
  refine ⟨B∩(P.neighborhood∩O),hB.inter (P.isOpen_neighborhood.inter hO),
    ⟨h0B,P.zero_mem,h0O⟩,(fun _ hz=>hz.2.1),(fun _ hz=>hz.2.2),?_⟩
  intro z hz hHS j
  exact hBsub hz.1 j hz.2.1 hHS

/-- On ONE common open, the actual whole HS reference stratum lies in ALL
literal historical coordinate-prefix planes and all true selected carriers. -/
theorem exists_actual_whole_hs_coordinate_contact_window
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (f : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) →
      ComplexModel n → ℂ)
    (hf : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (f j) z)
    (hRep : ∀j,HolGerm.mk (f j) (hf j)=actualFixedSelectorDerivative S G.germs j)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆P.neighborhood ∧ U⊆O ∧
      ∀z∈U,(∀ℓ,hilbertSamuelAt A z ℓ=R ℓ) → (∀j,f j z=0) ∧
        ∀k,∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal n I)) k,z i=0 := by
  obtain ⟨Uhs,hUhs,h0hs,hHsSub,hHsO,hZeros⟩:=
    exists_actual_whole_hs_selected_derivative_window P S f hf hRep O hO h0O
  obtain ⟨V,hV,h0V,hVsub,_hHol,hCarrier⟩:=
    exists_actual_selected_contact_flags_neighborhood S G.germs G.monic G.lower
      hContact f hf hRep Uhs hUhs h0hs
  refine ⟨V,hV,h0V,(fun _ hz=>hHsSub (hVsub hz)),
    (fun _ hz=>hHsO (hVsub hz)),?_⟩
  intro z hz hHS
  have hZero:=hZeros z (hVsub hz) hHS
  exact ⟨hZero,fun k=>(hCarrier k z hz).mp (fun j _=>hZero j)⟩

open Hironaka.BlowupSequences HironakaActualSameCurrentGeometricStage
 HironakaActualSameStageSelectedCarrierTransport HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualCurrentMarkedFunctionSquares
 HironakaActualGeometricMarkedSquare HironakaActualControlledNeighborhoodGenerators
 HironakaActualNormalMarkedDirection HironakaActualAnalyticBlowupTaylor
 HironakaActualFiniteCoefficientIdeals HironakaActualCoefficientAnalyticBlowup
 HironakaActualOriginalAdaptedMarkedTransport HironakaRelativeNormalDeformationInitialRelations
 HironakaActualInheritedSourcePermutationFamily BlowupControlledTransform
 MarkedIdeals.MarkedIdeal InvertibleIdealQuotient
 MarkedIdeals GermIdealOrder HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualGlobalInheritedCut HironakaActualGeometricAdaptedCurrentFamily
 HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
 HironakaActualFixedFlatteningHSComparison HironakaActualSingularChartTransport
 MarkedIdealBiholomorphism HironakaActualWeightedCoefficientCompression
 HironakaActualCoherentWeightedCoefficientMarked

/-- Original geometric inputs internally produce the SAME whole stage and
ALL selected carrier comparisons and actual next HS-centre contact laws. -/
theorem exists_actual_geometric_stage_selected_contact_centres
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+2))) Z] [IsComplexManifold (d+(t+2)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+2)))) (h0U : (0 : ComplexModel (d+(t+2)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
      ComplexModel (d+(t+2)) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+(t+2))))∩complexCoordinatePlane (d+(t+2)) d⊆
      cosupport (d+(t+2)) univ (actualPrincipalCoefficientIdeal (d+(t+2)) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+2)) ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+2)))=0)
    (W : Set U) (hWa : IsComplexAnalyticSubset (n:=d+(t+2)) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+(t+2)))))
    (hOrigin : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0)) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    y∈Q.cosupp →
    ∃(e : Fin (d+(t+2)))(b : Fin (d+(t+2)) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
        chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
        (π z : ComplexModel (d+(t+2)))=actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      ∃u : HolGerm (ComplexModel (d+(t+2))),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (d+(t+2))))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2))
            (strictTransform (d+(t+2)) π W)) y Θ) 0)
        let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
        let A₀:=vanishingIdeal (n:=d+(t+2))
          (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
        let A:=GermIdeal.pullback (m:=d+(t+2)) P.chart.toFun A₀
        J=Ideal.map C.toRingEquiv.toRingHom K ∧ J=originalCoherentOriginIdeal A ∧
        ∃PHS : ActualGeometricInheritedNeighborhoodHS A J D.targetFamily (hilbertSamuelValue I),
          PHS.representatives=P.currentFunctions ∧ PHS.neighborhood⊆P.currentDomain ∧
          MapsTo P.chart.toFun PHS.neighborhood Θ.target ∧
          (∀k,∀z∈PHS.neighborhood,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) (sameAnalyticZeroNormalizedIdeal (d+(t+2)) _
                D.sourceFamily q D.sourcePower))) k,z j=0) ∧
          (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) ∧
          ActualSelectedContactWindowLaws S
            (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
            (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
            A (hilbertSamuelValue I) P.chart.toFun PHS.neighborhood := by
  dsimp only
  intro hcut
  obtain ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,C,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic⟩:=
    exists_actual_same_current_geometric_stage I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hcut
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,C,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,?_⟩
  intro fOld hfOld hRepOld fNew hfNew hRepNew
  obtain ⟨O,hO,h0O,hOsub,_hMapOld,_hHolNew,hCarriers⟩:=
    exists_actual_same_stage_selected_carrier_transport (I:=I) (G:=G) (e:=e) (f:=f)
      (b:=b) (he:=he) (hp:=hp) (S:=S) hmem hred hContact D P
      PHS.neighborhood PHS.isOpen_neighborhood PHS.zero_mem hPHS hFlags
      fOld hfOld hRepOld fNew hfNew hRepNew
  obtain ⟨V,hV,h0V,hVPHS,hVO,hHSContact⟩:=
    exists_actual_whole_hs_coordinate_contact_window PHS
      (actualAdaptedHistoricalCurrentSource D).selector D.targetContact fNew hfNew hRepNew O hO h0O
  refine ⟨V,hV,h0V,hVPHS,(fun k z hz=>hCarriers k z (hVO hz)),?_⟩
  intro z hz hHS
  obtain ⟨hNewZero,hCoords⟩:=hHSContact z hz hHS
  exact ⟨hNewZero,hCoords,fun k=>(hCarriers k z (hVO hz)).mpr (fun j _=>hNewZero j)⟩

end
end Hironaka.HironakaActualWholeHSContactWindow
