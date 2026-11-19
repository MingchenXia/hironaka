import Hironaka.Resolution.HironakaActualPrescribedHSRecursion

/-! Repeated historical transitions on the actually given following global
blowup, with the exact produced source open and full ordered marked record. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalPrescribedIteration
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 HironakaActualPrescribedHSRecursion HironakaActualPrescribedCentreRebasing
 HironakaActualPrescribedWeightedSuccessor HironakaActualRawRecordPullbacks
 HironakaActualOpenCoordinateStrictSquare HironakaActualVanishingIntrinsicHSTransport
 HironakaHolomorphicPointJets HironakaActualCoefficientPresentationCentrePower
 HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
 HironakaActualFormalInitialDiagram HironakaRelativeNormalMonomialBasis
 HironakaActualFixedInheritedSelector HironakaActualInheritedNestedContactFlag
 HironakaActualCurrentMarkedFunctionSquares HironakaActualGeometricCurrentNeighborhoodHS
 HironakaActualGeometricAdaptedCurrentSelector HironakaActualAnalyticAdaptedCurrentSelector
 HironakaActualOriginalAdaptedMarkedTransport HironakaHolomorphicJetChartInvariance
 HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentTranslatedJets
 MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder OkaRelationSheaf
 MarkedIdealBiholomorphism BlowupTowers OkaIdealOperations
 HironakaActualFixedFlatteningHSComparison HironakaActualInheritedCurrentSourceRelabel
 HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 HironakaRelativeNormalDeformationInitialRelations RelativePrincipalizationSpan
 HironakaActualNormalMarkedDirection HironakaActualAnalyticBlowupTaylor
 HironakaActualSameCurrentGeometricStage HironakaActualWholeHSContactWindow
 HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualInheritedSourcePermutationFamily BlowupFlatCoordinates
 HironakaActualFiniteCoefficientIdeals InvertibleIdealQuotient

variable {n : ℕ}

section Restrict
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n X] [IsComplexManifold n Y]

def followingSourceOpen {C : Set X} {σ : Y → X} (hσ : IsBlowupAlong n C σ) (V : Opens X) : Opens Y :=
  ⟨σ ⁻¹' (V : Set X),V.isOpen.preimage hσ.contMDiff.continuous⟩

def followingRestrictedMap {C : Set X} {σ : Y → X} (hσ : IsBlowupAlong n C σ) (V : Opens X) :
    followingSourceOpen hσ V → V := fun z=>⟨σ z.val,z.property⟩

theorem followingRestrictedMap_blowup {C : Set X} {σ : Y → X}
    (hσ : IsBlowupAlong n C σ) (V : Opens X) :
    IsBlowupAlong n ((Subtype.val : V → X) ⁻¹' C) (followingRestrictedMap hσ V) :=
  BlowupRestrictOpen.isBlowupAlong_restrict hσ V (V.isOpen.preimage hσ.contMDiff.continuous)

/-- Entire differential strict set of the SAME following global blowup. -/
theorem followingRestrictedMap_strict {C : Set X} {σ : Y → X}
    (hσ : IsBlowupAlong n C σ) (V : Opens X) (W : Set X) :
    strictTransform n (followingRestrictedMap hσ V) ((Subtype.val : V → X) ⁻¹' W)=
      (Subtype.val : followingSourceOpen hσ V → Y) ⁻¹' strictTransform n σ W := by
  have h:=strictTransform_actual_open_coordinate_square σ (followingRestrictedMap hσ V)
    hσ.contMDiff (followingRestrictedMap_blowup hσ V).contMDiff V (followingSourceOpen hσ V)
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) V ∞)
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (followingSourceOpen hσ V) ∞)
    (fun _=>rfl) W
  exact h

/-- Whole ordered marked record of that literal same restricted global map. -/
theorem followingRestrictedMap_record {C : Set X} {σ : Y → X}
    (hσ : IsBlowupAlong n C σ) (V : Opens X) (Q : MarkedIdeal n X)
    (hQhol : ∀x f,Q.ideal.mem x f → HolomorphicAt n f x) :
    (MarkedIdeal.pullback (Subtype.val : V → X) Q).geoTransform
      ((Subtype.val : V → X) ⁻¹' C) (followingRestrictedMap hσ V)=
      MarkedIdeal.pullback (Subtype.val : followingSourceOpen hσ V → Y) (Q.geoTransform C σ) :=
  geoTransform_pullback_val_of_hhol (X:=CMfd.of (n:=n) X) (Y:=CMfd.of (n:=n) Y)
    hQhol hσ V (V.isOpen.preimage hσ.contMDiff.continuous)

/-- Actual geometric phase equality gives native phase equality on the
following restricted map, at the same actual point. -/
theorem followingRestrictedMap_hs {C : Set X} {σ : Y → X}
    (hσ : IsBlowupAlong n C σ) (V : Opens X) (W : Set X)
    (z : followingSourceOpen hσ V)
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n σ W)) z.val ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (σ z.val) ℓ) :
    ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n)
      (strictTransform n (followingRestrictedMap hσ V) ((Subtype.val : V → X) ⁻¹' W))) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) ((Subtype.val : V → X) ⁻¹' W))
        (followingRestrictedMap hσ V z) ℓ := by
  intro ℓ
  rw [followingRestrictedMap_strict]
  have ht:=hilbertSamuelAt_vanishing_actual_open_any (n:=n) (followingSourceOpen hσ V)
    (strictTransform n σ W) z ℓ
  have hs:=hilbertSamuelAt_vanishing_actual_open_any (n:=n) V W (followingRestrictedMap hσ V z) ℓ
  exact ht.trans ((hHS ℓ).trans hs.symm)

/-- Native centre cosupport is derived from the actual GLOBAL centre and
full native record, rather than supplied as a next-stage input. -/
theorem following_global_centre_cosupport (Q : MarkedIdeal n X) (V : Opens X)
    {C : Set X} (hC : C⊆Q.cosupp) :
    (Subtype.val : V → X) ⁻¹' C⊆(MarkedIdeal.pullback (Subtype.val : V → X) Q).cosupp := by
  intro z hz
  have h:=hC hz
  refine ⟨h.1,fun g hg=>?_⟩
  refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_
  rintro _ ⟨a,ha,rfl⟩
  have hval : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (Subtype.val : V → X):=
    contMDiff_subtype_val
  exact MonomialPartEtale.vanishesToOrderOn_comp
    (Eventually.of_forall fun w=>(hval w).mdifferentiableAt (by simp)) (h.2 a ha)

end Restrict

section GlobalTransition
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (n+1)) X] [IsComplexManifold (n+1) X]
variable (V : Opens X)

/-- All next historical data for the genuinely given following GLOBAL map,
using the exact produced current source open. All fields are OUTPUTS. -/
def ActualFollowingGlobalHistoricalLaws
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel (n+1))}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)}
    {Cg : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1))} {u : HolGerm (ComplexModel (n+1))}
    (Qg : MarkedIdeal (n+1) X) (Wg : Set X)
    (Q : MarkedIdeal (n+1) V) (x : V)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u) (W : Set V)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R) : Prop :=
    ∀(Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+1)) Y] [IsComplexManifold (n+1) Y],
    ∀(C : Set X)(σ : Y → X)(hσ : IsBlowupAlong (n+1) C σ),x.val∈C → C⊆Qg.cosupp →
    let r:=followingRestrictedMap hσ V
    let hσV:=followingRestrictedMap_blowup hσ V
    let Cn:=(Subtype.val : V → X) ⁻¹' C
    ∃(Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
      (_hΞsrc : Ξ.source⊆(chartAt (ComplexModel (n+1)) x).target)
      (hΞ0 : Ξ.toFun (chartAt (ComplexModel (n+1)) x x)=0),
      Ξ.target=PHS.neighborhood ∧ Ξ.invFun=Θ.invFun ∘ P.chart.toFun ∧
      ∃k,∃T : ActualPrescribedHistoricalFlattening I G hspan S (actualFixedFlatteningSet x Ξ Cn) k,
      let Ω:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
      ∃hΩsrc : Ω.source⊆(chartAt (ComplexModel (n+1)) x).target,
      ∃_hΩ0 : Ω.toFun (chartAt (ComplexModel (n+1)) x x)=0,
      ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' Cn=
        (Subtype.val : actualRebaseModel x Ω → ComplexModel (n+1)) ⁻¹' complexCoordinatePlane (n+1) k) ∧
      (∀z∈Ω.target,∀v,(GermIdeal.pullback (m:=(n+1)) T.chart.invFun
        (actualHistoricalStageSheaf x Θ P.chart W)).mem z v ↔
        (vanishingIdeal (n:=(n+1)) (actualFixedFlatteningSet x Ω W)).mem z v) ∧
      prescribedFlatOriginIdeal I T.chart T.chart_zero=
        originalCoherentOriginIdeal (vanishingIdeal (n:=(n+1)) (actualFixedFlatteningSet x Ω W)) ∧
      ActualPrescribedNextBlowupLaws Q x Ω hΩsrc Cn r hσV W ∧
      ActualFlatWeightedRecordLaws Q x P Ξ hΞ0 T ∧
      (∀j : actualInitialVertices MonomialOrder.degLex
        (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
        0<normalExponentDegree j.val) ∧
      ActualFlatCentreOrders x Ξ hΞ0 T P.currentFunctions ∧
      (∀(_hk : k+2≤n+1)(z : prescribedSourceOpen hσV x Ω),σ z.val.val=x.val →
        (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n+1) (strictTransform (n+1) σ Wg)) z.val.val ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n+1) Wg) (σ z.val.val) ℓ) →
        let If:=prescribedFlatOriginIdeal I T.chart T.chart_zero
        let F:=prescribedFlatFunctions T P.currentFunctions
        let E:=Q.E.map ((fun v : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω v) ⁻¹' ·)
        let π:=prescribedNativeMap hσV x Ω hΩsrc
        let M : MarkedIdeal (n+1) (actualRebaseModel x Ω):=⟨univ,E,
          weightedFunctionIdeal (fun a=>normalExponentDegree a.val) (fun a v=>F a v),
          weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex
            (analyticZeroTaylorIdeal (n+1) If)=>normalExponentDegree a.val)⟩
        let Qnext:=M.geoTransform ((Subtype.val : actualRebaseModel x Ω → ComplexModel (n+1)) ⁻¹'
          complexCoordinatePlane (n+1) k) π
        Qnext=MarkedIdeal.pullback (fun z : prescribedSourceOpen hσV x Ω=>z.val.val) (Qg.geoTransform C σ) ∧
        strictTransform (n+1) π (nativeStrictSet x Ω W)=
          (fun z : prescribedSourceOpen hσV x Ω=>z.val.val) ⁻¹' strictTransform (n+1) σ Wg ∧
        z∈Qnext.cosupp ∧ ActualNextHistoricalStage k If T.family T.historicalSelector Qnext
          π (nativeStrictSet x Ω W) z R)

/-- Restrict the actual global next map, derive its native centre and HS
conditions, and construct the following entire historical stage. -/
theorem global_transition_from_weighted_stage
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel (n+1))}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)}
    {Cg : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1))} {u : HolGerm (ComplexModel (n+1))}
    (Qg : MarkedIdeal (n+1) X) (Wg : Set X)
    (Q : MarkedIdeal (n+1) V) (x : V)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u) (W : Set V)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R)
    (hRecord : Q=MarkedIdeal.pullback (Subtype.val : V → X) Qg)
    (hQhol : ∀x f,Qg.ideal.mem x f → HolomorphicAt (n+1) f x)
    (hTrace : W=(Subtype.val : V → X) ⁻¹' Wg)
    (hOrigin : I=originalCoherentOriginIdeal (actualHistoricalStageSheaf x Θ P.chart W))
    (hWa : IsComplexAnalyticSubset (n:=n+1) W)
    (hWeighted : ActualPrescribedWeightedRebaseLaws Q x Θ P W hspan S R PHS) :
    ActualFollowingGlobalHistoricalLaws V Qg Wg Q x Θ P W hspan S R PHS := by
  have hTransition:=hs_rebase_of_weighted_stage Q x Θ P W hspan S R PHS hOrigin hWa hWeighted
  intro Y _ _ _ C σ hσ hxC hC
  let r:=followingRestrictedMap hσ V
  let hσV:=followingRestrictedMap_blowup hσ V
  let Cn:=(Subtype.val : V → X) ⁻¹' C
  have hCn : Cn⊆Q.cosupp := by
    rw [hRecord]
    exact following_global_centre_cosupport Qg V hC
  obtain ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hFlatWeighted,
    hwFlat,hFlatCos,hStep⟩:=hTransition (followingSourceOpen hσ V) Cn r hσV hxC hCn
  refine ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hFlatWeighted,
    hwFlat,hFlatCos,?_⟩
  intro hk z hz hHS
  have hzNative : r z.val=x:=Subtype.ext hz
  have hPhase:=followingRestrictedMap_hs hσ V Wg z.val hHS
  rw [←hTrace] at hPhase
  obtain ⟨hExact,hCut,hStage⟩:=hStep hk z hzNative hPhase
  have hRestrict : Q.geoTransform Cn r=MarkedIdeal.pullback
      (Subtype.val : followingSourceOpen hσ V → Y) (Qg.geoTransform C σ) := by
    rw [hRecord]
    exact followingRestrictedMap_record hσ V Qg hQhol
  rw [hRestrict] at hExact
  let Ω:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
  have hCompose : MarkedIdeal.pullback
      (Subtype.val : prescribedSourceOpen hσV x Ω → followingSourceOpen hσ V)
      (MarkedIdeal.pullback (Subtype.val : followingSourceOpen hσ V → Y) (Qg.geoTransform C σ))=
      MarkedIdeal.pullback (fun v : prescribedSourceOpen hσV x Ω=>v.val.val) (Qg.geoTransform C σ) :=
    marked_pullback_comp_hhol (J:=Qg.geoTransform C σ) (fun _ _ hg=>hg.1)
      contMDiff_subtype_val contMDiff_subtype_val (fun _=>rfl)
  have hGlobalStrict : strictTransform (n+1) (prescribedNativeMap hσV x Ω hΩsrc)
      (nativeStrictSet x Ω W)=
      (fun v : prescribedSourceOpen hσV x Ω=>v.val.val) ⁻¹' strictTransform (n+1) σ Wg := by
    rw [prescribedNativeMap_strict,hTrace,followingRestrictedMap_strict]
    rfl
  exact ⟨hExact.trans hCompose,hGlobalStrict,hCut,hStage⟩


/-- The actually produced next stage retains its full historical witnesses,
original labels, and a further transition on the following GLOBAL map. -/
def ActualNextGlobalHistoricalStage
    (Qg : MarkedIdeal (n+1) X) (Wg : Set X)
    (k : ℕ) (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    {κ : Type} (L : κ≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))
    (w0 : κ → ℕ)
    (Q : MarkedIdeal (n+1) V) {U : Opens (ComplexModel (n+1))} (π : V → U)
    (W : Set U) (y : V) (R : ℕ → ℕ) : Prop :=
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)=>
    normalExponentDegree a.val
  ∃q : Fin (n+1),q.val=k ∧
    ∃(e : Fin (n+1))(b : Fin (n+1) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (n+1)) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (n+1)) y).target ∧
      (∀z : V,z∈(chartAt (ComplexModel (n+1)) y).source →
        chartAt (ComplexModel (n+1)) y z∈Θ.source →
        (π z : ComplexModel (n+1))=actualAnalyticBlowupMap (Set.Ici q) e b
          (Θ.toFun (chartAt (ComplexModel (n+1)) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1)),
      ∃u : HolGerm (ComplexModel (n+1)),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (n+1) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (n+1)))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n+1)
            (strictTransform (n+1) π W)) y Θ) 0)
        let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
        let A₀:=vanishingIdeal (n:=n+1)
          (actualFixedFlatteningSet y Θ (strictTransform (n+1) π W))
        let A:=GermIdeal.pullback (m:=(n+1)) P.chart.toFun A₀
        J=Ideal.map C.toRingEquiv.toRingHom K ∧ J=originalCoherentOriginIdeal A ∧
        ∃PHS : ActualGeometricInheritedNeighborhoodHS A J D.targetFamily R,
          PHS.representatives=P.currentFunctions ∧ PHS.neighborhood⊆P.currentDomain ∧
          MapsTo P.chart.toFun PHS.neighborhood Θ.target ∧
          (∀k,∀z∈PHS.neighborhood,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (n+1) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (n+1) (sameAnalyticZeroNormalizedIdeal (n+1) _
                D.sourceFamily q D.sourcePower))) k,z j=0) ∧
          (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n+1) (strictTransform (n+1) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=n+1) W) (π y) ℓ) ∧
          ActualSelectedContactWindowLaws S
            (sameAnalyticNormalNormalizedVertex (n+1) I G q e he b hp)
            (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
            A R P.chart.toFun PHS.neighborhood ∧
          ActualPrescribedStageRebaseLaws Q y Θ P (strictTransform (n+1) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector R PHS ∧
          ActualPrescribedWeightedRebaseLaws Q y Θ P (strictTransform (n+1) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector R PHS ∧
          ActualFollowingGlobalHistoricalLaws V Qg Wg Q y Θ P (strictTransform (n+1) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector R PHS ∧
          (∀a,normalExponentDegree ((actualAdaptedOriginalLabelEquiv D) (L a)).val=w0 a)

/-- Consume a genuinely produced stage and its actual global restriction
square; derive the next global transition and literal historical label map. -/
theorem global_continuation_of_next_stage
    (Qg : MarkedIdeal (n+1) X) (Wg : Set X)
    (k : ℕ) (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    {κ : Type} (L : κ≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))
    (w0 : κ → ℕ)
    (Q : MarkedIdeal (n+1) V) {U : Opens (ComplexModel (n+1))} (π : V → U)
    (W : Set U) (y : V) (R : ℕ → ℕ)
    (hRecord : Q=MarkedIdeal.pullback (Subtype.val : V → X) Qg)
    (hQhol : ∀x f,Qg.ideal.mem x f → HolomorphicAt (n+1) f x)
    (hTrace : strictTransform (n+1) π W=(Subtype.val : V → X) ⁻¹' Wg)
    (hWa : IsComplexAnalyticSubset (n:=n+1) W)
    {C : Set U} (hπ : IsBlowupAlong (n+1) C π)
    (hL : ∀a,normalExponentDegree (L a).val=w0 a)
    (hStage : ActualNextHistoricalStage k I G S Q π W y R) :
    ActualNextGlobalHistoricalStage V Qg Wg k I G S L w0 Q π W y R := by
  obtain ⟨q,hq,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hSquareRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContact,hRebase,hWeighted⟩:=hStage
  refine ⟨q,hq,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hSquareRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContact,hRebase,hWeighted,?_,?_⟩
  · have hNextAnalytic:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa
    exact global_transition_from_weighted_stage V Qg Wg Q y Θ P (strictTransform (n+1) π W)
      D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector R PHS hRecord hQhol hTrace
      hOriginCurrent hNextAnalytic hWeighted
  · intro a
    exact (actualAdaptedOriginalLabelEquiv_degree D (L a)).trans (hL a)

end GlobalTransition

section RepeatedStage
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (n+1)) X] [IsComplexManifold (n+1) X]

/-- Original-source output laws for a further genuinely prescribed GLOBAL
map after the first produced prescribed transition, with original labels. -/
def ActualPrescribedRepeatedHSRebaseLaws
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel (n+1))}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)}
    {Cg : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1))} {u : HolGerm (ComplexModel (n+1))}
    (Q : MarkedIdeal (n+1) X) (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u) (W : Set X)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R) : Prop :=
    ∀(Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel (n+1)) Y] [IsComplexManifold (n+1) Y],
    ∀(C : Set X)(ρ : Y → X)(hρ : IsBlowupAlong (n+1) C ρ),x∈C → C⊆Q.cosupp →
    ∃(Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
      (_hΞsrc : Ξ.source⊆(chartAt (ComplexModel (n+1)) x).target)
      (hΞ0 : Ξ.toFun (chartAt (ComplexModel (n+1)) x x)=0),
      Ξ.target=PHS.neighborhood ∧ Ξ.invFun=Θ.invFun ∘ P.chart.toFun ∧
      ∃k,∃T : ActualPrescribedHistoricalFlattening I G hspan S (actualFixedFlatteningSet x Ξ C) k,
      let Ω:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
      ∃hΩsrc : Ω.source⊆(chartAt (ComplexModel (n+1)) x).target,
      ∃_hΩ0 : Ω.toFun (chartAt (ComplexModel (n+1)) x x)=0,
      ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' C=
        (Subtype.val : actualRebaseModel x Ω → ComplexModel (n+1)) ⁻¹' complexCoordinatePlane (n+1) k) ∧
      (∀z∈Ω.target,∀v,(GermIdeal.pullback (m:=(n+1)) T.chart.invFun
        (actualHistoricalStageSheaf x Θ P.chart W)).mem z v ↔
        (vanishingIdeal (n:=(n+1)) (actualFixedFlatteningSet x Ω W)).mem z v) ∧
      prescribedFlatOriginIdeal I T.chart T.chart_zero=
        originalCoherentOriginIdeal (vanishingIdeal (n:=(n+1)) (actualFixedFlatteningSet x Ω W)) ∧
      ActualPrescribedNextBlowupLaws Q x Ω hΩsrc C ρ hρ W ∧
      ActualFlatWeightedRecordLaws Q x P Ξ hΞ0 T ∧
      (∀j : actualInitialVertices MonomialOrder.degLex
        (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
        0<normalExponentDegree j.val) ∧
      ActualFlatCentreOrders x Ξ hΞ0 T P.currentFunctions ∧
      (∀(_hk : k+2≤n+1)(z : prescribedSourceOpen hρ x Ω),ρ z.val=x →
        (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n+1) (strictTransform (n+1) ρ W)) z.val ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n+1) W) (ρ z.val) ℓ) →
        let If:=prescribedFlatOriginIdeal I T.chart T.chart_zero
        let F:=prescribedFlatFunctions T P.currentFunctions
        let E:=Q.E.map ((fun v : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω v) ⁻¹' ·)
        let π:=prescribedNativeMap hρ x Ω hΩsrc
        let M : MarkedIdeal (n+1) (actualRebaseModel x Ω):=⟨univ,E,
          weightedFunctionIdeal (fun a=>normalExponentDegree a.val) (fun a v=>F a v),
          weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex
            (analyticZeroTaylorIdeal (n+1) If)=>normalExponentDegree a.val)⟩
        let Qnext:=M.geoTransform ((Subtype.val : actualRebaseModel x Ω → ComplexModel (n+1)) ⁻¹'
          complexCoordinatePlane (n+1) k) π
        Qnext=MarkedIdeal.pullback (Subtype.val : prescribedSourceOpen hρ x Ω → Y) (Q.geoTransform C ρ) ∧
        z∈Qnext.cosupp ∧ ActualNextGlobalHistoricalStage (prescribedSourceOpen hρ x Ω)
          (Q.geoTransform C ρ) (strictTransform (n+1) ρ W) k If T.family T.historicalSelector
          (labels.trans T.historicalLabels) w Qnext π (nativeStrictSet x Ω W) z R)

/-- The original produced next stage genuinely constructs a further
transition on the given following global map, with composed original labels. -/
theorem repeated_transition_of_actual_hs_stage
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel (n+1))}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)}
    {Cg : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1))} {u : HolGerm (ComplexModel (n+1))}
    (Q : MarkedIdeal (n+1) X) (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) x x))
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u) (W : Set X)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R)
    (hWa : IsComplexAnalyticSubset (n:=n+1) W)
    (hLabels : ∀a,normalExponentDegree (labels a).val=w a)
    (hTransition : ActualPrescribedHSRebaseLaws Q x Θ P W hspan S R PHS) :
    ActualPrescribedRepeatedHSRebaseLaws Q x Θ P W hspan S R PHS := by
  intro Y _ _ _ C ρ hρ hxC hC
  obtain ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hFlatWeighted,
    hwFlat,hFlatCos,hStep⟩:=hTransition Y C ρ hρ hxC hC
  refine ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hFlatWeighted,
    hwFlat,hFlatCos,?_⟩
  intro hk z hz hHS
  obtain ⟨hExact,hCut,hStage⟩:=hStep hk z hz hHS
  refine ⟨hExact,hCut,?_⟩
  let Ω:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
  have hLabelsFlat : ∀a,normalExponentDegree (T.historicalLabels (labels a)).val=w a :=
    fun a=>(T.historicalLabels_degree (labels a)).trans (hLabels a)
  exact global_continuation_of_next_stage (prescribedSourceOpen hρ x Ω)
    (Q.geoTransform C ρ) (strictTransform (n+1) ρ W) k
    (prescribedFlatOriginIdeal I T.chart T.chart_zero) T.family T.historicalSelector
    (labels.trans T.historicalLabels) w _ (prescribedNativeMap hρ x Ω hΩsrc)
    (nativeStrictSet x Ω W) z R hExact (fun _ _ hg=>hg.1)
    (prescribedNativeMap_strict hρ x Ω hΩsrc W) (nativeStrictSet_analytic x Ω hΩsrc hWa)
    (prescribedNativeMap_blowup hρ x Ω hΩsrc) hLabelsFlat hStage

end RepeatedStage

/-- ORIGINAL source geometry constructs a repeated historical transition on
the genuinely given following GLOBAL map. The full original stage/family,
selector/prefix history, original-degree composition and ordered global
marked-transform restriction are retained; no repeated-history certificate
or following cut/order/neighbourhood is supplied. -/
theorem exists_actual_geometric_stage_prescribed_historical_iteration
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
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    y∈Q.cosupp ∧
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
            A (hilbertSamuelValue I) P.chart.toFun PHS.neighborhood ∧
          ActualPrescribedStageRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedWeightedRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedRepeatedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS := by
  dsimp only
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition⟩:=
    exists_actual_geometric_stage_prescribed_hs_successor I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,?_⟩
  have hNextAnalytic:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa
  exact repeated_transition_of_actual_hs_stage Q y Θ P (strictTransform (d+(t+2)) π W)
    D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS
    hNextAnalytic (fun a=>actualAdaptedOriginalLabelEquiv_degree D a) hHSTransition

end
end Hironaka.HironakaActualHistoricalPrescribedIteration
