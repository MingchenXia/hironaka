import Hironaka.Resolution.HironakaActualHistoricalFormalSupportedDivision
import Hironaka.Invariant.OrderTaylor

/-! Whole moving historical prefix support for the SAME actual functions.
Only genuine translation and diagonal normalization are used; no target
monic head or graph-coordinate preservation certificate is presumed. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalMovingPrefixSupport
noncomputable section
open HolGerm HironakaHolomorphicPointJets HolomorphicTaylorTail
 HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
 HironakaActualInheritedNestedContactFlag HironakaActualInheritedAnalyticBlockJacobian
 HironakaRelativeNormalTaylorCoefficients HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualOriginalFormalHSTransfer
 HironakaActualGeometricCurrentNeighborhoodHS HironakaHolomorphicJetRankLoci
 HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
 HironakaActualHistoricalFormalSupportedDivision
 HironakaActualCauchyCoordinateDivision HironakaActualRelativeNormalJetDivision OkaRelationSheaf
 HironakaActualDiagonalTaylor HironakaActualInheritedSmallTails
 HironakaActualOriginalScaledAnalyticDivision HironakaActualInheritedNeighborhoodStandardJets
 HironakaActualFiniteDegLexWeights HironakaActualWeightedVertexSmallTails
 HironakaHolomorphicJetChartInvariance
 Hironaka.HolomorphicIdealSheaves
 HironakaActualCauchyMonomialDivision HironakaActualCanonicalBlockJacobian

variable {n : ℕ}

/-- Literal whole-germ commutation for the SAME constant-coordinate
multi-derivative and the genuine translation at the inspected point. -/
theorem actualAnalyticMultiDerivative_translatedGerm
    (β : Fin n →₀ ℕ) (u : ComplexModel n) (f : ComplexModel n → ℂ) (hf : HolAt f u)
    (hdf : HolAt (iterDeriv ((actualCoordinateDerivativeWord β).map
      (fun i=>EuclideanSpace.single i (1 : ℂ))) f) u) :
    actualAnalyticMultiDerivative β (translatedGerm u f hf)=
      translatedGerm u (iterDeriv ((actualCoordinateDerivativeWord β).map
        (fun i=>EuclideanSpace.single i (1 : ℂ))) f) hdf := by
  let L:=(actualCoordinateDerivativeWord β).map (fun i=>EuclideanSpace.single i (1 : ℂ))
  change iteratedDerivativeGerm L (HolGerm.mk (fun z=>f (z+u)) _)=
    HolGerm.mk (fun z=>iterDeriv L f (z+u)) _
  rw [iteratedDerivativeGerm_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall (OrderTaylor.iterDeriv_comp_add_right f u L)

theorem translatedGerm_zero_of_eqOn {U : Set (ComplexModel n)} (hU : IsOpen U)
    {u : ComplexModel n} (hu : u∈U) (f : ComplexModel n → ℂ) (hf : HolAt f u)
    (hzero : EqOn f (fun _=>0) U) : translatedGerm u f hf=0 := by
  have ht : Tendsto (fun z : ComplexModel n=>z+u) (𝓝 0) (𝓝 u):=by
    simpa only [id_eq,zero_add] using (continuous_id.add_const u).tendsto (0 : ComplexModel n)
  have hz : ∀ᶠz in 𝓝 (0 : ComplexModel n),f (z+u)=0:=
    ht.eventually ((show ∀ᶠz in 𝓝 u,z∈U from hU.mem_nhds hu).mono fun z hz=>hzero hz)
  have hEq : translatedGerm u f hf=HolGerm.mk (fun _ : ComplexModel n=>(0 : ℂ))
      (Eventually.of_forall fun _=>differentiableAt_const 0):=HolGerm.mk_eq_mk_iff.mpr hz
  simpa only [HolGerm.mk_const,map_zero] using hEq

/-- Whole coefficient support is a property of the literal member family,
with its OLD vertex labels; no current monicity or diagram is asserted. -/
def HistoricalWholePrefixSupport (V : Finset (Fin n →₀ ℕ)) (g : V → MvPowerSeries (Fin n) ℂ) : Prop :=
  ∀k,∀a : V,k<normalExponentDegree a.val →
    ∀b : V,normalExponentDegree b.val≤k →
      ∀α : Fin n →₀ ℕ,b.val≤α → MvPowerSeries.coeff α (g a)=0

theorem historicalWholePrefixSupport_multiDerivative_zero
    {V : Finset (Fin n →₀ ℕ)} {g : V → MvPowerSeries (Fin n) ℂ}
    (h : HistoricalWholePrefixSupport V g) (k : ℕ) (a : V)
    (hka : k<normalExponentDegree a.val) (b : V) (hbk : normalExponentDegree b.val≤k)
    (β : Fin n →₀ ℕ) (hβ : b.val≤β) : actualFormalMultiDerivative β (g a)=0 := by
  apply (actualFormalMultiDerivative_eq_zero_iff_cone β (g a)).mpr
  intro α hβα
  exact h k a hka b hbk α (hβ.trans hβα)

theorem coeff_actual_diagonal_row_zero (c : Fin n → ℂ) (q : ℂ)
    (F : HolGerm (ComplexModel n)) (α : Fin n →₀ ℕ)
    (hzero : MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n F)=0) :
    MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n
      (HolGerm.constHom q*actualDiagonalPullback c F))=0 := by
  have hConst : actualUnshiftedTaylorAlgHom n (HolGerm.constHom q)=MvPowerSeries.C q:=by
    change (actualUnshiftedTaylorAlgHom n) (algebraMap ℂ (HolGerm (ComplexModel n)) q)=algebraMap ℂ _ q
    exact AlgHom.commutes _ q
  rw [map_mul,hConst,MvPowerSeries.coeff_C_mul,coeff_actualDiagonalPullback,hzero,mul_zero,mul_zero]

section GeometricSource
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

/-- Whole origin prefix support of the SAME family gives actual derivative
identities on ONE genuine neighbourhood, before every native point. -/
theorem exists_actual_native_moving_prefix_derivative_zero
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆PHS.neighborhood ∧
      ∀u∈U,∀hu : u∈PHS.neighborhood,
        ∀a b : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
          normalExponentDegree b.val<normalExponentDegree a.val →
          actualAnalyticMultiDerivative b.val
            (translatedGerm u (PHS.representatives a) (PHS.holomorphicAt _ hu a))=0 := by
  classical
  have hOne (a b : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      ∀ᶠu in 𝓝 (0 : ComplexModel n),
        normalExponentDegree b.val<normalExponentDegree a.val →
        iterDeriv ((actualCoordinateDerivativeWord b.val).map
          (fun i=>EuclideanSpace.single i (1 : ℂ))) (PHS.representatives a) u=0 := by
    by_cases hba : normalExponentDegree b.val<normalExponentDegree a.val
    · let L:=(actualCoordinateDerivativeWord b.val).map (fun i=>EuclideanSpace.single i (1 : ℂ))
      have hDeriv : actualAnalyticMultiDerivative b.val (G.germs a)=0:=
        (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val (G.germs a)).mpr
          (fun α hα=>hred (normalExponentDegree b.val) a hba b le_rfl α hα)
      have hHol : HolAt (iterDeriv L (PHS.representatives a)) 0:=
        eventually_holomorphic_iterDeriv (PHS.holomorphicAtZero a) L
      have hZero : HolGerm.mk (iterDeriv L (PHS.representatives a)) hHol=0:=by
        rw [←iteratedDerivativeGerm_mk L (PHS.holomorphicAtZero a),PHS.sameGerms a]
        exact hDeriv
      have hEq : HolGerm.mk (iterDeriv L (PHS.representatives a)) hHol=
          HolGerm.mk (fun _ : ComplexModel n=>(0 : ℂ))
            (Eventually.of_forall fun _=>differentiableAt_const 0):=by
        simpa only [HolGerm.mk_const,map_zero] using hZero
      filter_upwards [HolGerm.mk_eq_mk_iff.mp hEq] with u hu _
      exact hu
    · exact Eventually.of_forall fun _ h=>(hba h).elim
  have hPmem : ∀ᶠu in 𝓝 (0 : ComplexModel n),u∈PHS.neighborhood:=
    PHS.isOpen_neighborhood.mem_nhds PHS.zero_mem
  have hAll : ∀ᶠu in 𝓝 (0 : ComplexModel n),u∈PHS.neighborhood ∧
      ∀a b : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
        normalExponentDegree b.val<normalExponentDegree a.val →
        iterDeriv ((actualCoordinateDerivativeWord b.val).map
          (fun i=>EuclideanSpace.single i (1 : ℂ))) (PHS.representatives a) u=0 :=
    hPmem.and
      (eventually_all.mpr fun a=>eventually_all.mpr fun b=>hOne a b)
  obtain ⟨U,hUsub,hU,h0U⟩:=mem_nhds_iff.mp hAll
  refine ⟨U,hU,h0U,fun _ hu=>(hUsub hu).1,?_⟩
  intro u hu huP a b hba
  let L:=(actualCoordinateDerivativeWord b.val).map (fun i=>EuclideanSpace.single i (1 : ℂ))
  have hHol : HolAt (iterDeriv L (PHS.representatives a)) u:=by
    filter_upwards [PHS.isOpen_neighborhood.mem_nhds huP] with z hz
    exact (differentiableOn_iterDeriv (PHS.holomorphicOn a) PHS.isOpen_neighborhood L z hz).differentiableAt
      (PHS.isOpen_neighborhood.mem_nhds hz)
  rw [actualAnalyticMultiDerivative_translatedGerm b.val u (PHS.representatives a) (PHS.holomorphicAt _ huP a) hHol]
  exact translatedGerm_zero_of_eqOn hU hu _ hHol (fun z hz=>(hUsub hz).2 a b hba)

theorem actual_scaled_moving_whole_prefix_support
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s∈Metric.ball 0 P.radius)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (hu : scaledOriginalPoint P s p∈PHS.neighborhood)
    (hCov : ∀j : Fin (actualVertexCount n I),
      let a:=actualVertexEnumeration n I j
      let W:=degLexWeight n P.germs.degreeBound
      actualInheritedTranslatedGerm P hs p hdom j=
        HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
          actualDiagonalPullback (fun i=>s^W i)
            (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a)))
    (hzero : ∀a b : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      normalExponentDegree b.val<normalExponentDegree a.val →
      actualAnalyticMultiDerivative b.val (translatedGerm (scaledOriginalPoint P s p)
        (PHS.representatives a) (PHS.holomorphicAt _ hu a))=0) :
    HistoricalWholePrefixSupport (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
      (fun a=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
        ((actualVertexEnumeration n I).symm a))) := by
  intro k a hka b hbk α hβα
  have hNative : MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n
      (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a)))=0:=
    (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val _).mp
      (hzero a b (lt_of_le_of_lt hbk hka)) α hβα
  let j:=(actualVertexEnumeration n I).symm a
  have hj : actualVertexEnumeration n I j=a:=(actualVertexEnumeration n I).apply_symm_apply a
  have hCovj : actualInheritedTranslatedGerm P hs p hdom j=
      HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)*
        actualDiagonalPullback (fun i=>s^(degLexWeight n P.germs.degreeBound i))
          (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a)):=by
    simpa only [hj] using hCov j
  exact (congrArg (fun F : HolGerm (ComplexModel n)=>MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n F)) hCovj).trans
    (coeff_actual_diagonal_row_zero _ _ _ α hNative)

/-- ONE actual moving presentation, retaining (1)--(3) and adding full
original prefix-cone exclusion on the SAME scaled family, before all orders. -/
def ActualHistoricalSupportedPresentationNeighborhood
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) : Prop :=
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (hs : s∈Metric.ball 0 P.radius)(δ : ℝ),0<δ ∧
    IsOpen (historicalNativeJetWindow P s hs0 δ) ∧
    (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ ∧
    historicalNativeJetWindow P s hs0 δ⊆PHS.neighborhood ∧
    ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
      ∃hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius),
      ∃hu : scaledOriginalPoint P s p∈PHS.neighborhood,
        (∀j : Fin (actualVertexCount n I),
          let a:=actualVertexEnumeration n I j
          let W:=degLexWeight n P.germs.degreeBound
          actualInheritedTranslatedGerm P hs p hdom j=
            HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
              actualDiagonalPullback (fun i=>s^W i)
                (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a)
                  (PHS.holomorphicAt _ hu a))) ∧
        actualHistoricalScaledFormalIdeal A (scaledOriginalPoint P s p)
            (fun i=>s^(degLexWeight n P.germs.degreeBound i))=
          Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
            (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))) ∧
        HistoricalWholePrefixSupport
          (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
          (fun a=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
            ((actualVertexEnumeration n I).symm a))) ∧
        ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ActualHistoricalNativeExactOrderAt PHS (scaledOriginalPoint P s p) hu ∧
          (∀j : Fin (actualVertexCount n I),
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
              genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) ∧
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∉
              genuineFormalVariables n^(normalExponentDegree (wordExponent (actualVertexWords n I j))+1)) ∧
          (∀m,HistoricalDegreePrefixFrames (actualVertexWords n I)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) m) ∧
          HistoricalWholeSupportedDivision
            (historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
              (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))))

/-- A restriction of the SAME produced E scale/window retains every actual
formal presentation law and adds WHOLE moving prefix support, derived from
its genuine origin historical prefix data. No moving support is supplied. -/
theorem exists_actual_geometric_historical_supported_presentation_neighbourhood
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hFormal : ActualHistoricalFormalPresentationNeighborhood PHS)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k) :
    ActualHistoricalSupportedPresentationNeighborhood PHS := by
  obtain ⟨O,hO,h0O,_hOsub,hNative⟩:=exists_actual_native_moving_prefix_derivative_zero PHS hred
  obtain ⟨P,s,hs0,hs,δ,hδ,_hWindow,_hWindow0,hWindowSub,hPoints⟩:=hFormal
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have hc : Continuous (scaledOriginalPoint P s):=
    (actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))).continuous.comp e.symm.continuous
  have hc0 : scaledOriginalPoint P s (0 : CoordinateSpace n)=0:=by
    change actualDiagonalMap _ (e.symm 0)=0
    rw [map_zero,map_zero]
  have ht : Tendsto (scaledOriginalPoint P s) (𝓝 0) (𝓝 0):=by simpa only [hc0] using hc.tendsto 0
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp (ht.eventually (hO.mem_nhds h0O))
  refine ⟨P,s,hs0,hs,min δ η,lt_min hδ hη,
    historicalNativeJetWindow_isOpen P s hs0 _,historicalNativeJetWindow_zero P s hs0 (lt_min hδ hη),?_,?_⟩
  · intro u hu
    apply hWindowSub
    change (scaledOriginalPointHomeomorph P s hs0).symm u∈Metric.ball 0 δ
    change (scaledOriginalPointHomeomorph P s hs0).symm u∈Metric.ball 0 (min δ η) at hu
    exact Metric.ball_subset_ball (min_le_left δ η) hu
  intro p hp
  have hpδ : p∈Metric.ball (0 : CoordinateSpace n) δ:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_left δ η))
  have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
  obtain ⟨hdom,hu,hCov,hIdeal,hPhase⟩:=hPoints p hpδ
  refine ⟨hdom,hu,hCov,hIdeal,?_,hPhase⟩
  exact actual_scaled_moving_whole_prefix_support PHS P hs p hdom hu hCov
    (hNative _ (hηsub hpη) hu)

end GeometricSource

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
 HironakaActualHistoricalPrescribedIteration HironakaActualPrescribedHSRecursion
 HironakaActualPrescribedCentreRebasing HironakaActualPrescribedWeightedSuccessor
 HironakaActualCurrentMarkedFunctionSquares HironakaActualWholeHSContactWindow
 HironakaSmoothCentreCoherentDomain HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualInheritedCurrentSourceRelabel
 HironakaActualNormalMarkedDirection HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualRelativeNormalJetDivision HironakaActualAnalyticBlowupTaylor
 HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
 HironakaActualFiniteCoefficientIdeals HironakaRelativeNormalDeformationInitialRelations
 HironakaActualFixedFlatteningHSComparison
 HironakaRelativeNormalCoherentTranslatedJets HironakaActualNormalAllDirectionAnalyticSaturation
 MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder InvertibleIdealQuotient

/-- ORIGINAL geometry retains the SAME actual stage and exact produced E
formal-presentation data, restricts that genuine window and derives WHOLE
moving historical prefix support from the actual current origin prefix data. -/
theorem exists_actual_geometric_stage_with_historical_prefix_support
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧ ActualHistoricalWholeJetNeighborhood PHS ∧ ActualHistoricalDegreePrefixJetNeighborhood PHS ∧ ActualHistoricalFormalPresentationNeighborhood PHS ∧ ActualHistoricalSupportedPresentationNeighborhood PHS := by
  dsimp only
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets,hFormalJets⟩:=
    exists_actual_geometric_stage_with_historical_formal_presentation I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets,hFormalJets,?_⟩
  exact exists_actual_geometric_historical_supported_presentation_neighbourhood PHS hFormalJets D.targetPrefix




end
end Hironaka.HironakaActualHistoricalMovingPrefixSupport
