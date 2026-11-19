import Hironaka.Resolution.HironakaActualPrescribedWeightedSuccessor
import Hironaka.Resolution.HironakaActualGeometricPersistentInheritedCut
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Resolution.HironakaActualOpenCoordinateStrictSquare

/-! The prescribed actual next map, its whole geometric strict set, and
the same historical weighted source produce the next actual HS stage. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPrescribedHSRecursion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 HironakaActualPrescribedCentreRebasing HironakaActualPrescribedWeightedSuccessor
 HironakaActualGeometricPersistentInheritedCut HironakaActualCurrentMarkedFunctionSquares
 HironakaActualGeometricCurrentNeighborhoodHS HironakaActualWholeHSContactWindow
 HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
 HironakaSmoothCentreCoherentDomain HironakaRelativeNormalDeformationInitialRelations
 HironakaActualFixedFlatteningHSComparison HironakaActualFlatCoordinateIntrinsicHS
 HironakaActualVanishingIntrinsicHSTransport HironakaActualOpenCoordinateStrictSquare
 AnalyticSubsetOpens AnalyticSubsetPreimage BlowupFlatCoordinates
 MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
 HironakaActualFixedInheritedSelector HironakaActualCoefficientPresentationCentrePower
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualNormalZeroAnalyticSaturation HironakaActualInheritedCurrentSourceRelabel
 HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 OkaRelationSheaf OkaIdealOperations HironakaRelativeNormalCoherentTranslatedJets

variable {n : ℕ}

private theorem native_chart_value (U : Opens (ComplexModel n)) (p q : U) :
    chartAt (ComplexModel n) p q=(q : ComplexModel n) := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

/-- Identity coordinates on the exact native source open. -/
def nativeIdentityChart (U : Opens (ComplexModel n)) (p : U) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel n) p p) where
  source:=U
  target:=U
  isOpen_source:=U.isOpen
  isOpen_target:=U.isOpen
  center_mem_source:=by
    rw [native_chart_value]
    exact p.property
  toFun:=id
  invFun:=id
  toFun_holomorphic:=differentiableOn_id
  invFun_holomorphic:=differentiableOn_id
  mapsTo_toFun:=fun _ h=>h
  mapsTo_invFun:=fun _ h=>h
  left_inv:=fun _ _=>rfl
  right_inv:=fun _ _=>rfl

theorem nativeIdentityChart_source (U : Opens (ComplexModel n)) (p : U) :
    (nativeIdentityChart U p).source⊆(chartAt (ComplexModel n) p).target := by
  intro z hz
  have hsource : z∈(chartAt (ComplexModel n) (p : ComplexModel n)).source := by
    rw [chartAt_self_eq]
    exact mem_univ z
  have h:=chart_mem_opens_target (n:=n) (x:=p) (y:=(⟨z,hz⟩ : U)) hsource
  change z∈(chartAt (ComplexModel n) p).target at h
  exact h

theorem nativeIdentityChart_zero (U : Opens (ComplexModel n)) (p : U)
    (hp : (p : ComplexModel n)=0) :
    (nativeIdentityChart U p).toFun (chartAt (ComplexModel n) p p)=0 := by
  change chartAt (ComplexModel n) p p=0
  rw [native_chart_value]
  exact hp

theorem nativeIdentity_model_set (U : Opens (ComplexModel n)) (p : U) (B : Set (ComplexModel n)) :
    actualFixedFlatteningSet p (nativeIdentityChart U p) ((Subtype.val : U → ComplexModel n) ⁻¹' B)=
      (U : Set (ComplexModel n))∩B := by
  have hInv (z : ComplexModel n) (hz : z∈U) :
      (((chartAt (ComplexModel n) p).symm z : U) : ComplexModel n)=z := by
    have h:=(chartAt (ComplexModel n) p).right_inv (nativeIdentityChart_source U p hz)
    rw [native_chart_value] at h
    exact h
  ext z
  change (z∈U ∧ (((chartAt (ComplexModel n) p).symm z : U) : ComplexModel n)∈B) ↔
    z∈((U : Set (ComplexModel n))∩B)
  constructor
  · rintro ⟨hz,hzB⟩
    exact ⟨hz,(hInv z hz) ▸ hzB⟩
  · rintro ⟨hz,hzB⟩
    exact ⟨hz,(hInv z hz).symm ▸ hzB⟩

/-- The existing true flat strict origin is the literal identity-source origin. -/
theorem nativeIdentity_origin (U : Opens (ComplexModel n)) (p : U)
    (hp : (p : ComplexModel n)=0) (B : Set (ComplexModel n))
    (hB : B⊆(U : Set (ComplexModel n))) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n)
        ((Subtype.val : U → ComplexModel n) ⁻¹' B)) p (nativeIdentityChart U p)) 0)=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) B) := by
  have h:=originalFlattenedVanishingOriginIdeal_eq_model p (nativeIdentityChart U p)
    (nativeIdentityChart_source U p) (nativeIdentityChart_zero U p hp)
    ((Subtype.val : U → ComplexModel n) ⁻¹' B)
  rw [nativeIdentity_model_set,inter_eq_right.mpr hB] at h
  exact h

section ActualMap
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n X] [IsComplexManifold n Y]

def nativeStrictSet (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) (W : Set X) :
    Set (actualRebaseModel x Ω) :=
  (Subtype.val : actualRebaseModel x Ω → ComplexModel n) ⁻¹' actualFixedFlatteningSet x Ω W

omit [IsComplexManifold n X] in
theorem nativeStrictSet_eq (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) (W : Set X) :
    nativeStrictSet x Ω W=(fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' W := by
  ext z
  exact and_iff_right z.property

def prescribedSourceOpen {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) : Opens Y :=
  ⟨ρ ⁻¹' (actualRebaseWindow x Ω : Set X),
    (actualRebaseWindow x Ω).isOpen.preimage hρ.contMDiff.continuous⟩

def prescribedNativeMap {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target) :
    prescribedSourceOpen hρ x Ω → actualRebaseModel x Ω :=
  actualFlatCoordinateDiffeomorph Ω hsrc ∘
    (fun z : prescribedSourceOpen hρ x Ω=>(⟨ρ z.val,z.property⟩ : actualRebaseWindow x Ω))

theorem prescribedNativeMap_blowup {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target) :
    IsBlowupAlong n ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' C)
      (prescribedNativeMap hρ x Ω hsrc) := by
  let V:=actualRebaseWindow x Ω
  let e:=actualFlatCoordinateDiffeomorph Ω hsrc
  have hr:=BlowupRestrictOpen.isBlowupAlong_restrict hρ V
    (V.isOpen.preimage hρ.contMDiff.continuous)
  exact isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
    e.symm_apply_apply e.apply_symm_apply hr

omit [IsComplexManifold n Y] in
theorem prescribedNativeMap_inverse {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target)
    (z : prescribedSourceOpen hρ x Ω) :
    actualFlatteningInverseMap x Ω (prescribedNativeMap hρ x Ω hsrc z)=ρ z.val := by
  let e:=actualFlatCoordinateDiffeomorph Ω hsrc
  exact congrArg Subtype.val (e.symm_apply_apply (⟨ρ z.val,z.property⟩ : actualRebaseWindow x Ω))

/-- The whole actual strict set, not a centre-complement proxy, on the SAME
prescribed map restricted to the exact inverse image of the actual window. -/
theorem prescribedNativeMap_strict {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target) (W : Set X) :
    strictTransform n (prescribedNativeMap hρ x Ω hsrc) (nativeStrictSet x Ω W)=
      (Subtype.val : prescribedSourceOpen hρ x Ω → Y) ⁻¹' strictTransform n ρ W := by
  let V:=actualRebaseWindow x Ω
  let Z:=prescribedSourceOpen hρ x Ω
  let U:=actualRebaseModel x Ω
  let e : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U:=actualFlatCoordinateDiffeomorph Ω hsrc
  have h:=strictTransform_actual_open_coordinate_square ρ (prescribedNativeMap hρ x Ω hsrc)
    hρ.contMDiff (prescribedNativeMap_blowup hρ x Ω hsrc).contMDiff V Z e.symm
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z ∞)
    (fun z=>(prescribedNativeMap_inverse hρ x Ω hsrc z).symm) W
  have hi : (fun u : U=>(e.symm u : X))=
      (fun u : U=>actualFlatteningInverseMap x Ω u) := rfl
  have hj : (fun z : Z=>((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z ∞) z : Y))=
      (Subtype.val : Z → Y) := rfl
  rw [hi,hj] at h
  rw [nativeStrictSet_eq]
  exact h

theorem nativeStrictSet_analytic (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target)
    {W : Set X} (hW : IsComplexAnalyticSubset (n:=n) W) :
    IsComplexAnalyticSubset (n:=n) (nativeStrictSet x Ω W) := by
  rw [nativeStrictSet_eq]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_actual_flat_inverse Ω hsrc) hW

theorem prescribedNativeMap_hs {C : Set X} {ρ : Y → X} (hρ : IsBlowupAlong n C ρ)
    (x : X) (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target) (W : Set X)
    (z : prescribedSourceOpen hρ x Ω)
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n ρ W)) z.val ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (ρ z.val) ℓ) :
    ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n)
      (strictTransform n (prescribedNativeMap hρ x Ω hsrc) (nativeStrictSet x Ω W))) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) (nativeStrictSet x Ω W))
        (prescribedNativeMap hρ x Ω hsrc z) ℓ := by
  intro ℓ
  rw [prescribedNativeMap_strict]
  have hTarget:=hilbertSamuelAt_vanishing_actual_open_any (n:=n) (prescribedSourceOpen hρ x Ω)
    (strictTransform n ρ W) z ℓ
  have hSource:=hilbertSamuelAt_vanishing_actual_flat_inverse Ω hsrc W
    (prescribedNativeMap hρ x Ω hsrc z) ℓ
  change hilbertSamuelAt (vanishingIdeal (n:=n)
    ((fun u : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω u) ⁻¹' W))
    (prescribedNativeMap hρ x Ω hsrc z) ℓ=
    hilbertSamuelAt (vanishingIdeal (n:=n) W)
      (actualFlatteningInverseMap x Ω (prescribedNativeMap hρ x Ω hsrc z)) ℓ at hSource
  rw [←nativeStrictSet_eq,prescribedNativeMap_inverse] at hSource
  exact hTarget.trans ((hHS ℓ).trans hSource.symm)

end ActualMap

open HironakaActualOriginalFormalHSTransfer HironakaActualSameCurrentGeometricStage
 HironakaActualSameStageSelectedCarrierTransport HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualNormalMarkedDirection
 HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientAnalyticBlowup
 HironakaActualGlobalInheritedCut HironakaActualGeometricAdaptedCurrentFamily
 HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualFormalStandardMonomialHS HironakaActualOriginalFormalTaylor
 HironakaActualPointGeometricBennett HironakaActualOriginalAdaptedMarkedTransport
 GermIdealOrder InvertibleIdealQuotient HironakaActualFiniteCoefficientIdeals

/-- Every SAME inherited source member has its original marked origin order. -/
theorem historical_origin_orders
    {I : Ideal (HolGerm (ComplexModel n))}
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) :
    ∀a,G.germs a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val := by
  intro a
  rw [mem_analytic_ideal_iff_actualUnshifted_extension n,
    map_actualUnshifted_maximal_pow,mem_genuineFormalVariables_pow_iff_coefficients_zero]
  intro β hβ
  apply G.lower a β
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,normalExponentDegree,←Finsupp.degree_eq_sum] using hβ

/-- The reference of a true historical presentation is the whole origin HS
profile of its actual origin ideal, with no reference equality supplied. -/
theorem historical_presentation_reference
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hOrigin : I=originalCoherentOriginIdeal A) :
    hilbertSamuelValue I=R := by
  funext ℓ
  have hOrder : ∀a,translatedGerm 0 (PHS.representatives a)
      (PHS.holomorphicAt 0 PHS.zero_mem a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val := by
    intro a
    have hg : translatedGerm 0 (PHS.representatives a)
        (PHS.holomorphicAt 0 PHS.zero_mem a)=G.germs a := by
      rw [←PHS.sameGerms a]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z=>congrArg (PHS.representatives a) (add_zero z)
    rw [hg]
    exact historical_origin_orders G a
  have h:=(PHS.wholeHS 0 PHS.zero_mem).mp hOrder ℓ
  rw [hilbertSamuelAt_model_zero,←hOrigin] at h
  exact h

/-- The compatible historical flattening preserves the ENTIRE original
HS profile through its genuine inverse coordinate germ map. -/
theorem prescribed_flat_hilbertSamuelValue
    (I : Ideal (HolGerm (ComplexModel n)))
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0) :
    hilbertSamuelValue (prescribedFlatOriginIdeal I Φ hΦ0)=hilbertSamuelValue I := by
  let Ψ:=HironakaEmbeddedExceptional.LocalHolomorphicEquivAt.symmAt Φ hΦ0
  have hΨ0 : Ψ.toFun 0=0:=local_invFun_zero Φ hΦ0
  have he : localGermAlgEquiv Ψ hΨ0=(localGermAlgEquiv Φ hΦ0).symm := by
    apply AlgEquiv.ext
    intro F
    induction F using HolGerm.induction_on with
    | h f hf=>rfl
  funext ℓ
  have h:=hilbertSamuelValue_map_eq Ψ hΨ0 I ℓ
  simpa only [prescribedFlatOriginIdeal,he] using h

section NextStage
variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (n+1)) Z] [IsComplexManifold (n+1) Z]

/-- All geometric, full-record, prefix and selector witnesses of one actual
next stage.  The reference R is the original historical profile. -/
def ActualNextHistoricalStage
    (k : ℕ) (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (Q : MarkedIdeal (n+1) Z) {U : Opens (ComplexModel (n+1))} (π : Z → U)
    (W : Set U) (y : Z) (R : ℕ → ℕ) : Prop :=
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)=>
    normalExponentDegree a.val
  ∃q : Fin (n+1),q.val=k ∧
    ∃(e : Fin (n+1))(b : Fin (n+1) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (n+1)) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (n+1)) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (n+1)) y).source →
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector R PHS

/-- The genuine geometric constant-HS point condition derives the cut and
constructs all next-stage witnesses on the SAME native blowup. -/
theorem native_persistent_hs_produces_next_stage
    (k : ℕ) (hk : k+2≤n+1)
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (hred : ∀r,ActualInheritedPrefixReducedAt G r)
    (hContact : ∀r,actualFixedSelectorContactAt S G.germs r)
    (U : Opens (ComplexModel (n+1))) (h0U : (0 : ComplexModel (n+1))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I) →
      ComplexModel (n+1) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (n+1)))∩complexCoordinatePlane (n+1) k⊆
      cosupport (n+1) univ (actualPrincipalCoefficientIdeal (n+1) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (n+1) ((Subtype.val : U → ComplexModel (n+1)) ⁻¹'
      complexCoordinatePlane (n+1) k) π)
    (y : Z) (hy : (π y : ComplexModel (n+1))=0)
    (B : Set (ComplexModel (n+1))) (hB : B⊆(U : Set (ComplexModel (n+1))))
    (hBa : IsComplexAnalyticSubset (n:=n+1) ((Subtype.val : U → ComplexModel (n+1)) ⁻¹' B))
    (hOrigin : I=originalCoherentOriginIdeal (vanishingIdeal (n:=n+1) B))
    (R : ℕ → ℕ) (hReference : hilbertSamuelValue I=R)
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n+1)
      (strictTransform (n+1) π ((Subtype.val : U → ComplexModel (n+1)) ⁻¹' B))) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n+1) ((Subtype.val : U → ComplexModel (n+1)) ⁻¹' B)) (π y) ℓ) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (n+1) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (n+1)) ⁻¹' complexCoordinatePlane (n+1) k) π
    y∈Q.cosupp ∧ ActualNextHistoricalStage k I G S Q π
      ((Subtype.val : U → ComplexModel (n+1)) ⁻¹' B) y R := by
  obtain ⟨t,hn⟩ : ∃t,n=k+(t+1) := ⟨n-k-1,by omega⟩
  subst n
  let Φ:=nativeIdentityChart U (π y)
  have hΦsrc:=nativeIdentityChart_source U (π y)
  have hΦ0:=nativeIdentityChart_zero U (π y) hy
  have hOriginNative : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=k+(t+2))
        ((Subtype.val : U → ComplexModel (k+(t+2))) ⁻¹' B)) (π y) Φ) 0) :=
    hOrigin.trans (nativeIdentity_origin U (π y) hy B hB).symm
  have hcut:=(exists_actual_hs_equal_controlled_entry I G hmem hw hred U h0U c hc hrep hCos
    E π hπ y hy ((Subtype.val : U → ComplexModel (k+(t+2))) ⁻¹' B)
    Φ hΦsrc hΦ0 rfl rfl hOriginNative hHS).1
  refine ⟨hcut,?_⟩
  rw [←hReference]
  dsimp only [ActualNextHistoricalStage]
  let q : Fin (k+(t+2)):=⟨k,by omega⟩
  refine ⟨q,rfl,?_⟩
  have hTail : actualTangentCentreVariables k (t+2)=Set.Ici q := by
    ext i
    simp only [actualTangentCentreVariables_eq_tail,mem_ofPred_eq,mem_Ici,Fin.le_def,q]
  have hStage:=exists_actual_geometric_stage_prescribed_weighted_source I G hmem hw S hred hContact
    U h0U c hc hrep hCos E π hπ y hy ((Subtype.val : U → ComplexModel (k+(t+2))) ⁻¹' B)
    hBa Φ hΦsrc hΦ0 rfl rfl hOriginNative hcut
  obtain ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hRest⟩:=hStage
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,?_,hRest⟩
  simpa only [hTail] using hSquare

end NextStage

section HSRebase
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (n+1)) X] [IsComplexManifold (n+1) X]

/-- Strengthened, transparent OUTPUT laws: the prescribed actual next
constant-HS point produces its next entire historical stage. -/
def ActualPrescribedHSRebaseLaws
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
        z∈Qnext.cosupp ∧ ActualNextHistoricalStage k If T.family T.historicalSelector Qnext
          π (nativeStrictSet x Ω W) z R)

/-- Compose the SAME produced weighted rebase with true geometric HS
persistence; every origin/reference/cut/neighbourhood input is derived. -/
theorem hs_rebase_of_weighted_stage
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
    (hOrigin : I=originalCoherentOriginIdeal (actualHistoricalStageSheaf x Θ P.chart W))
    (hWa : IsComplexAnalyticSubset (n:=n+1) W)
    (hWeightedRebase : ActualPrescribedWeightedRebaseLaws Q x Θ P W hspan S R PHS) :
    ActualPrescribedHSRebaseLaws Q x Θ P W hspan S R PHS := by
  intro Y _ _ _ Cnext ρ hρ hxC hC
  obtain ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hWeighted,hwFlat,hFlatCos⟩:=
    hWeightedRebase Y Cnext ρ hρ hxC hC
  refine ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hWeighted,hwFlat,hFlatCos,?_⟩
  intro hk z hz hHS
  let Ω:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
  let U:=actualRebaseModel x Ω
  let F:=prescribedFlatFunctions T P.currentFunctions
  let If:=prescribedFlatOriginIdeal I T.chart T.chart_zero
  let π:=prescribedNativeMap hρ x Ω hΩsrc
  have h0U : (0 : ComplexModel (n+1))∈U := by
    change (0 : ComplexModel (n+1))∈Ω.target
    have hzero : Ω.toFun (chartAt (ComplexModel (n+1)) x x)=0:=hΩ0
    simpa only [hzero] using Ω.mapsTo_toFun Ω.center_mem_source
  have hy : (π z : ComplexModel (n+1))=0 := by
    change Ω.toFun (chartAt (ComplexModel (n+1)) x (ρ z.val))=0
    rw [hz]
    exact hΩ0
  have hπ : IsBlowupAlong (n+1) ((Subtype.val : U → ComplexModel (n+1)) ⁻¹'
      complexCoordinatePlane (n+1) k) π := by
    have h:=prescribedNativeMap_blowup hρ x Ω hΩsrc
    rw [hCentre] at h
    exact h
  have hc (a) : MDifferentiableOn 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (F a) U :=
    mdifferentiableOn_iff_differentiableOn.mpr (hWeighted.2.1 a)
  have hrep (a) : HolGerm.mk (F a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=
      T.family.germs a := hWeighted.1 a
  have hCos (a) : (U : Set (ComplexModel (n+1)))∩complexCoordinatePlane (n+1) k⊆
      cosupport (n+1) univ (actualPrincipalCoefficientIdeal (n+1) (F a)) (normalExponentDegree a.val) :=
    hFlatCos a
  have hB : actualFixedFlatteningSet x Ω W⊆(U : Set (ComplexModel (n+1))) := fun _ h=>h.1
  have hBa:=nativeStrictSet_analytic x Ω hΩsrc hWa
  have hReference : hilbertSamuelValue If=R :=
    (prescribed_flat_hilbertSamuelValue I T.chart T.chart_zero).trans
      (historical_presentation_reference PHS hOrigin)
  have hPhase:=prescribedNativeMap_hs hρ x Ω hΩsrc W z hHS
  let E:=Q.E.map ((fun v : U=>actualFlatteningInverseMap x Ω v) ⁻¹' ·)
  have hStage:=native_persistent_hs_produces_next_stage k hk If T.family
    (fun a=>T.span.le (Ideal.subset_span ⟨a,rfl⟩)) hwFlat T.historicalSelector
    T.prefixes T.historicalSelector_contact U h0U F hc hrep hCos E π hπ z hy
    (actualFixedFlatteningSet x Ω W) hB hBa hFlatOrigin R hReference hPhase
  have hExact:=hNext.2.1
  rw [hCentre,hWeighted.2.2] at hExact
  exact ⟨hExact,hStage⟩

end HSRebase

/-- ORIGINAL source geometry and genuine geometric HS persistence internally
produce both the current historical stage and every next prescribed actual
constant-HS stage, with literal full-record restriction and original profile.
No controlled-cut or repeated-order/neighbourhood certificate is supplied. -/
theorem exists_actual_geometric_stage_prescribed_hs_successor
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS := by
  dsimp only
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
  have hcut:=(exists_actual_hs_equal_controlled_entry I G hmem hw hred U h0U c hc hrep hCos
    E π hπ y hy W Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS).1
  obtain ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,hRebaseLaws,hWeightedLaws⟩:=
    exists_actual_geometric_stage_prescribed_weighted_source I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hcut
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,?_⟩
  have hNextAnalytic:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa
  exact hs_rebase_of_weighted_stage Q y Θ P (strictTransform (d+(t+2)) π W)
    D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS
    hOriginCurrent hNextAnalytic hWeightedLaws

end
end Hironaka.HironakaActualPrescribedHSRecursion
