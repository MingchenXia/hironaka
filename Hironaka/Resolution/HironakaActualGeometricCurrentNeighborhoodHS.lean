import Hironaka.Resolution.HironakaActualGeometricAdaptedCurrentSelector
import Hironaka.Resolution.HironakaActualGermEquivLocalRealization
import Hironaka.Resolution.HironakaActualLocalHolomorphicOriginPullback
import Hironaka.Resolution.HironakaActualInheritedNeighborhoodMarkedHS
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Coherence.CartanIrreducible

/-! The internally produced CURRENT family gives an entire neighborhood HS
presentation of the literal pullback of the ORIGINAL geometric strict chart
sheaf, on a genuinely constructed common local coordinate domain. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeometricCurrentNeighborhoodHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 OkaRelationSheaf HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
 HironakaHolomorphicPointJets HironakaActualAnalyticBlowupTaylor
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
 HironakaActualInheritedNestedContactFlag HironakaActualNormalZeroAnalyticSaturation
 HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualInheritedSourcePermutationFamily HironakaActualNormalMarkedDirection
 HironakaRelativeNormalDeformationInitialRelations HironakaActualCoefficientAnalyticBlowup
 HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
 HironakaSmoothCentreNearbyStalks BlowupFlatCoordinates HironakaActualFixedInheritedSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualGermEquivLocalRealization HironakaActualLocalHolomorphicOriginPullback
 HironakaActualInheritedNeighborhoodMarkedHS HironakaActualInheritedHSContactContainment
 HironakaActualLocalStrictSaturation HironakaActualPointGeometricBennett
 HironakaActualFixedFlatteningHSComparison
 OkaIdealOperations HironakaHolomorphicJetRankLoci HironakaRelativeNormalCoherentSaturation
variable {n : ℕ}

/-- Literal current representatives generate the supplied ACTUAL geometric
chart sheaf on one neighborhood, and their original marks describe its
entire HS reference locus there. Every field is output data. -/
structure ActualGeometricInheritedNeighborhoodHS
    (A : GermIdeal n (ComplexModel n)) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (R : ℕ → ℕ) where
  representatives : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ
  holomorphicAtZero : ∀a,HolAt (representatives a) 0
  sameGerms : ∀a,HolGerm.mk (representatives a) (holomorphicAtZero a)=G.germs a
  neighborhood : Set (ComplexModel n)
  isOpen_neighborhood : IsOpen neighborhood
  zero_mem : (0 : ComplexModel n)∈neighborhood
  holomorphicOn : ∀a,DifferentiableOn ℂ (representatives a) neighborhood
  wholeGeneration : ∀y∈neighborhood,∀f,A.mem y f ↔ InSpanAt representatives y f
  holomorphicAt : ∀y∈neighborhood,∀a,HolAt (representatives a) y
  wholeHS : ∀y (hy : y∈neighborhood),
    (∀a,translatedGerm y (representatives a) (holomorphicAt y hy a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val) ↔
      ∀ℓ,hilbertSamuelAt A y ℓ=R ℓ

private def restrict_neighborhood
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS A I G R)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ActualGeometricInheritedNeighborhoodHS A I G R where
  representatives:=P.representatives
  holomorphicAtZero:=P.holomorphicAtZero
  sameGerms:=P.sameGerms
  neighborhood:=P.neighborhood∩O
  isOpen_neighborhood:=P.isOpen_neighborhood.inter hO
  zero_mem:=⟨P.zero_mem,h0O⟩
  holomorphicOn:=fun a=>(P.holomorphicOn a).mono inter_subset_left
  wholeGeneration:=fun y hy=>P.wholeGeneration y hy.1
  holomorphicAt:=fun y hy=>P.holomorphicAt y hy.1
  wholeHS:=fun y hy=>P.wholeHS y hy.1

private theorem neighborhood_presentation_of_origin_eq
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hspan : Ideal.span (range G.germs)=I) (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hI : I=originalCoherentOriginIdeal A) (R : ℕ → ℕ)
    (hReference : ∀ℓ,hilbertSamuelAt A 0 ℓ=R ℓ) :
    Nonempty (ActualGeometricInheritedNeighborhoodHS A I G R) := by
  subst I
  obtain ⟨H,hg,hG,U,hU,h0U,hHd,hgen,hhol,hHS⟩:=
    exists_actual_inherited_neighborhood_member_orders_iff_hs A hfg G hspan hred
  refine ⟨{
    representatives:=H
    holomorphicAtZero:=hg
    sameGerms:=hG
    neighborhood:=U
    isOpen_neighborhood:=hU
    zero_mem:=h0U
    holomorphicOn:=hHd
    wholeGeneration:=hgen
    holomorphicAt:=hhol
    wholeHS:=?_ }⟩
  intro y hy
  simpa only [hReference,actualInheritedOriginFormalIdeal,analyticZeroTaylorIdeal] using hHS y hy

section Geometric
variable {d t : ℕ} {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+(t+2))) X] [ChartedSpace (ComplexModel (d+(t+2))) Z]
 [IsComplexManifold (d+(t+2)) X] [IsComplexManifold (d+(t+2)) Z]

/-- The SAME internally produced current family presents the literal
pullback of the ORIGINAL geometric strict chart sheaf on a true neighborhood.
Current local finite generation, chart realization, whole generation and the entire HS
marked cosupport equality are conclusions, not supplied target certificates. -/
theorem exists_actual_geometric_current_neighborhood_whole_hs
    (π : Z → X)
    {C₀ : Set X} (hπ : IsBlowupAlong (d+(t+2)) C₀ π)
    (y : Z) (W : Set X) (hWa : IsComplexAnalyticSubset (n:=d+(t+2)) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (e : Fin (d+(t+2))) (he : d≤e.val) (b : Fin (d+(t+2)) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
    (hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
      chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z)))
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (hI : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    ∀hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
    (∀a,sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val) →
    let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y Θ) 0)
    let A₀:=vanishingIdeal (n:=d+(t+2)) (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
    ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃Λ : LocalHolomorphicEquivAt (n:=d+(t+2)) (0 : ComplexModel (d+(t+2))),
      ∃hΛ0 : Λ.toFun 0=0,∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      let A:=GermIdeal.pullback (m:=d+(t+2)) Λ.toFun A₀
      (actualAdaptedHistoricalCurrentSource D).ideal=
        Ideal.map (localGermAlgEquiv Λ hΛ0).toRingEquiv.toRingHom K ∧
      (actualAdaptedHistoricalCurrentSource D).ideal=originalCoherentOriginIdeal A ∧
      ∃P : ActualGeometricInheritedNeighborhoodHS A (actualAdaptedHistoricalCurrentSource D).ideal
        D.targetFamily (hilbertSamuelValue I),
      P.neighborhood⊆Λ.source ∧ MapsTo Λ.toFun P.neighborhood Θ.target ∧
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ := by
  dsimp only
  intro hp hOrder
  let q : Fin (d+(t+2)):=⟨d,by omega⟩
  have hW : (vanishingIdeal (n:=d+(t+2)) W).IsCoherent:=CartanIrreducible.cartanCoherence W hWa
  obtain ⟨f,hqf,hvf,E,D,hCurrent,hHS,hIntrinsic⟩:=
    exists_actual_geometric_current_source_and_historical_selector π hπ.contMDiff y W hW
      Φ hΦsrc hΦ0 e he b Θ hΘsrc hΘ0 hnormal I hI G hmem hred S hContact hp hOrder
  obtain ⟨Λ,hΛ0,hΛE⟩:=exists_localHolomorphicEquivAt_of_germ_equiv E
  let A₀:=vanishingIdeal (n:=d+(t+2)) (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
  let A:=GermIdeal.pullback (m:=d+(t+2)) Λ.toFun A₀
  have hSa:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa
  have hScoh : (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)).IsCoherent:=
    CartanIrreducible.cartanCoherence _ hSa
  have hfg₀ : IdealFGAt A₀.mem (0 : ComplexModel (d+(t+2))):=
    fixedFlattening_vanishing_local_fg _ hScoh y Θ hΘsrc hΘ0
  have hfg : IdealFGAt A.mem (0 : ComplexModel (d+(t+2))):=
    local_fg_pullback_of_holomorphic_germ Λ.toFun (local_toFun_holomorphic Λ) hΛ0 A₀ hfg₀
  have hHom : (compAlgHom Λ.toFun (local_toFun_holomorphic Λ) hΛ0).toRingHom=
      E.toRingEquiv.toRingHom := by
    change (localGermAlgEquiv Λ hΛ0).toRingEquiv.toRingHom=E.toRingEquiv.toRingHom
    rw [hΛE]
  have hModel:=originalFlattenedVanishingOriginIdeal_eq_model y Θ hΘsrc hΘ0
    (strictTransform (d+(t+2)) π W)
  have hOrigin:=origin_pullback_eq_of_holomorphic_germ Λ.toFun (local_toFun_holomorphic Λ) hΛ0 A₀ hfg₀
  rw [hHom,←hModel] at hOrigin
  have hCurrentOrigin : (actualAdaptedHistoricalCurrentSource D).ideal=originalCoherentOriginIdeal A:=
    hCurrent.trans hOrigin.symm
  have hReference (ℓ : ℕ) : hilbertSamuelAt A 0 ℓ=hilbertSamuelValue I ℓ := by
    rw [hilbertSamuelAt_model_zero,←hCurrentOrigin]
    exact hHS ℓ
  have hPresentation:=neighborhood_presentation_of_origin_eq A hfg
    (actualAdaptedHistoricalCurrentSource D).ideal D.targetFamily D.targetSpan D.targetPrefix
    hCurrentOrigin (hilbertSamuelValue I) hReference
  obtain ⟨P⟩:=hPresentation
  let O:=Λ.source∩Λ.toFun ⁻¹' Θ.target
  have hO : IsOpen O:=Λ.toFun_holomorphic.continuousOn.isOpen_inter_preimage
    Λ.isOpen_source Θ.isOpen_target
  have h0O : (0 : ComplexModel (d+(t+2)))∈O := by
    refine ⟨Λ.center_mem_source,?_⟩
    change Λ.toFun 0∈Θ.target
    rw [hΛ0]
    exact actualFlattening_target_zero_mem y Θ hΘ0
  let Q:=restrict_neighborhood P O hO h0O
  have hQsource : Q.neighborhood⊆Λ.source:=fun _ hz=>hz.2.1
  have hQtarget : MapsTo Λ.toFun Q.neighborhood Θ.target:=fun _ hz=>hz.2.2
  refine ⟨f,hqf,hvf,Λ,hΛ0,D,?_,hCurrentOrigin,Q,hQsource,hQtarget,hIntrinsic⟩
  rw [hΛE]
  exact hCurrent

end Geometric

end
end Hironaka.HironakaActualGeometricCurrentNeighborhoodHS
