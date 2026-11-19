import Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Resolution.HironakaActualOriginalInitialHSPhase

/-! An ordinary original local embedding initializes the SAME held whole-HS
record. Its actual map to X is defined only on the genuine analytic carrier.
BP FIRST: original-local-embedding-initial-hs.tex. No initial engine,
successor history, global driver, stopping packet or new scalar action. -/
set_option autoImplicit false
open Set Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingInitialHS
noncomputable section
open Hironaka
  Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceIntrinsicHS HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualPrescribedCentreRebasing
  HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualInheritedNestedContactFlag
  HironakaActualInheritedCurrentSourceRelabel HironakaActualFixedInheritedSelector
  HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualLocalStrictSaturation HironakaEmbeddedAnalytic
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaHolomorphicPointJets
  HironakaRelativeNormalDeformationInitialRelations MarkedIdealBiholomorphism
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers ResolutionInvariantSpec CanonicalCentres
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicSingularLocus

attribute [local instance] originalStalkAlgebra

variable (X : SourceReducedComplexSpace) (e : LocalEmbedding X)
  (U : Opens (ComplexModel e.dim)) (V : Opens e.ambient)
  (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel e.dim),𝓘(ℂ,ComplexModel e.dim)⟯ V)

/-- A full map to the ORIGINAL AMBIENT manifold, not a map from U to X. -/
@[implicit_reducible]
def presentationMap : U → e.ambient := fun z => (η z : e.ambient)

theorem presentationMap_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel e.dim) ∞
      (presentationMap X e U V η) :=
  contMDiff_subtype_val.comp η.contMDiff

/-- The actual analytic carrier is separate from the whole ambient marked carrier. -/
@[implicit_reducible]
def presentationCarrier : Set U := presentationMap X e U V η ⁻¹' e.carrier

theorem presentationCarrier_analytic :
    IsComplexAnalyticSubset (n := e.dim) (presentationCarrier X e U V η) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (presentationMap_holomorphic X e U V η) e.analytic

/-- Actual subspace biholomorphism followed by the SAME native open restriction. -/
def presentationProjection :
    actualSubspaceLocallyRingedSpace (n := e.dim) (presentationCarrier X e U V η) ⟶
      actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier :=
  (actualSubspaceBiholomorphicIso η (presentationCarrier X e U V η)
    ((Subtype.val : V → e.ambient) ⁻¹' e.carrier) (fun _ => Iff.rfl)).hom ≫
      actualOpenSubspaceMap (n := e.dim) e.carrier V

/-- The two actual constructions agree as FULL locally ringed morphisms. -/
theorem presentationProjection_eq_actualSubspaceMap :
    presentationProjection X e U V η =
      actualSubspaceMap (presentationMap_holomorphic X e U V η) (fun _ hz => hz) := by
  exact (actualSubspaceMap_comp η.contMDiff contMDiff_subtype_val
    (C := presentationCarrier X e U V η)
    (D := (Subtype.val : V → e.ambient) ⁻¹' e.carrier)
    (E := e.carrier) (fun _ hz => hz) (fun _ hz => hz)).symm

theorem presentationProjection_inclusion :
    actualSubspaceInclusion (n := e.dim) (presentationCarrier X e U V η) ≫
        ChartedSpace.locallyRingedSpaceMap (presentationMap X e U V η)
          (presentationMap_holomorphic X e U V η) =
      presentationProjection X e U V η ≫ actualSubspaceInclusion (n := e.dim) e.carrier := by
  rw [presentationProjection_eq_actualSubspaceMap]
  exact actualSubspaceMap_inclusion (presentationMap_holomorphic X e U V η) (fun _ hz => hz)

/-- EVERY original ambient numerator, before identifying either whole quotient. -/
theorem presentationProjection_stalk (d : presentationCarrier X e U V η)
    (r : actualComplexStructureStalk (n := e.dim) (presentationMap X e U V η d.val)) :
    (presentationProjection X e U V η).stalkMap d
        ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap
          ⟨presentationMap X e U V η d.val,d.property⟩ r) =
      (actualSubspaceInclusion (n := e.dim) (presentationCarrier X e U V η)).stalkMap d
        ((ChartedSpace.locallyRingedSpaceMap (presentationMap X e U V η)
          (presentationMap_holomorphic X e U V η)).stalkMap d.val r) := by
  have hs := LocallyRingedSpace.stalkMap_congr_hom
    (presentationProjection X e U V η)
    (actualSubspaceMap (presentationMap_holomorphic X e U V η) (fun _ hz => hz))
    (presentationProjection_eq_actualSubspaceMap X e U V η) d
  change (presentationProjection X e U V η).stalkMap d =
    (actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalkSpecializes
      (specializes_of_eq (rfl :
        (⟨presentationMap X e U V η d.val,d.property⟩ : e.carrier) =
          ⟨presentationMap X e U V η d.val,d.property⟩)) ≫
      (actualSubspaceMap (presentationMap_holomorphic X e U V η) (fun _ hz => hz)).stalkMap d at hs
  rw [TopCat.Presheaf.stalkSpecializes_refl] at hs
  have hr := ConcreteCategory.congr_hom (hs.trans (Category.id_comp _))
    ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap
      ⟨presentationMap X e U V η d.val,d.property⟩ r)
  have h := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (presentationMap_holomorphic X e U V η)
      (fun _ hz => hz) d) r
  change (actualSubspaceMap (presentationMap_holomorphic X e U V η) (fun _ hz => hz)).stalkMap d
      ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap
        ⟨presentationMap X e U V η d.val,d.property⟩ r) =
    (actualSubspaceInclusion (n := e.dim) (presentationCarrier X e U V η)).stalkMap d
      ((ChartedSpace.locallyRingedSpaceMap (presentationMap X e U V η)
        (presentationMap_holomorphic X e U V η)).stalkMap d.val r) at h
  exact hr.trans h

theorem presentationProjection_point :
    presentationProjection X e U V η ≫ subspacePointMap (n := e.dim) e.carrier =
      subspacePointMap (n := e.dim) (presentationCarrier X e U V η) := by
  rw [presentationProjection_eq_actualSubspaceMap]
  exact actualSubspaceMap_point (presentationMap_holomorphic X e U V η) (fun _ hz => hz)

/-- Genuine original local embedding ONLY on the actual closed analytic D. -/
@[implicit_reducible]
def presentationLocalEmbedding : LocalEmbedding X where
  dim := e.dim
  ambient := U
  carrier := presentationCarrier X e U V η
  analytic := presentationCarrier_analytic X e U V η
  map := presentationProjection X e U V η ≫ e.map
  isOpenImmersion := by
    let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
    let : LocallyRingedSpace.IsOpenImmersion j := e.isOpenImmersion
    change LocallyRingedSpace.IsOpenImmersion
      (((actualSubspaceBiholomorphicIso η (presentationCarrier X e U V η)
        ((Subtype.val : V → e.ambient) ⁻¹' e.carrier) (fun _ => Iff.rfl)).hom ≫
          actualOpenSubspaceMap (n := e.dim) e.carrier V) ≫ j)
    infer_instance
  overPoint := by
    let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
    have hj : j ≫ X.obj.hom = subspacePointMap (n := e.dim) e.carrier := e.overPoint
    change (presentationProjection X e U V η ≫ j) ≫ X.obj.hom =
      subspacePointMap (n := e.dim) (presentationCarrier X e U V η)
    calc
      _ = presentationProjection X e U V η ≫ (j ≫ X.obj.hom) := Category.assoc _ _ _
      _ = presentationProjection X e U V η ≫ subspacePointMap (n := e.dim) e.carrier :=
        congrArg (fun f => presentationProjection X e U V η ≫ f) hj
      _ = _ := presentationProjection_point X e U V η

theorem presentationLocalEmbedding_toPoint (d : presentationCarrier X e U V η) :
    (presentationLocalEmbedding X e U V η).toPoint d =
      e.toPoint ⟨presentationMap X e U V η d.val,d.property⟩ := rfl

/-- The original-X inverse stalk map retains EVERY original ambient numerator. -/
theorem presentationLocalEmbedding_numerator (d : presentationCarrier X e U V η)
    (r : actualComplexStructureStalk (n := e.dim) (presentationMap X e U V η d.val)) :
    localEmbeddingStalkAlgEquiv X (presentationLocalEmbedding X e U V η) d
        (ambientToOriginalStalk X e ⟨presentationMap X e U V η d.val,d.property⟩ r) =
      (actualSubspaceInclusion (n := e.dim) (presentationCarrier X e U V η)).stalkMap d
        ((ChartedSpace.locallyRingedSpaceMap (presentationMap X e U V η)
          (presentationMap_holomorphic X e U V η)).stalkMap d.val r) := by
  let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
  let c : e.carrier := ⟨presentationMap X e U V η d.val,d.property⟩
  have hcomp := ConcreteCategory.congr_hom
    (LocallyRingedSpace.stalkMap_comp (presentationProjection X e U V η) j d)
    (ambientToOriginalStalk X e c r)
  calc
    _ = (presentationProjection X e U V η).stalkMap d
        (j.stalkMap c (ambientToOriginalStalk X e c r)) := hcomp
    _ = (presentationProjection X e U V η).stalkMap d
        ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r) := by
      change (presentationProjection X e U V η).stalkMap d
        (localEmbeddingStalkAlgEquiv X e c
          ((localEmbeddingStalkAlgEquiv X e c).symm
            ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c r))) = _
      rw [AlgEquiv.apply_symm_apply]
    _ = _ := presentationProjection_stalk X e U V η d r

/-- ONLY original X/e/c/intrinsic singularity initialize the SAME held520 record. -/
theorem exists_original_localEmbedding_initial_hs (c : e.carrier)
    (hSing : e.toPoint c ∈ intrinsicSingularLocus X.obj) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := e.dim)
        (chartAt (ComplexModel e.dim) c.val c.val))
      (_hsrc : Φ.source ⊆ (chartAt (ComplexModel e.dim) c.val).target)
      (hΦ0 : Φ.toFun (chartAt (ComplexModel e.dim) c.val c.val) = 0),
    ∃ (Ψ : LocalHolomorphicEquivAt (n := e.dim) (0 : ComplexModel e.dim))
      (hΨ0 : Ψ.toFun 0 = 0),
      let Ξ := currentCoordinateFlattening c.val Φ hΦ0 Ψ hΨ0
      ∃ (_hΞsrc : Ξ.source ⊆ (chartAt (ComplexModel e.dim) c.val).target)
        (_hΞ0 : Ξ.toFun (chartAt (ComplexModel e.dim) c.val c.val) = 0),
      let B := vanishingIdeal (n := e.dim) (actualFixedFlatteningSet c.val Ξ e.carrier)
      let I := originalCoherentOriginIdeal B
      ∃ (G : ActualAnalyticInheritedFamily e.dim 0 (analyticZeroTaylorIdeal e.dim I))
        (S : ActualFixedInheritedSelector
          (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal e.dim I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS B I G
          (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) c.val ℓ)),
        Ideal.span (Set.range G.germs) = I ∧
        (∀ i, G.germs i ∈ I) ∧
        (∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal e.dim I),
          0 < normalExponentDegree i.val) ∧
        (∀ k, ActualInheritedPrefixReducedAt G k) ∧
        (∀ k, actualFixedSelectorContactAt S G.germs k) ∧
        (∀ k, (actualFixedSelectorJacobian S G.germs k).det ≠ 0) ∧
        PHS.neighborhood ⊆ Ξ.target ∧
        (∀ ℓ, hilbertSamuelValue I ℓ =
          hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) c.val ℓ) ∧
      ∃ (V : Opens e.ambient)
        (η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel e.dim),𝓘(ℂ,ComplexModel e.dim)⟯ V),
        c.val ∈ V ∧
        (∀ z, (η z : e.ambient) = actualFlatteningInverseMap c.val Ξ z.val) ∧
        (∀ z ℓ, hilbertSamuelAt B z.val ℓ =
          hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) (η z : e.ambient) ℓ) ∧
        let U := presentationOpen PHS
        let σ := presentationMap X e U V η
        let D := presentationCarrier X e U V η
        let eU := presentationLocalEmbedding X e U V η
        let Q := initialWeightedRecord PHS σ ([] : List (Set e.ambient))
        IsInvDomain e.dim Q ∧
        Q.N = univ ∧ Q.E = [] ∧
        Q.cosupp = {z | ∀ ℓ,
          hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) (σ z) ℓ =
            hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) c.val ℓ} ∧
        Q.cosupp ⊆ σ ⁻¹' singularSet (n := e.dim) e.carrier ∧
        (⟨0,PHS.zero_mem⟩ : U) ∈ Q.cosupp ∧
        D = (Subtype.val : U → ComplexModel e.dim) ⁻¹'
          actualFixedFlatteningSet c.val Ξ e.carrier ∧
        σ ⟨0,PHS.zero_mem⟩ = c.val ∧
        (∀ d : D, eU.toPoint d = e.toPoint ⟨σ d.val,d.property⟩) ∧
        (∀ d : D, ∀ ℓ,
          originalStalkHS X (eU.toPoint d) ℓ = hilbertSamuelAt B d.val.val ℓ) ∧
        (∀ z : U, z ∈ Q.cosupp ↔
          ∃ hz : σ z ∈ e.carrier, ∀ ℓ,
            originalStalkHS X (e.toPoint ⟨σ z,hz⟩) ℓ =
              originalStalkHS X (e.toPoint c) ℓ) ∧
        (∀ d : D, d.val ∈ Q.cosupp →
          eU.toPoint d ∈ intrinsicSingularLocus X.obj) ∧
        ∀ (K : Set U), IsCompact K →
        ∀ (O : Opens U), (O : Set U) ⊆ K →
        ∃ (Y : CMfd e.dim) (T : BlowupTower (CMfd.of (n := e.dim) O) Y),
          IsCanonical (MarkedIdeal.pullback (Subtype.val : O → U) Q)
            ((CanonicalCentres.canonicalInvariant e.dim).inv
              (MarkedIdeal.pullback (Subtype.val : O → U) Q)) T ∧
          IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O → U) Q) T := by
  have hc : c.val ∈ singularSet (n := e.dim) e.carrier := by
    have h : c ∈ e.toPoint ⁻¹' intrinsicSingularLocus X.obj := hSing
    rw [intrinsicSingularLocus_localEmbedding_preimage X e] at h
    exact h
  obtain ⟨Φ,hsrc,hΦ0⟩ := NormalCrossings.exists_centred_coordinates (n := e.dim) c.val
  obtain ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,hMem,hw,hPrefix,hContact,hJac,hU,hOrigin,
    V,η,haV,hη,hCov,hDom,hCos,hContained,hZero,hPhase⟩ :=
    exists_original_initial_hs_phase e.carrier e.analytic c.val hc
      ([] : List (Set e.ambient)) (NormalCrossings.isSNCDivisor_nil (n := e.dim)) Φ hsrc hΦ0
  let Ξ := currentCoordinateFlattening c.val Φ hΦ0 Ψ hΨ0
  let U := presentationOpen PHS
  let σ := presentationMap X e U V η
  let D := presentationCarrier X e U V η
  refine ⟨Φ,hsrc,hΦ0,Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,hMem,hw,hPrefix,hContact,hJac,hU,
    hOrigin,V,η,haV,hη,hCov,hDom,rfl,rfl,hCos,hContained,hZero,?_,?_,?_,?_,?_,?_,hPhase⟩
  · ext z
    change σ z ∈ e.carrier ↔ z.val ∈ Ξ.target ∧
      actualFlatteningInverseMap c.val Ξ z.val ∈ e.carrier
    rw [← hη z]
    exact (and_iff_right (hU z.property)).symm
  · change (η ⟨0,PHS.zero_mem⟩ : e.ambient) = c.val
    rw [hη,actualFlatteningInverseMap_zero c.val Ξ hΞ0]
  · exact presentationLocalEmbedding_toPoint X e U V η
  · intro d ℓ
    rw [presentationLocalEmbedding_toPoint]
    exact (originalStalkHS_localEmbedding_eq X e ⟨σ d.val,d.property⟩ ℓ).trans
      (hCov d.val ℓ).symm
  · intro z
    constructor
    · intro hz
      have hs := hContained hz
      have hzC := (mem_singularSet_iff.mp hs).1
      have hEq := (Set.ext_iff.mp hCos z).mp hz
      refine ⟨hzC,fun ℓ => ?_⟩
      exact (originalStalkHS_localEmbedding_eq X e ⟨σ z,hzC⟩ ℓ).trans
        ((hEq ℓ).trans (originalStalkHS_localEmbedding_eq X e c ℓ).symm)
    · rintro ⟨hzC,hEq⟩
      apply (Set.ext_iff.mp hCos z).mpr
      intro ℓ
      exact (originalStalkHS_localEmbedding_eq X e ⟨σ z,hzC⟩ ℓ).symm.trans
        ((hEq ℓ).trans (originalStalkHS_localEmbedding_eq X e c ℓ))
  · intro d hd
    rw [presentationLocalEmbedding_toPoint]
    change ⟨σ d.val,d.property⟩ ∈ e.toPoint ⁻¹' intrinsicSingularLocus X.obj
    rw [intrinsicSingularLocus_localEmbedding_preimage X e]
    exact hContained hd

end
end Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingInitialHS
