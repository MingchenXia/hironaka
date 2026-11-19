import Hironaka.Resolution.HironakaActualNormalAllDirectionAnalyticSaturation
import Hironaka.Resolution.HironakaActualNormalZeroGeometricConverse
import Hironaka.Resolution.HironakaActualFixedInheritedSelectorDirections
import Hironaka.Resolution.HironakaActualFixedInheritedSelectorBlowup

/-! Genuine geometric all-direction converse and original historical-selector
consumers. HS is proved independently BEFORE using HS-to-selector legality.
No selector is reselected and no nonzero formal translation is made.
Source-only draft, not kernel checked. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalAllDirectionGeometricConverse
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualOriginalFormalTaylor
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalDeformationInitialRelations
  HironakaActualFormalInitialDiagram HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualRelativeNormalJetDivision
  HironakaActualAnalyticStrictGenerators HironakaActualPointGeometricBennett
  HironakaActualStrictPullbackSaturation HironakaActualNormalZeroAnalyticSaturation
  HironakaActualNormalZeroGeometricConverse HironakaActualNormalAllDirectionAnalyticSaturation
  HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
  HironakaActualFixedInheritedSelectorDirections HironakaActualFixedInheritedSelectorBlowup
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualFormalCoordinatePowerDivision
  HironakaActualRelativeStandardnessBlockSupport

/-- Every literal normal pivot lies in the genuine terminal normal block. -/
theorem normalZeroFirstIndex_le_normalPivot (d t : ℕ) (ht : 2 ≤ t) (j : Fin t) :
    normalZeroFirstIndex d t ht ≤ j.natAdd d := by
  change d + 0 ≤ d + j.val
  omega

/-- At ANY actual normal pivot/direction, natural marked orders of the SAME
analytic inherited family give the WHOLE genuine geometric strict ideal. -/
theorem original_geometric_normal_strict_eq_same_span_of_marked_orders
    (d t : ℕ) (ht : 2 ≤ t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n := d+t) W)
    (G : ActualAnalyticInheritedFamily (d+t) 0
      (analyticZeroTaylorIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))))
    (hmem : ∀ a, G.germs a ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici (normalZeroFirstIndex d t ht)) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex (d+t)
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G
      (normalZeroFirstIndex d t ht) (j.natAdd d) (normalZeroFirstIndex_le_normalPivot d t ht j) b hpower a ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ normalExponentDegree a.val) :
    originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) =
      sameAnalyticNormalNormalizedIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G
        (normalZeroFirstIndex d t ht) (j.natAdd d) (normalZeroFirstIndex_le_normalPivot d t ht j) b hpower := by
  obtain ⟨_M, _hbound, _hcolon, hs, _hhs⟩ := exists_same_normal_analytic_fixed_colon_and_hs_of_marked_orders (d+t)
    (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G hmem
      (normalZeroFirstIndex d t ht) (j.natAdd d) (normalZeroFirstIndex_le_normalPivot d t ht j) b hpower horder
  ext g
  exact (mem_original_analytic_strict_ideal_iff_exists_coordinate_power d t ht j b W hW g).trans
    (by simpa only [actualTangentCentreVariables_eq_Ici_first d t ht] using (hs g).symm)

/-- Every intrinsic geometric HS value at the ORIGINAL arbitrary normal chart
origin equals the source value, without any target numerical certificate. -/
theorem hilbertSamuelAt_geometric_normal_strict_eq_of_marked_orders
    (d t : ℕ) (ht : 2 ≤ t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n := d+t) W)
    (G : ActualAnalyticInheritedFamily (d+t) 0
      (analyticZeroTaylorIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))))
    (hmem : ∀ a, G.germs a ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici (normalZeroFirstIndex d t ht)) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex (d+t)
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G
      (normalZeroFirstIndex d t ht) (j.natAdd d) (normalZeroFirstIndex_le_normalPivot d t ht j) b hpower a ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ normalExponentDegree a.val)
    (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ =
        hilbertSamuelAt (vanishingIdeal (n := d+t) W) 0 ℓ := by
  rw [hilbertSamuelAt_model_zero, hilbertSamuelAt_model_zero,
    original_geometric_normal_strict_eq_same_span_of_marked_orders d t ht j b W hW G hmem hpower horder]
  exact hilbertSamuelValue_same_normal_ideal_eq_of_marked_orders (d+t)
    (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G hmem
      (normalZeroFirstIndex d t ht) (j.natAdd d) (normalZeroFirstIndex_le_normalPivot d t ht j) b hpower horder ℓ

/-- The original fixed historical selector is retained. Its chart legality and
ALL normalized contact blocks/Jacobians follow only AFTER the new independently
proved converse has supplied actual HS equality. -/
theorem actual_normal_marked_orders_preserve_same_historical_selector
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀ k, actualFixedSelectorContactAt S G.germs k) :
    ∃ hp : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n (Set.Ici q) ^ normalExponentDegree a.val,
    ∀ k,
      let J : Matrix (actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k)
          (actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k) ℂ :=
        actualNormalizedFixedSelectorJacobian (n := n) (K := analyticZeroTaylorIdeal n I) G S k (Set.Ici q) e hqe b hp
      (actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k ⊆ (Set.Ici q) \ {e} ∧
        ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k, b i = 0) ∧
      (∀ j : actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k,
        actualNormalizedFixedSelectorDerivative G S k (Set.Ici q) e hqe b hp j ∈
          actualFormalCoordinateIdeal n (actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k)) ∧
      J = actualFixedSelectorJacobian S G.germs k ∧
      J.det ≠ 0 := by
  have hformal := actual_analytic_normal_formal_hs_and_regular_of_marked_orders n I G hmem q e hqe b hpower horder
  have hm (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      actualUnshiftedTaylorAlgHom n (G.germs a) ∈ analyticZeroTaylorIdeal n I := Ideal.mem_map_of_mem _ (hmem a)
  have hchart := actual_normal_hs_equal_fixed_selector_chart_conditions G S hm (Set.Ici q) e hqe b hpower hred hadapt hformal.1
  let hp (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :=
    actualTaylor_mem_coordinateCentre_pow (n := n) (Set.Ici q) (normalExponentDegree a.val) (G.germs a) (hpower a)
  have hcontact := actual_normalized_fixed_selector_all_blocks_contact G S (Set.Ici q) e hqe b hp
    (fun k => (hchart k).1) hadapt (fun k => (hchart k).2)
  exact ⟨hp, fun k => ⟨hchart k, (hcontact k).1, (hcontact k).2.1, (hcontact k).2.2⟩⟩

end
end Hironaka.HironakaActualNormalAllDirectionGeometricConverse
