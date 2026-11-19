import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation
import Hironaka.Resolution.HironakaActualStrictPullbackSaturation

/-!
# Genuine geometric zero normal-chart converse from SAME inherited marked orders

The actual analytic geometric strict ideal is identified by the independently
proved whole exceptional-saturation theorem, not an HS-input strict dictionary.
The normal codimension is at least two. No arbitrary-direction adaptation or
neighbourhood presentation cosupport equality is asserted.

Source-only draft. No kernel acceptance is asserted.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroGeometricConverse
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalDeformationInitialRelations
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
  HironakaActualAnalyticStrictGenerators HironakaActualPointGeometricBennett
  HironakaActualStrictPullbackSaturation HironakaActualNormalZeroAnalyticSaturation

/-- The literal first normal coordinate, with its existence internally supplied
by the genuine geometric codimension bound. -/
def normalZeroFirstIndex (d t : ℕ) (ht : 2 ≤ t) : Fin (d+t) :=
  (⟨0, lt_of_lt_of_le Nat.zero_lt_two ht⟩ : Fin t).natAdd d

/-- The actual split normal coordinate set is the terminal coordinate set used
by the zero owner converse. No coordinate-compatibility certificate is input. -/
theorem actualTangentCentreVariables_eq_Ici_first (d t : ℕ) (ht : 2 ≤ t) :
    actualTangentCentreVariables d t = Set.Ici (normalZeroFirstIndex d t ht) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    change d + 0 ≤ d + j.val
    omega
  · intro hi
    change d + 0 ≤ i.val at hi
    have hi' := i.isLt
    refine ⟨⟨i.val-d, by omega⟩, Fin.ext ?_⟩
    change d + (i.val-d) = i.val
    omega

/-- At the adapted zero chart, the WHOLE genuine geometric strict ideal equals
the SAME inherited analytic normalized span, from natural marked orders alone.
The only geometric premise is that the original set is genuinely analytic. -/
theorem original_geometric_normal_zero_strict_eq_same_span_of_marked_orders
    (d t : ℕ) (ht : 2 ≤ t) (W : Set (ComplexModel (d+t)))
    (hW : IsComplexAnalyticSubset (n := d+t) W)
    (G : ActualAnalyticInheritedFamily (d+t) 0
      (analyticZeroTaylorIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))))
    (hmem : ∀ a, G.germs a ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici (normalZeroFirstIndex d t ht)) ^
      normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticZeroNormalizedVertex (d+t)
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G (normalZeroFirstIndex d t ht) hpower a ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ normalExponentDegree a.val) :
    originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t)
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (normalZeroFirstIndex d t ht) (fun _ => 0)) W)) =
      sameAnalyticZeroNormalizedIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
        G (normalZeroFirstIndex d t ht) hpower := by
  obtain ⟨_M, _hbound, _hcolon, hs, _hhs⟩ :=
    exists_same_zero_analytic_fixed_colon_and_hs_of_marked_orders (d+t)
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G hmem
      (normalZeroFirstIndex d t ht) hpower horder
  ext g
  have hg := mem_original_analytic_strict_ideal_iff_exists_coordinate_power d t ht
    (⟨0, lt_of_lt_of_le Nat.zero_lt_two ht⟩ : Fin t) (fun _ => 0) W hW g
  change g ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t)
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (normalZeroFirstIndex d t ht) (fun _ => 0)) W)) ↔ _ at hg
  exact hg.trans (by
    simpa only [actualTangentCentreVariables_eq_Ici_first d t ht, normalZeroFirstIndex] using (hs g).symm)

/-- All intrinsic geometric HS values at the actual zero-chart target follow
from SAME inherited marked orders. Neither target HS nor saturation is assumed. -/
theorem hilbertSamuelAt_geometric_normal_zero_strict_eq_of_marked_orders
    (d t : ℕ) (ht : 2 ≤ t) (W : Set (ComplexModel (d+t)))
    (hW : IsComplexAnalyticSubset (n := d+t) W)
    (G : ActualAnalyticInheritedFamily (d+t) 0
      (analyticZeroTaylorIdeal (d+t) (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))))
    (hmem : ∀ a, G.germs a ∈ originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici (normalZeroFirstIndex d t ht)) ^
      normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticZeroNormalizedVertex (d+t)
      (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G (normalZeroFirstIndex d t ht) hpower a ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ normalExponentDegree a.val)
    (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t)
      (strictTransform (d+t)
        (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (normalZeroFirstIndex d t ht) (fun _ => 0)) W)) 0 ℓ =
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) 0 ℓ := by
  rw [hilbertSamuelAt_model_zero, hilbertSamuelAt_model_zero,
    original_geometric_normal_zero_strict_eq_same_span_of_marked_orders d t ht W hW G hmem hpower horder]
  exact hilbertSamuelValue_same_zero_ideal_eq_of_marked_orders (d+t)
    (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) G hmem
      (normalZeroFirstIndex d t ht) hpower horder ℓ

end
end Hironaka.HironakaActualNormalZeroGeometricConverse
