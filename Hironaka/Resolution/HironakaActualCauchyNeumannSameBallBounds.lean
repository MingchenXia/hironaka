import Hironaka.Resolution.HironakaActualCauchyNeumannDivision
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Explicit bounds for the SAME actual Neumann quotient and remainder sums
on the SAME unchanged coordinate ball. All estimates use the public actual
iterate theorem and public ConcreteNeumannData fields; the private mother
component_bounds is not accessed. The bound M can depend on the numerator,
but the given ball and literal sum functions are unchanged.
This is a lower adapter for BP3 uniform translated division, not a separate
blueprint node or a uniform-family/HS producer. Source-only initial draft;
no elaboration, object or acceptance is claimed. -/
set_option autoImplicit false
open Set Metric

namespace Hironaka.HironakaActualCauchyNeumannSameBallBounds
noncomputable section
open HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualCauchyEnumeratedPartition
  HironakaActualCauchyNeumannDivision

variable {n k : ℕ}

private theorem actual_neumann_component_norm_bounds {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ}
    (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M)
    (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) :
    (∀ N j, ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖arrayQuotient (R/2) w j (diagramNeumannIter R w H h N) z‖ ≤
        (D.quotientConstant j * M) * (1/2 : ℝ)^N) ∧
    ∀ N, ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖arrayRemainder (R/2) w (diagramNeumannIter R w H h N) z‖ ≤
        (D.remainderConstant * M) * (1/2 : ℝ)^N := by
  have hi := diagramNeumannIter_differentiableOn_and_norm_le hR D hHd hHb hM hhd hhb
  constructor
  · intro N j z hz
    exact (D.quotient_bound _ _ (hi N).1 (hi N).2 j z hz).trans_eq (by ring)
  · intro N z hz
    exact (D.remainder_bound _ _ (hi N).1 (hi N).2 z hz).trans_eq (by ring)

/-- The original actual Neumann sums have explicit component, whole finite
quotient-tuple and remainder bounds on the SAME ball. No output radius is
lost: R/2 remains only the original native Cauchy contour parameter. -/
theorem neumannSums_same_ball_norm_bounds {R M : ℝ} (hR : 0 < R)
    {w : Fin k → CoordinateWord n} (D : ConcreteNeumannData R w)
    {H : Fin k → CoordinateSpace n → ℂ}
    (hHd : ∀ j, DifferentiableOn ℂ (H j) (ball 0 R))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖H j z‖ ≤ D.epsilon)
    {h : CoordinateSpace n → ℂ} (hM : 0 ≤ M)
    (hhd : DifferentiableOn ℂ h (ball 0 R))
    (hhb : ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) :
    (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖neumannQuotientSum R w H h j z‖ ≤ 2 * D.quotientConstant j * M) ∧
    (∀ z ∈ ball (0 : CoordinateSpace n) R,
      ∑ j, ‖neumannQuotientSum R w H h j z‖ ≤
        (2 * ∑ j, D.quotientConstant j) * M) ∧
    ∀ z ∈ ball (0 : CoordinateSpace n) R,
      ‖neumannRemainderSum R w H h z‖ ≤ 2 * D.remainderConstant * M := by
  obtain ⟨hqb, hrb⟩ := actual_neumann_component_norm_bounds hR D hHd hHb hM hhd hhb
  have hquot (j : Fin k) (z : CoordinateSpace n) (hz : z ∈ ball 0 R) :
      ‖neumannQuotientSum R w H h j z‖ ≤ 2 * D.quotientConstant j * M := by
    have hg : HasSum (fun N : ℕ => (D.quotientConstant j * M) * (1/2 : ℝ)^N)
        ((D.quotientConstant j * M) * 2) :=
      HasSum.mul_left (D.quotientConstant j * M) hasSum_geometric_two
    change ‖∑' N, arrayQuotient (R/2) w j (diagramNeumannIter R w H h N) z‖ ≤ _
    exact (tsum_of_norm_bounded hg (fun N => hqb N j z hz)).trans_eq (by ring)
  refine ⟨hquot, ?_, ?_⟩
  · intro z hz
    calc
      _ ≤ ∑ j, 2 * D.quotientConstant j * M :=
        Finset.sum_le_sum fun j _ => hquot j z hz
      _ = (2 * ∑ j, D.quotientConstant j) * M := by
        simp only [Finset.mul_sum, Finset.sum_mul]
  · intro z hz
    have hg : HasSum (fun N : ℕ => (D.remainderConstant * M) * (1/2 : ℝ)^N)
        ((D.remainderConstant * M) * 2) :=
      HasSum.mul_left (D.remainderConstant * M) hasSum_geometric_two
    change ‖∑' N, arrayRemainder (R/2) w (diagramNeumannIter R w H h N) z‖ ≤ _
    exact (tsum_of_norm_bounded hg (fun N => hrb N z hz)).trans_eq (by ring)

end
end Hironaka.HironakaActualCauchyNeumannSameBallBounds
