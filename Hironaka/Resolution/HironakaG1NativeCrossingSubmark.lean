import Hironaka.Resolution.HironakaG1AnchoredBoundaryTraceWitness
import Hironaka.Resolution.HironakaG1NativeCrossingGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionComposition

/-! An actual ordered boundary of the analytic two-axis crossing has submark exponent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.HironakaG1NativeCrossingSubmark
noncomputable section

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong HironakaG1NativeCrossingGeometry HironakaG1AnchoredBoundaryTraceWitness
  HironakaSmoothSubmersionComposition HironakaActualHistoricalNativeStageStep
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision

/-- The two analytic axes, with the first axis as the literal singleton
ordered boundary, furnish an actual native weighted record whose raw
boundary exponent is positive and strictly below its native mark. -/
theorem exists_actual_native_crossing_submark :
    ∃ (X : CMfd.{0} 2) (ι : X → M) (Q : MarkedIdeal 2 X) (x : X),
      Topology.IsOpenEmbedding ι ∧ ι x = origin ∧ IsInvDomain 2 Q ∧ Q.N = univ ∧
      Q.E = [ι ⁻¹' axis 0] ∧ x ∈ Q.cosupp ∧
      0 < divExpAlong 2 Q.N Q.ideal (ι ⁻¹' axis 0) x ∧
      divExpAlong 2 Q.N Q.ideal (ι ⁻¹' axis 0) x < Q.d ∧
      (∀ᶠ y in 𝓝 x, y ∈ ι ⁻¹' axis 0 → y ∈ ι ⁻¹' crossing) ∧
      (∃ᶠ y in 𝓝 x, y ∈ ι ⁻¹' axis 0 ∧ y ∉ Q.cosupp) ∧
      ∃ (Vtx : Finset (Fin 2 →₀ ℕ)) (S : ActualFixedInheritedSelector Vtx)
        (k : ℕ) (a : Fin k ≃ Vtx) (w : Fin k → CoordinateWord 2),
        ActualHistoricalNativePointPresentation S a w (ι ⁻¹' crossing) Q x := by
  exact exists_anchored_submark_boundary (M := CMfd.of (n := 2) M)
    crossing crossing_analytic origin crossing_origin_singular [axis 0]
    axis_zero_ordered_snc ⟨0, by decide⟩ (origin_mem_axis 0)
    (Eventually.of_forall fun _ hy => Or.inl hy) crossing_hs_drop_on_axis
    (centeredCoordinates origin) (centeredCoordinates_source origin) (centeredCoordinates_zero origin)

#print axioms exists_actual_native_crossing_submark

end
end Hironaka.HironakaG1NativeCrossingSubmark
