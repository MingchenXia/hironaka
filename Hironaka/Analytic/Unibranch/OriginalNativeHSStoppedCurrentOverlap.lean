import Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedEndpointComparison
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap

/-! Actual STOP--STOP Context constructor, with no case oracle or future map.
Blueprint FIRST: original-native-hs-stopped-current-overlap.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedCurrentOverlap
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}
  (S : State X K₁) (T : State X K₂) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
  (heS : singularShadow S = ∅) (heT : singularShadow T = ∅)
  (c : Context S T L) (hL : IsCompact L) (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂)

include hL hL₁ hL₂ in
/-- The concrete terminal base case uses the SAME computed stops and literal prescribed endpoints. -/
theorem exists_context : ∃ d : Context (stopped S hK₁ heS) (stopped T hK₂ heT) L,
    d.openSet ≤ c.openSet := by
  let N := OriginalNativeHSStoppedEndpointComparison.neighbourhood S T hK₁ hK₂ heS heT
    c.openSet L hL c.contains hL₁ hL₂
  refine ⟨⟨N.openSet,N.compactClosure,N.contains,
    OriginalNativeHSStoppedEndpointComparison.closure_subset_stop_left S T hK₁ hK₂ heS heT
      c.openSet L hL c.contains hL₁ hL₂,
    OriginalNativeHSStoppedEndpointComparison.closure_subset_stop_right S T hK₁ hK₂ heS heT
      c.openSet L hL c.contains hL₁ hL₂,
    OriginalNativeHSStoppedEndpointComparison.comparison S T hK₁ hK₂ heS heT c.openSet
      c.compactClosure c.leftRange c.rightRange c.comparison c.square L hL c.contains hL₁ hL₂,
    OriginalNativeHSStoppedEndpointComparison.comparison_projection S T hK₁ hK₂ heS heT c.openSet
      c.compactClosure c.leftRange c.rightRange c.comparison c.square L hL c.contains hL₁ hL₂⟩,
    OriginalNativeHSStoppedEndpointComparison.open_le_old S T hK₁ hK₂ heS heT c.openSet L hL c.contains hL₁ hL₂⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedCurrentOverlap
