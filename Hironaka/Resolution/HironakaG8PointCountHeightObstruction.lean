import Hironaka.Resolution.HironakaG8PointCountRank
import Hironaka.Resolution.HironakaG8AnalyticFootprintHeightExample

/-! The fixed-point height bound does not bound paths that change points. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8PointCountHeightObstruction

open HironakaG8PointCountRank HironakaG8StageRankCoherence
open HironakaG8AnalyticFootprintHeightExample HironakaG8CountablePlaneSheets

theorem analytic_uniform_local_height_but_no_rank :
    (∀ x : PlaneSheets, ∀ b l,
      DependencyPath (fun a b => analyticChronology a b ∧
        x ∈ analyticChainFootprint a ∧ x ∈ analyticChainFootprint b) l b → l ≤ 3) ∧
    ¬ ∃ rank : Option ℕ → ℕ, ∀ {a b}, analyticSpatialBefore a b → rank a < rank b := by
  refine ⟨?_,no_weak_rank_analyticSpatialBefore⟩
  intro x b l hPath
  have hBound := local_path_length_le_count analyticChainFootprint analyticChronology
    (fun ha hb => analyticChronology_trans ha hb) analyticChronology_irrefl
    analyticChainFootprint_locallyFinite.point_finite x hPath
  obtain ⟨U,hx,F,hCard,hF⟩ := analyticChainFootprint_uniform_local_width x
  have hSub : pointPredecessors analyticChainFootprint analyticChronology x b ⊆ (F : Set _) := by
    intro a ha
    exact hF a ⟨x,ha.1,hx⟩
  exact hBound.trans ((Set.ncard_le_ncard hSub F.finite_toSet).trans (by simpa using hCard))

end Hironaka.HironakaG8PointCountHeightObstruction
