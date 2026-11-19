import Hironaka.Geometry.MonomialBlowupTowerChartContext
import Hironaka.Geometry.MonomialBlowupTowerRange

/-! Exact open-range coverage for the separately checked actual successor chart maps. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerCharts.StepContext

open Algebra.NodeBlowupChart MonomialBlowupTowerBase BlowupGluing MonomialBlowupTowerRange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A]
    {l : List A} {n : ℕ} {P t : A} {b : List A}
    (S : ChartData l n P (t * b.prod))
    [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)]

local instance (i : S.I) : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
local instance : IsOpenImmersion S.continuationInclusion := S.continuation_open

theorem fresh_next_opensRange (hprefix : (l.take (n + 1)).prod = P * t) :
    (freshInclusion S hprefix).opensRange ⊔ (nextInclusion S hprefix).opensRange =
      blowupStructure (center (l := l) (n := n)) ⁻¹ᵁ S.continuationInclusion.opensRange := by
  have hcont : (MonomialBlowupIteration.continuationChartInclusion t b.prod).opensRange =
      (tChartInclusion t b.prod).opensRange := by
    dsimp only [MonomialBlowupIteration.continuationChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso]
  have hcov : (uChartInclusion t b.prod).opensRange ⊔
      (MonomialBlowupIteration.continuationChartInclusion t b.prod).opensRange = ⊤ := by
    rw [hcont, NodeBlowupCover.chartInclusions_sup_opensRange]
  change (uChartInclusion t b.prod ≫
      ((continuationIso S).inv ≫ continuationGlobalMap S hprefix)).opensRange ⊔
    (MonomialBlowupIteration.continuationChartInclusion t b.prod ≫
      ((continuationIso S).inv ≫ continuationGlobalMap S hprefix)).opensRange = _
  rw [opensRange_comp_sup_eq _ _ _ hcov,
    Scheme.Hom.opensRange_comp_of_isIso, continuationGlobalMap_opensRange]

/-- Coverage follows only from exact open ranges, with no evaluation of inverse isomorphisms. -/
theorem covers (hprefix : (l.take (n + 1)).prod = P * t) :
    ∀ y : blowup (center (l := l) (n := n)),
      (∃ i, y ∈ (oldInclusion S hprefix i).opensRange) ∨
        y ∈ (freshInclusion S hprefix).opensRange ∨ y ∈ (nextInclusion S hprefix).opensRange := by
  let : ∀ i, IsOpenImmersion (S.inclusion i) := S.inclusion_open
  let : IsOpenImmersion S.continuationInclusion := S.continuation_open
  exact covers_of_preimage_ranges (blowupStructure (center (l := l) (n := n)))
    S.inclusion S.continuationInclusion (oldInclusion S hprefix)
    (freshInclusion S hprefix) (nextInclusion S hprefix)
    S.covers (oldInclusion_opensRange S hprefix) (fresh_next_opensRange S hprefix)

end Hironaka.Geometry.MonomialBlowupTowerCharts.StepContext
