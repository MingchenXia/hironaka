import Hironaka.Resolution.HironakaG4LocalizedProtectedWindow
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Invariant.MaxLocusLocal

/-! Well-formedness on a window descends to a smaller ambient open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4WellFormedSubopen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  NormalCrossings NormalCrossingsInvariance HironakaBaseChange MaxLocusLocal
  RelativePrincipalizationSpan GermIdealPullbackCalculus

variable {n : ℕ} {X : CMfd.{u} n}

/-- Global smoothness and coherence plus well-formedness on U imply
well-formedness after restriction to every ambient subopen V of U. -/
theorem wellFormed_pullback_val_of_subopen (D : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n D.N) (hI : D.ideal.IsCoherent)
    (U V : Opens X) (hVU : V ≤ U)
    (hU : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed) :
    (MarkedIdeal.pullback (Subtype.val : V → X) D).IsWellFormed := by
  let i : V → U := fun z => ⟨z.val, hVU z.property⟩
  have hi : IsOpenHoloEmbedding n i :=
    ⟨nestedOpens U V, (nestedOpensDiffeo (n := n) hVU).symm, fun _ => rfl⟩
  have hSNC := isSNCDivisor_map_preimage hi.pullsBackCoordinates hi.continuous hU.isSNCDivisor
  have hTr := isTransverse_preimage hi.pullsBackCoordinates hU.isTransverse
  refine ⟨isClosedSubmanifold_preimage_val hN V, isCoherent_pullback contMDiff_subtype_val hI, ?_, ?_⟩
  · simpa only [MarkedIdeal.pullback, List.map_map, Function.comp_def, Set.preimage_preimage] using hSNC
  · simpa only [MarkedIdeal.pullback, List.map_map, Function.comp_def, Set.preimage_preimage] using hTr

end
end Hironaka.HironakaG4WellFormedSubopen
