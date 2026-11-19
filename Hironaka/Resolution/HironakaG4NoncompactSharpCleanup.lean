import Hironaka.Resolution.HironakaG4CertifiedSharpAtlas
import Hironaka.Resolution.HironakaG4CertifiedSharpFullComparison

/-! The sharp G4 cleanup on a possibly noncompact ambient manifold. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4NoncompactSharpCleanup

noncomputable section

open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaG3RTowerClass HironakaG3EmptyAwareBornSlots HironakaG4SharpTerminalAtlas
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedTraceComparison
  HironakaG4CertifiedSharpAtlas HironakaG4CertifiedSharpFullComparison

private theorem certified_sharp_history_comparisons {n : ℕ} (hn : 0 < n) :
    CertifiedSharpHistoryComparisons.{u} hn := by
  intro X X' Y Y' W E T T' e hW hE hDense hT hT'
  have geometry : NativeRetainedGeometry W E [] :=
    ⟨hW, by simpa only [List.append_nil] using hE,
      isTransverse_nil_of_isClosedSubmanifold hW, by simpa only [List.append_nil] using hDense⟩
  have geometry' := native_geometry_rebase geometry e
  exact sharpHistory_overlap hn n e hW hE hDense geometry'.carrier
    (by simpa only [List.map_nil, List.append_nil] using geometry'.full)
    (by simpa only [List.map_nil, List.append_nil] using geometry'.dense) rfl
    (filter_map_bijection e e.surjective E) hT hT'

/-- A single proper sharp cleanup realizes compatible actual finite
histories over every prescribed compact-enclosed open of the original
ambient manifold, with its entire original ordered SNC boundary. -/
theorem exists_glued_full_sharp_cleanup {n : ℕ} {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    ∃ (C : LocalTowerClass X) (Z : CMfd.{u} n) (P : Z → X),
      IsGluedSharpCleanup C W E Z P ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart C Z P, c.U = U :=
  exists_glued_full_sharp_cleanup_of_certified_comparison certified_sharp_history_comparisons hW hE

end
end Hironaka.HironakaG4NoncompactSharpCleanup
