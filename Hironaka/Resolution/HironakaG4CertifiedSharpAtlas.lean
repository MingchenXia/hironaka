import Hironaka.Resolution.HironakaG4CertifiedSharpHistory
import Hironaka.Resolution.HironakaG4DenseSharpChartAtlas
import Hironaka.Resolution.HironakaG4OrderedContainmentAtlasUniverse

/-! The comparison of certified actual histories is the remaining input
to the full sharp atlas. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CertifiedSharpAtlas
noncomputable section

open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  RegularPointDimension HironakaG3RTowerClass G3UniverseEmptyAwareCore
  HironakaG4CertifiedSharpHistory HironakaG4DenseSharpChartAtlas
  HironakaG4OrderedContainmentAtlas HironakaG4OrderedContainmentAtlasUniverse
  HironakaG4SharpTerminalAtlas HironakaG4RetainedEquivariantRowService
  HironakaG4CompactRelativeSharpDimension

variable {n : ℕ}

/-- Physical comparison of the fully certified sharp terminal histories
on the same carrier and ordered boundary under a source biholomorphism. -/
def CertifiedSharpHistoryComparisons (hn : 0 < n) : Prop :=
  ∀ {X X' Y Y' : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    SharpHistory hn n W E T → SharpHistory hn n (e ⁻¹' W) (E.map (e ⁻¹' ·)) T' →
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso e T' T η

/-- Every chart operation except comparison is provided by the actual
compact-relative certified construction. -/
theorem certified_sharp_chart_service (hn : 0 < n) (compare : CertifiedSharpHistoryComparisons.{u} hn) :
    DenseSharpChartService (SharpHistory.{u} hn n) := by
  refine ⟨sharpHistory_restrict,?_,compare,sharpHistory_terminal,?_⟩
  · intro X X' Y W E T hT e
    exact sharpHistory_rebase hn n e T hT
  · intro X W E hW hE hDense K hK
    have hDim : ∀ x ∈ W, ∃ d ≤ n, RegularAtDim (n := n) W x d := by
      intro x hx
      obtain ⟨d,hd⟩ := hW.2 x hx
      exact ⟨d,hd.1,hd⟩
    obtain ⟨V,hKV,Y,T,_,_,hCert⟩ :=
      compactRelativeCertifiedSharpCleanupsExist.{u} hn n X W E hW hE hDense hDim K hK
    exact ⟨V,hKV,Y,T,hCert⟩

/-- Certified comparison in the small universe suffices for one glued
full sharp cleanup map on the original ambient manifold. -/
theorem exists_glued_full_sharp_cleanup_of_certified_comparison
    (compare : ∀ hn : 0 < n, CertifiedSharpHistoryComparisons.{0} hn)
    {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    ∃ (C : LocalTowerClass X) (Z : CMfd.{u} n) (P : Z → X),
      IsGluedSharpCleanup C W E Z P ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart C Z P, c.U = U :=
  exists_glued_full_sharp_cleanup_of_dense_all_universes
    (fun hn => denseSharpAtlasService_of_charts (certified_sharp_chart_service hn (compare hn))) hW hE

end
end Hironaka.HironakaG4CertifiedSharpAtlas
