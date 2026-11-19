import Hironaka.Resolution.HironakaSmoothSubmersionRelativeControlledTower
import Hironaka.Resolution.HironakaOriginalStoppedPrefixSmoothComparison
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaG8SurfaceSingularPhase
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SubmersionSingularHistory
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaSmoothSubmersionCartesianTower
  HironakaOriginalStoppedPrefixSmoothComparison HironakaOriginalCanonicalDimensionList

/-- Actual smooth base change preserves literal singular-centred stages. -/
theorem actual_pullback_singular_stages {n m : ℕ} {X D : CMfd.{0} n} {Y D' : CMfd.{0} m}
    {f : Y → X} (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    {Q : BlowupTower Y D'} {T : BlowupTower X D} {g : D' → D}
    (h : IsActualTowerPullback f Q T g)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    StageCentres (fun P C => C ⊆ singularSet (n := m) (strictTransform m P.proj (f ⁻¹' W))) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hStage.1,?_⟩
    let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
      change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
      simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hStage.1)
    have heq :=  HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hf h O hp.1 W hDense
    change g ⁻¹' C ⊆ singularSet (n := m) (strictTransform m Q.proj (f ⁻¹' W))
    rw [heq,singularSet_preimage_eq hg]
    exact preimage_mono hStage.2
end
end Hironaka.HironakaG8SubmersionSingularHistory
