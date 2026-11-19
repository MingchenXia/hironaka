import Hironaka.Resolution.HironakaG8StableWindowTest
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

/-! A completed locally finite original TEST clears a compact task at a finite stage. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CompactStageLimit

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8SurfaceLimitEndpoint
  HironakaG8StableWindowTest ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaAdmissibleSequence
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaResolutionSpaceLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- Smoothness of the actual limit supplies a finite stage that clears
the whole compact task. Every later stage retains that clearance. -/
theorem exists_compact_task_cleared_at_finite_stage {n : ℕ} {X : CMfd.{0} n}
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower M (s.stage i).2)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj W)) (s.stage i).2)
    (hSmooth : IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W))
    (K : Set X) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ i ≥ N,
      Disjoint (singularSet (n := n) (strictTransform n (s.stage i).2.proj W))
        ((s.stage i).2.proj ⁻¹' K) := by
  classical
  let U (x : X) := stableWindow s hLF x
  let J (x : X) := stableIndex s hLF x
  have hLocal (x : X) :
      Disjoint (singularSet (n := n) (strictTransform n (s.stage (J x)).2.proj W))
        ((s.stage (J x)).2.proj ⁻¹' (U x : Set X)) := by
    let T := (s.stage (J x)).2
    have hS := (stable_window_completed_test s hLF x M hM hTest W hSing hSmooth).2.2
    apply disjoint_left.mpr
    intro z hz hzU
    let y : openPreimage T (U x) := ⟨z,hzU⟩
    have hy : y ∈ singularSet (n := n)
        (strictTransform n (restrict (U x) T).proj ((Subtype.val : U x → X) ⁻¹' W)) := by
      rw [strictTransform_restricted_tower (U x) T W,singularSet_preimage_val]
      exact hz
    obtain ⟨hyW,hyS⟩ := mem_singularSet_iff.mp hy
    obtain ⟨d,hd⟩ := hS.2 y hyW
    exact hyS d hd
  have hCover : K ⊆ ⋃ x, (U x : Set X) :=
    fun x _ => mem_iUnion.mpr ⟨x,point_mem_stableWindow s hLF x⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen) hCover
  refine ⟨F.sup J,?_⟩
  intro i hi
  apply disjoint_left.mpr
  intro z hz hzK
  obtain ⟨x,hx⟩ := mem_iUnion.mp (hF hzK)
  obtain ⟨hxF,hxz⟩ := mem_iUnion.mp hx
  have hj : J x ≤ i := (Finset.le_sup (f := J) hxF).trans hi
  have hPreserve := intrinsic_stage_regular_later W hW s hSing (J x) (U x) (hLocal x) (i-J x)
  rw [Nat.add_sub_of_le hj] at hPreserve
  exact disjoint_left.mp hPreserve hz hxz

end Hironaka.HironakaG8CompactStageLimit
