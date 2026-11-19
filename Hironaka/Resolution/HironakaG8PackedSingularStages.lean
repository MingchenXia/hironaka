import Hironaka.Resolution.HironakaG8FinitePartitionPacking
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8PackedSingularStages

open Hironaka.BlowupSequences BlowupTowers
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8OccupiedSlotComparison
  HironakaG8FinitePartitionPacking HironakaG8FiniteParallelGeometry HironakaG8SurfaceLimitEndpoint

variable {n : ℕ} {X : CMfd.{0} n}

private theorem intrinsic_prefix {A Y : CMfd.{0} n} (W : Set X)
    (P : BlowupTower X A) (T : BlowupTower A Y)
    (h : StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj W))
      (P.append T)) :
    StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj W)) P := by
  induction T with
  | refl => exact h
  | step T C π hπ ih => exact ih h.1

/-- Every packed centre lies in the intrinsic singular locus of the strict
transform at its actual packed prefix. -/
theorem blockPacking_intrinsic_stages {Y : CMfd.{0} n}
    {P G : BlowupTower X Y} {trace : List (Set X)} (h : BlockPacking X P G trace)
    (W : Set X)
    (hStage : StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj W)) P) :
    StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj W)) G := by
  induction h with
  | nil => trivial
  | @append A Y P G trace hPrefix T hDisj hBlowup ih =>
      have hBlock (i j : ℕ) (hij : i < j) (hj : j < T.length) :
          Disjoint (slotFootprint T i) (slotFootprint T j) := by
        rw [Set.disjoint_left]
        intro a hai haj
        exact Set.disjoint_left.mp (hDisj i j hij hj)
          (mem_image_of_mem P.proj hai) (mem_image_of_mem P.proj haj)
      refine ⟨ih (intrinsic_prefix W P T hStage),?_⟩
      change blockCentre T ⊆ singularSet (n := n) (strictTransform n G.proj W)
      rw [hPrefix.proj_eq]
      exact blockCentre_subset_singular isClosed_closure T hBlock (intrinsic_stage_tail W P T hStage)

end Hironaka.HironakaG8PackedSingularStages
