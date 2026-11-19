import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryClass
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedVisibleChartWindow
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaG3RTowerClass HironakaG3RBoundaryEmbedded
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaDisjointFiniteControlledHistory HironakaG3EmptyAwareFullBoundary
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
  (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X) {P : Z → X}

/-- A finite visible window is the actual stopped window or belongs to an empty chart. -/
def separatedWindowWitness (c : TowerChart (finiteVisibleClass
    (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) (R : Finset κ) : Prop :=
  (∀ j, (D j ∩ (c.U : Set X)).Nonempty → j ∈ R) ∧
    ((∃ i, c.U ≤ W i ∧ bdryClass (C i) (r i) ((R.sort (· ≤ ·)).map D) c.U c.Y c.T) ∨
      ((c.U : Set X) ⊆ (⋃ i, C i)ᶜ ∧ IsEmptyTower c.T))

theorem exists_separated_chart_window (c : TowerChart (finiteVisibleClass
    (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) :
    ∃ R, separatedWindowWitness C r D W c R := by
  rcases c.mem.1 with ⟨i,hUW,R,hVis,hStop⟩ | ⟨hAvoid,hEmpty⟩
  · exact ⟨R,hVis,Or.inl ⟨i,hUW,hStop⟩⟩
  · obtain ⟨R,hVis⟩ := c.mem.2
    exact ⟨R,hVis,Or.inr ⟨hAvoid,hEmpty⟩⟩

def separatedChartWindow (c : TowerChart (finiteVisibleClass
    (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) : Finset κ :=
  Classical.choose (exists_separated_chart_window C r D W c)

theorem separated_chart_window_spec (c : TowerChart (finiteVisibleClass
    (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) :
    separatedWindowWitness C r D W c (separatedChartWindow C r D W c) :=
  Classical.choose_spec (exists_separated_chart_window C r D W c)

/-- The transformed list only depends on the boundary list and physical tower. -/
theorem transformed_boundary_independent_of_ideal {Y : CMfd.{0} n}
    (E : List (Set X)) (J₁ J₂ : GermIdeal n X) (T : BlowupTower X Y) :
    (geoTransformAlong (fullMarked E J₁) T).E = (geoTransformAlong (fullMarked E J₂) T).E := by
  rw [boundary_decomp,boundary_decomp]
  rfl
end
end Hironaka.HironakaG3SeparatedVisibleChartWindow
