import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
import Hironaka.Resolution.HironakaG3IndexedTopContact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TopContactEmptyClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3IndexedContainingBoundary HironakaG3IndexedTopContact
  RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

def emptyTowerClass {n : ℕ} {X : CMfd.{0} n} : LocalTowerClass X := fun _ _ T => IsEmptyTower T

theorem empty_tower_class_comparisons {n : ℕ} {X : CMfd.{0} n} : HasComparisons (emptyTowerClass (X := X)) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  exact avoiding_overlap_comparison U₁ U₂ T₁ T₂ (empty_avoids _ T₁ h₁) (empty_avoids _ T₂ h₂)

theorem empty_tower_class_centres_over {n : ℕ} {X : CMfd.{0} n} (F : Set X) :
    ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      emptyTowerClass U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F) T := by
  intro U Y T
  induction T with
  | refl => intro _; trivial
  | step T C π hπ ih =>
    intro hT
    exact ⟨ih hT.1,by rw [hT.2]; exact empty_subset _⟩

theorem top_contact_empty_class_data {n r : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (C : Set X) (D : κ → Set X) (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r) :
    HasComparisons (emptyTowerClass (X := X)) ∧
      (∀ U : Opens X, ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), emptyTowerClass U Y T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        emptyTowerClass U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C) T) ∧
      IsClosedSubmanifold n C ∧ (∀ x ∈ C, RegularAtDim (n := n) C x r) ∧ HasNormalCrossingsWithBoundary C D := by
  obtain ⟨O,hO,hSmooth,hReg,hNC⟩ := indexed_top_contact_already_normal C D hC hD hpure htop
  exact ⟨empty_tower_class_comparisons,fun U => ⟨CMfd.of (n := n) U,.refl,trivial⟩,
    empty_tower_class_centres_over C,hSmooth,hReg,hNC⟩
end
end Hironaka.HironakaG3TopContactEmptyClass
