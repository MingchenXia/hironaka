import Hironaka.Resolution.HironakaG3DisjointActiveFootprint
import Hironaka.Resolution.HironakaG3SeparatedInheritedBoundary
import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingActiveInheritedOldSlot
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3DisjointActiveFootprint
  HironakaG3SeparatedInheritedBoundary HironakaG3RPureEmbedded RestrictEmptyTower HomogenizedGlueingTower

theorem varying_active_inherited_old_slot {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) (j : κ) :
    strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j) =
      chartIncl c ⁻¹' strictTransform n P (D j) := by
  let active : ι → Prop := fun i => (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
    r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card
  let A : {i // active i} → Set X := fun i => C i.val
  have hOver : CentresOver ((Subtype.val : c.U → X) ⁻¹' (⋃ i, A i)) c.T := by
    apply disjoint_class_centres_over_active_union C active W K ?_ ?_ c.U c.Y c.T c.mem.1
    · intro i hi U Y T hT
      change (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
        r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card at hi
      have hh := hCentres i U Y T hT
      rw [if_pos hi] at hh
      exact hh
    · intro i hi U Y T hT
      change ¬ ((containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
        r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card) at hi
      have hh := hCentres i U Y T hT
      rw [if_neg hi] at hh
      simpa only [preimage_empty] using hh
  have hDense : ∀ j, D j ⊆ closure (D j \ ⋃ i, A i) := by
    simpa only [A,active] using indexed_boundary_dense_off_varying_active_components C r D hC hLF hD hr hpure
  exact inherited_old_slot_eq_strict_trace_of_centres_over A D
    (fun i => (hC i.val).analytic.isClosed) (hLF.comp_injective Subtype.val_injective) hD.2.1 hDense hP c hOver j
end
end Hironaka.HironakaG3VaryingActiveInheritedOldSlot
