import Hironaka.Resolution.HironakaG3DisjointAtlasFootprint
import Hironaka.Resolution.HironakaG3BoundaryDenseOffComponents
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointActiveFootprint
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3GluedClassFootprint
  HironakaG3BoundaryDenseOffComponents HironakaActualLocallyFiniteBoundary
  HironakaG3IndexedContainingBoundary RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

private theorem centres_mono {n : ℕ} {X : CMfd.{0} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centres_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

private theorem empty_centres_over {n : ℕ} {X : CMfd.{0} n} (F : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsEmptyTower T → CentresOver F T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => ⟨empty_centres_over F T h.1, by rw [h.2]; exact empty_subset _⟩

/-- A disjoint chart has centres over the active component union, even when
inactive component classes occur in the atlas. -/
theorem disjoint_class_centres_over_active_union {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (active : ι → Prop) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hActive : ∀ (i : ι), active i → ∀ (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hInactive : ∀ (i : ι), ¬ active i → ∀ (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver (∅ : Set (CMfd.of (n := n) U)) T)
    (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : disjointWindowClass A W K U Y T) :
    CentresOver ((Subtype.val : U → X) ⁻¹' (⋃ i : {i // active i}, A i.val)) T := by
  rcases hT with ⟨i,_,hK⟩ | ⟨_,hEmpty⟩
  · by_cases hi : active i
    · apply centres_mono _ T (hActive i hi U Y T hK)
      intro x hx
      exact mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩
    · exact centres_mono (empty_subset _) T (hInactive i hi U Y T hK)
  · exact empty_centres_over _ T hEmpty

/-- The actual glued map has no exceptional points away from the active union. -/
theorem disjoint_atlas_active_footprint {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (active : ι → Prop) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hActive : ∀ (i : ι), active i → ∀ (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hInactive : ∀ (i : ι), ¬ active i → ∀ (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver (∅ : Set (CMfd.of (n := n) U)) T)
    {P : Z → X} (hP : IsGluedFrom (disjointWindowClass A W K) Z P) :
    exceptionalLocus n P ⊆ P ⁻¹' (⋃ i : {i // active i}, A i.val) ∧
      IsIsomorphismOver n P (⋃ i : {i // active i}, A i.val)ᶜ := by
  have hF : IsClosed (⋃ i : {i // active i}, A i.val) :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun i => hClosed i.val)
  refine ⟨glued_exceptional_subset _ hF ?_ hP, glued_isomorphism_over_compl _ hF ?_ hP⟩
  all_goals exact disjoint_class_centres_over_active_union A active W K hActive hInactive

/-- Original boundary members are dense off the actual active support when
all active components satisfy the small-or-avoiding alternative. -/
theorem indexed_boundary_dense_off_active_components {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (active : ι → Prop)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hSmall : ∀ i, active i → r i < n - 1 ∨ containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, active i → r i < n)
    (hpure : ∀ i, active i → C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∀ j, D j ⊆ closure (D j \ ⋃ i : {i // active i}, C i.val) := by
  exact indexed_boundary_dense_off_small_or_avoiding_components
    (fun i : {i // active i} => C i.val) (fun i => r i.val) D
    (fun i => hC i.val) (hLF.comp_injective Subtype.val_injective) hD
    (fun i => hSmall i.val i.property) (fun i => hr i.val i.property)
    (fun i => hpure i.val i.property)

/-- For the varying-contact selector, the active union excludes the top
contact branch, so the original indexed boundary is dense off that union. -/
theorem indexed_boundary_dense_off_varying_active_components {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∀ j, D j ⊆ closure (D j \ ⋃ i : {i //
      (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
        r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card}, C i.val) := by
  apply indexed_boundary_dense_off_active_components C r D _ hC hLF hD
  · intro i hi
    rcases hi with hzero | hstrict
    · exact Or.inr (Finset.card_eq_zero.mp hzero)
    · by_cases hzero : (containingLabels (C i) D (hC i).nonempty hD.1).card = 0
      · exact Or.inr (Finset.card_eq_zero.mp hzero)
      · left
        have hpos : 0 < (containingLabels (C i) D (hC i).nonempty hD.1).card := Nat.pos_of_ne_zero hzero
        omega
  · exact fun i _ => hr i
  · exact fun i _ => hpure i
end
end Hironaka.HironakaG3DisjointActiveFootprint
