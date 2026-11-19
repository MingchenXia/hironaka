import Hironaka.Resolution.HironakaG3DisjointActiveFootprint
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingContactActiveFootprint
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointActiveFootprint RestrictEmptyTower

def varyingActive {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hD : IsLocallyFiniteSNCDivisor n D) (i : ι) : Prop :=
  (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
    r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card

/-- The same varying-contact glued map is an isomorphism off the active
support, and each original boundary member is dense off that support. -/
theorem varying_contact_active_footprint {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hLF : LocallyFinite C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T →
      CentresOver ((Subtype.val : U → X) ⁻¹' (if varyingActive C r D hC hD i then C i else ∅)) T)
    {P : Z → X} (hP : IsGluedFrom (disjointWindowClass C W K) Z P) :
    (exceptionalLocus n P ⊆ P ⁻¹' (⋃ i : {i // varyingActive C r D hC hD i}, C i.val)) ∧
      IsIsomorphismOver n P (⋃ i : {i // varyingActive C r D hC hD i}, C i.val)ᶜ ∧
      ∀ j, D j ⊆ closure (D j \ ⋃ i : {i // varyingActive C r D hC hD i}, C i.val) := by
  have hFoot := disjoint_atlas_active_footprint C (varyingActive C r D hC hD) W K
    (fun i => (hC i).analytic.isClosed) hLF
    (by
      intro i hi U Y T hT
      simpa [hi] using hCentres i U Y T hT)
    (by
      intro i hi U Y T hT
      simpa [hi] using hCentres i U Y T hT) hP
  refine ⟨hFoot.1,hFoot.2,?_⟩
  exact indexed_boundary_dense_off_varying_active_components C r D hC hLF hD hr hpure
end
end Hironaka.HironakaG3VaryingContactActiveFootprint
