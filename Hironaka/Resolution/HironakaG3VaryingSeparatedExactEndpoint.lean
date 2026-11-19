import Hironaka.Resolution.HironakaG3VaryingContactResolvedAtlas
import Hironaka.Resolution.HironakaG3VaryingActiveGlobalBorn
import Hironaka.Resolution.HironakaG3VaryingCombinedIndexedSNC
import Hironaka.Resolution.HironakaG3VaryingCombinedExactSupport
import Hironaka.Resolution.HironakaG3DisjointSortedChartExactSupport
import Hironaka.Resolution.HironakaG3StrictComponentUnionBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingSeparatedExactEndpoint
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3VaryingContactComponentClass HironakaG3VaryingContactResolvedAtlas HironakaG3VaryingContactActiveFootprint
  HironakaG3VaryingActiveInheritedLabels HironakaG3VaryingActiveGlobalBorn
  HironakaG3VaryingCombinedComponentSlots HironakaG3VaryingCombinedIndexedSNC
  HironakaG3VaryingCombinedExactSupport HironakaG3DisjointSortedChartExactSupport
  HironakaG3StrictComponentUnionBoundary HironakaG3PhysicalClassComparisons
  HironakaG3BoundaryDivisorBoundClass RestrictEmptyTower

theorem exists_varying_separated_exact_with_branch_provenance {n : ℕ} {X : CMfd.{0} n}
    {ι : Type u} {κ : Type v} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∃ (W : ι → Opens X) (K : ι → LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X)
      (ρ : Type (max u v)) (B : ρ → Set Z),
      (∀ i, C i ⊆ W i) ∧ (∀ i j, i ≠ j → Disjoint (C j) (W i : Set X)) ∧
      (∀ i, ActualComponentResolutionClass (r i) (C i) D (hC i) hD (K i)) ∧
      (∀ i, HasPhysicalComparisons (K i)) ∧
      (∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T) ∧
      (∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
          (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
            r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T) ∧
      (∀ i, HasBoundaryDivisorBound D (K i)) ∧
      (∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) ∧
      (∀ (i : ι) (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) ∧
      IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P ∧
      IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ ∧
      (∀ i, P '' strictTransform n P (C i) = C i) ∧
      (∀ i, IsClosedSubmanifold n (strictTransform n P (C i))) ∧
      (∀ i z, z ∈ strictTransform n P (C i) → RegularAtDim (n := n) (strictTransform n P (C i)) z (r i)) ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      HasNormalCrossingsWithBoundary (⋃ i, strictTransform n P (C i)) B := by
  obtain ⟨W,K,Z,P,hCW,hWindow,hKind,hPhys,hCentres,hActive,hBound,hGeo,hCompact,hGv,hG,hGood,hResolved⟩ :=
    exists_varying_contact_resolved_atlas_with_provenance C r D hC hLF hDis hD hr hpure
  have hActive' : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T →
      RestrictEmptyTower.CentresOver ((Subtype.val : U → X) ⁻¹'
        (if varyingActive C r D hC hD i then C i else ∅)) T := by
    intro i U Y T hT
    by_cases ha : (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
        r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card
    · simpa only [varyingActive, if_pos ha] using hActive i U Y T hT
    · simpa only [varyingActive, if_neg ha] using hActive i U Y T hT
  have hExc : exceptionalLocus n P ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD) := by
    exact (varying_contact_active_footprint C r D hC hLF hD hr hpure W K hActive' hG).1
  obtain ⟨c,Ex,hMem,_hUW,hExW,hExB,hBLF,hB⟩ :=
    exists_varying_active_global_born C r D hC hLF hD W K hCW hWindow hPhys hCentres hActive' hGeo hCompact hGv
  have hSNC := varying_combined_indexed_snc C r D W K hC hLF hDis hD hr hpure hCW hWindow
    hCentres hActive hGeo hGv hExc c hMem Ex hExW hExB hBLF (fun p => (hB p).1)
      (fun p => (hB p).2.2.1) (fun p => (hB p).2.2.2)
  have hChartSupport := fun c => disjoint_sorted_chart_exact_support C D hD W K hBound hGeo hGv.1 c
  have hSupport := varying_combined_exact_support C r D W K hC hLF hD hr hpure hCW hWindow
    hPhys hCentres hActive hGeo hGv hChartSupport c Ex hExW hExB
  obtain ⟨ρ,B,hBSNC,hBNE,hUnion,hNC⟩ := strict_component_union_boundary C
    (fun i => (hC i).analytic.isClosed) hLF hDis hGv.1 (varyingCombinedBoundary C D W K hGv Ex) hSNC.1 hSNC.2
  exact ⟨W,K,Z,P,ρ,B,hCW,hWindow,hKind,hPhys,hCentres,hActive,hBound,hGeo,hCompact,hGv,hGood,(fun i => (hResolved i).1),
    (fun i => (hResolved i).2.1),(fun i z hz => (hResolved i).2.2 z hz),
    hBSNC,hBNE,hUnion.trans hSupport,hNC⟩

theorem exists_varying_separated_exact_with_certificates {n : ℕ} {X : CMfd.{0} n}
    {ι : Type u} {κ : Type v} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∃ (W : ι → Opens X) (K : ι → LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X)
      (ρ : Type (max u v)) (B : ρ → Set Z),
      (∀ i, C i ⊆ W i) ∧ (∀ i j, i ≠ j → Disjoint (C j) (W i : Set X)) ∧
      (∀ i, HasPhysicalComparisons (K i)) ∧
      (∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T) ∧
      (∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
          (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
            r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T) ∧
      (∀ i, HasBoundaryDivisorBound D (K i)) ∧
      (∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) ∧
      (∀ (i : ι) (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) ∧
      IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P ∧
      IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ ∧
      (∀ i, P '' strictTransform n P (C i) = C i) ∧
      (∀ i, IsClosedSubmanifold n (strictTransform n P (C i))) ∧
      (∀ i z, z ∈ strictTransform n P (C i) → RegularAtDim (n := n) (strictTransform n P (C i)) z (r i)) ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      HasNormalCrossingsWithBoundary (⋃ i, strictTransform n P (C i)) B := by
  obtain ⟨W,K,Z,P,ρ,B,hCW,hWindow,_hKind,hRest⟩ :=
    exists_varying_separated_exact_with_branch_provenance C r D hC hLF hDis hD hr hpure
  exact ⟨W,K,Z,P,ρ,B,hCW,hWindow,hRest⟩

theorem exists_varying_separated_exact_endpoint {n : ℕ} {X : CMfd.{0} n}
    {ι : Type u} {κ : Type v} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∃ (W : ι → Opens X) (K : ι → LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X)
      (ρ : Type (max u v)) (B : ρ → Set Z),
      IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P ∧
      IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ ∧
      (∀ i, P '' strictTransform n P (C i) = C i) ∧
      (∀ i, IsClosedSubmanifold n (strictTransform n P (C i))) ∧
      (∀ i z, z ∈ strictTransform n P (C i) → RegularAtDim (n := n) (strictTransform n P (C i)) z (r i)) ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      HasNormalCrossingsWithBoundary (⋃ i, strictTransform n P (C i)) B := by
  obtain ⟨W,K,Z,P,ρ,B,_hCW,_hWindow,_hPhys,_hCentres,_hActive,_hBound,_hGeo,_hCompact,hRest⟩ :=
    exists_varying_separated_exact_with_certificates C r D hC hLF hDis hD hr hpure
  exact ⟨W,K,Z,P,ρ,B,hRest⟩

end
end Hironaka.HironakaG3VaryingSeparatedExactEndpoint
