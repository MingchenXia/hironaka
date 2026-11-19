import Hironaka.Resolution.HironakaG3VaryingContactComponentClass
import Hironaka.Resolution.HironakaG3DisjointLocalResolvedGeometry
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingContactResolvedAtlas
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointLocalResolvedGeometry HironakaG3IndexedSeparatedComponents
  HironakaG3VaryingContactComponentClass HironakaG3PhysicalClassComparisons HironakaG3DisjointAtlasCommonGood
  HironakaG3SeparatedAvoidingGood HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3BoundaryDivisorBoundClass RestrictEmptyTower

theorem exists_varying_contact_resolved_atlas_with_provenance {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hLF : LocallyFinite C) (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∃ (W : ι → Opens X) (K : ι → LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X),
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
      IsGluedFrom (disjointWindowClass C W K) Z P ∧
      IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ ∧
      ∀ i, P '' strictTransform n P (C i) = C i ∧
        IsClosedSubmanifold n (strictTransform n P (C i)) ∧
        ∀ z ∈ strictTransform n P (C i), RegularAtDim (n := n) (strictTransform n P (C i)) z (r i) := by
  have hEach : ∀ i, ∃ K : LocalTowerClass X, ActualComponentResolutionClass (r i) (C i) D (hC i) hD K ∧
      HasPhysicalComparisons K ∧ HasComparisons K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
          (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
            r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T) ∧
      HasBoundaryDivisorBound D K ∧
      HasSortedLocalWindowGeometry (C i) D K ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T →
        T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i) = (Subtype.val : U → X) ⁻¹' C i ∧
        ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i),
          RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C i)) y (r i)) ∧
      (∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        K U Y T → IsIsomorphismOver n T.proj
          ((Subtype.val : U → X) ⁻¹' (C i \ regularLocus (n := n) (C i) (r i) ∪ C i ∩ ⋃ j, D j)ᶜ)) ∧
      (∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T) := by
    intro i
    exact exists_actual_component_resolution_class_with_provenance (C i) D (hC i) hD rfl (hr i) (hpure i)
  choose K hKind hPhys hCmp hCentres hActiveCentres hBound hSorted hLocal hGood hCompact using hEach
  have hW : ∀ i, ∃ U : Opens X, C i ⊆ U ∧ ∀ j, j ≠ i → Disjoint (C j) (U : Set X) :=
    fun i => exists_component_isolating_open C (fun j => (hC j).analytic.isClosed) hLF hDis i
  choose W hCW hWin using hW
  have hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X) := fun i j hij => hWin i j (Ne.symm hij)
  have hMember : ∀ i x, x ∈ C i → ∃ (U : Opens X) (L : Set X), x ∈ U ∧ U ≤ W i ∧
      IsCompact L ∧ (U : Set X) ⊆ L ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T := by
    let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro i x hx
    obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
    let U : Opens X := ⟨interior L ∩ (W i : Set X),isOpen_interior.inter (W i).isOpen⟩
    have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hxL,hCW i hx⟩
    have hUL : (U : Set X) ⊆ L := fun _ h => interior_subset h.1
    obtain ⟨Y,T,hT⟩ := hCompact i U L hL hUL
    exact ⟨U,L,hxU,fun _ h => h.2,hL,hUL,Y,T,hT⟩
  obtain ⟨Z,P,hGv⟩ := exists_finite_visible_disjoint_atlas C W K
    (fun i => (hC i).analytic.isClosed) hLF hWindow hCmp hCentres D hD.1 hMember
  have hG : IsGluedFrom (disjointWindowClass C W K) Z P :=
    finite_visible_forget_glued _ D hGv
  have hGlobalGood : IsIsomorphismOver n P
      (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ := by
    apply disjoint_atlas_isomorphism_over_common_good C W K _ ?_ hG
    intro i U Y T hT
    apply iso_mono _ (hGood i U Y T hT)
    intro u hu
    change (u : X) ∉ (C i \ regularLocus (n := n) (C i) (r i) ∪ C i ∩ ⋃ j, D j)
    intro hbad
    exact hu (mem_iUnion.mpr ⟨i,hbad⟩)
  exact ⟨W,K,Z,P,hCW,hWindow,hKind,hPhys,hCentres,hActiveCentres,hBound,hSorted,hCompact,hGv,hG,hGlobalGood,
    disjoint_atlas_component_resolved_geometry C r W K (fun i => (hC i).analytic.isClosed) hWindow hLocal hG⟩

theorem exists_varying_contact_resolved_atlas {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hLF : LocallyFinite C) (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i))) :
    ∃ (W : ι → Opens X) (K : ι → LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X),
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
      IsGluedFrom (disjointWindowClass C W K) Z P ∧
      IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ ∧
      ∀ i, P '' strictTransform n P (C i) = C i ∧
        IsClosedSubmanifold n (strictTransform n P (C i)) ∧
        ∀ z ∈ strictTransform n P (C i), RegularAtDim (n := n) (strictTransform n P (C i)) z (r i) := by
  obtain ⟨W,K,Z,P,hCW,hWindow,_hKind,hRest⟩ :=
    exists_varying_contact_resolved_atlas_with_provenance C r D hC hLF hDis hD hr hpure
  exact ⟨W,K,Z,P,hCW,hWindow,hRest⟩

end
end Hironaka.HironakaG3VaryingContactResolvedAtlas
