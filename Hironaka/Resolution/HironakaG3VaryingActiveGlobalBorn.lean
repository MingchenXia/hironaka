import Hironaka.Resolution.HironakaG3DisjointCanonicalGlobalBorn
import Hironaka.Resolution.HironakaG3ActiveSupportedFamily
import Hironaka.Resolution.HironakaG3VaryingCombinedComponentSlots
import Hironaka.Resolution.HironakaG3PhysicalClassComparisons
import Hironaka.Resolution.HironakaG3VaryingContactActiveFootprint
import Hironaka.Resolution.HironakaG3VaryingActiveInheritedLabels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingActiveGlobalBorn
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3GenericBornChartOverlap HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  MaxLocusLocal RestrictEmptyTower HironakaG3ActiveSupportedFamily HironakaG3DisjointCanonicalGlobalBorn
  HironakaG3PhysicalClassComparisons HironakaG3VaryingContactActiveFootprint
  HironakaG3VaryingActiveInheritedLabels HironakaG3VaryingCombinedComponentSlots

/-- Actual varying-atlas born members, on the same component windows. -/
theorem exists_varying_active_global_born {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hPhys : ∀ i, HasPhysicalComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    (hBornCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' (if varyingActive C r D hC hD i then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    (hCompact : ∀ (i : ι) (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T)
    {P : Z → X} (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P) :
    let Q : ι → Opens Z := varyingComponentWindow C D W K hG
    ∃ (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
      (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (Q i))),
      (∀ i k, K i (c i k).U (c i k).Y (c i k).T) ∧
      (∀ i k, (c i k).U ≤ W i) ∧
      (∀ i k, (Ex i).W k = nestedOpens (Q i) (c i k).V) ∧
      (∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map ((Subtype.val : Q i → Z) ⁻¹' ·)) ∧
      let B : (Σ i, {H : Set (Q i) // (Ex i).IsGlobalMember H}) → Set Z :=
        fun p => (Subtype.val : Q p.1 → Z) '' p.2.1
      LocallyFinite B ∧ ∀ p, IsClosed (B p) ∧ (B p).Nonempty ∧ B p ⊆ P ⁻¹' C p.1 ∧ B p ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD) := by
  let active : ι → Prop := varyingActive C r D hC hD
  obtain ⟨hF,hFLF,hFW,_hUnion⟩ := active_supported_family C (fun i => (W i : Set X)) active
    (fun i => (hC i).analytic.isClosed) hLF hCW
  obtain ⟨c,Ex,hMem,hUW,hExW,hExB,hBLF,hB⟩ :=
    exists_disjoint_canonical_global_born C (fun i => if active i then C i else ∅)
      D hD W K hF hFLF hFW hWindow
      (fun i => physical_comparisons_to_comparisons (hPhys i))
      (fun i => hPhys i) hCentres hBornCentres hGeo hCompact hG
  refine ⟨c,Ex,hMem,hUW,hExW,hExB,hBLF,?_⟩
  intro p
  obtain ⟨hclosed,hne,hsupp⟩ := hB p
  refine ⟨hclosed,hne,?_,?_⟩
  · intro z hz
    have hz' := hsupp hz
    by_cases ha : active p.1
    · simpa [ha] using hz'
    · simp [ha] at hz'
  · intro z hz
    have hz' := hsupp hz
    by_cases ha : active p.1
    · change P z ∈ ⋃ i : {i // active i}, C i.val
      apply mem_iUnion.mpr
      exact ⟨⟨p.1,ha⟩, by simpa [ha] using hz'⟩
    · simp [ha] at hz'
end
end Hironaka.HironakaG3VaryingActiveGlobalBorn
