import Hironaka.Resolution.HironakaG3DisjointComponentBornLocalFamily
import Hironaka.Resolution.HironakaG3SupportedExhaustionGlobalMembers
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointCanonicalGlobalBorn
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry HironakaG3GenericBornChartOverlap
  HironakaG3DisjointComponentBornLocalFamily HironakaG3SupportedExhaustionGlobalMembers
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower

/-- Actual component-window born exhaustions globalize as canonical closed,
locally finite members over the specified closed locally finite footprints. -/
theorem exists_disjoint_canonical_global_born {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (A F : ι → Set X) (D : κ → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hF : ∀ i, IsClosed (F i)) (hFLF : LocallyFinite F) (hFW : ∀ i, F i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hCompare : ∀ i, HasComparisons (K i))
    (hSame : ∀ (i : ι) (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} n)
      (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂),
      K i U₁ Y₁ T₁ → K i U₂ Y₂ T₂ →
      ∃ β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
        EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
          (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (hBornCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F i) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i))
    (hCompact : ∀ (i : ι) (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T)
    {P : Z → X} (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P) :
    let Q : ι → Opens Z := fun i => ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩
    ∃ (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
      (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (Q i))),
      (∀ i k, K i (c i k).U (c i k).Y (c i k).T) ∧
      (∀ i k, (c i k).U ≤ W i) ∧
      (∀ i k, (Ex i).W k = nestedOpens (Q i) (c i k).V) ∧
      (∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map ((Subtype.val : Q i → Z) ⁻¹' ·)) ∧
      let B : (Σ i, {H : Set (Q i) // (Ex i).IsGlobalMember H}) → Set Z :=
        fun p => (Subtype.val : Q p.1 → Z) '' p.2.1
      LocallyFinite B ∧ ∀ p, IsClosed (B p) ∧ (B p).Nonempty ∧ B p ⊆ P ⁻¹' F p.1 := by
  let Q : ι → Opens Z := fun i => ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩
  have hEach : ∀ i, ∃ (c : ℕ → TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
      (Ex : SNCExhaustion (CMfd.of (n := n) (Q i))) (ρ : Type) (B : ρ → Set (Q i)),
      (∀ k, K i (c k).U (c k).Y (c k).T) ∧
      (∀ k, (c k).U ≤ W i) ∧
      (∀ k, Ex.W k = nestedOpens (Q i) (c k).V) ∧
      (∀ k, Ex.B k = (bornChartBoundary (c k)).map ((Subtype.val : Q i → Z) ⁻¹' ·)) ∧
      (∀ j, (B j).Nonempty ∧ B j ⊆ (Subtype.val : Q i → Z) ⁻¹' (P ⁻¹' F i)) ∧
      (⋃ j, B j) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
    intro i
    obtain ⟨c,Ex,hmem,hUW,hW,hB,ρ,B,_hSNC,hSupp,hUnion⟩ :=
      exists_disjoint_component_born_local_family A F D hD W K hWindow hCompare hSame hCentres hBornCentres hGeo hG i (hCompact i)
    exact ⟨c,Ex,ρ,B,hmem,hUW,hW,hB,hSupp,hUnion⟩
  choose c Ex ρ B hMem hUW hExW hExB hSupp hUnion using hEach
  let FZ : ι → Set Z := fun i => P ⁻¹' F i
  have hFZ : ∀ i, IsClosed (FZ i) := fun i => (hF i).preimage hG.1.continuous
  have hFZLF : LocallyFinite FZ := hFLF.preimage_continuous hG.1.continuous
  have hFZQ : ∀ i, FZ i ⊆ Q i := fun i _ h => hFW i h
  have hSlots : ∀ i k H, H ∈ (Ex i).B k → H ⊆ (Subtype.val : Q i → Z) ⁻¹' FZ i := by
    intro i k H hH x hx
    have hxU : x ∈ ⋃ k, ⋃ H ∈ (Ex i).B k, H := mem_iUnion.mpr ⟨k,mem_iUnion₂.mpr ⟨H,hH,hx⟩⟩
    rw [← hUnion i] at hxU
    obtain ⟨j,hxB⟩ := mem_iUnion.mp hxU
    exact (hSupp i j).2 hxB
  have hGlobal := supported_exhaustion_global_members Q FZ hFZ hFZLF hFZQ Ex hSlots
  exact ⟨c,Ex,hMem,hUW,hExW,hExB,hGlobal⟩
end
end Hironaka.HironakaG3DisjointCanonicalGlobalBorn
