import Hironaka.Resolution.HironakaG3DisjointBornChartGeometry
import Hironaka.Resolution.HironakaG3DisjointAtlasFootprint
import Hironaka.Resolution.HironakaG3GlobalMemberSafeTrace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointBornCoverage
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointAtlasFootprint HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaG3GenericBornChartOverlap HironakaG3DisjointBornChartGeometry
  HironakaG3BornChartFootprint HironakaG3GlobalMemberSafeTrace HironakaG3EmptyAwareHistory
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower

/-- Every literal born slot of an actual disjoint chart lies over the union
of its component supports. -/
theorem disjoint_born_chart_over_union {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    {H : Set Z} (hH : H ∈ bornChartBoundary c) : H ⊆ P ⁻¹' (⋃ i, A i) := by
  have hOver := disjoint_class_centres_over_union A W K hCentres c.U c.Y c.T c.mem.1
  obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
  exact born_chart_image_subset_of_centresOver c (⋃ i, A i) hOver hH'

/-- Each point of an actual born chart slot is covered by a canonical global
member of one of the actual component-window exhaustions. -/
theorem disjoint_born_chart_slot_covered {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (A : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X) (hAW : ∀ i, A i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
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
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n)
      (⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩ : Opens Z)))
    (hExW : ∀ i k, (Ex i).W k = nestedOpens
      (⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩ : Opens Z) (c i k).V)
    (hExB : ∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map
      ((Subtype.val : (⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩ : Opens Z) → Z) ⁻¹' ·))
    (c₀ : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (H : Set Z) (hH : H ∈ bornChartBoundary c₀) (z : Z) (hz : z ∈ H) :
    ∃ (i : ι) (b : {B : Set (⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩ : Opens Z) // (Ex i).IsGlobalMember B}),
      z ∈ (Subtype.val : (⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩ : Opens Z) → Z) '' b.val := by
  have hzA := disjoint_born_chart_over_union A D W K hCentres c₀ hH hz
  obtain ⟨i,hzi⟩ := mem_iUnion.mp hzA
  let Q : Opens Z := ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩
  have hzQ : z ∈ Q := hAW i hzi
  obtain ⟨k,hzk⟩ := (Ex i).cover ⟨z,hzQ⟩
  rw [hExW i k] at hzk
  have hzV : z ∈ (c i k).V := hzk
  have hzV₀ : z ∈ c₀.V := disjoint_born_chart_subset A D hD W K hGeo c₀ hH hz
  let O : Set Z := P ⁻¹' ((c₀.U ⊓ (c i k).U : Opens X) : Set X)
  have hzO : z ∈ O := by
    change P z ∈ c₀.U ∧ P z ∈ (c i k).U
    constructor
    · change z ∈ P ⁻¹' (c₀.U : Set X)
      rwa [← c₀.V_eq]
    · change z ∈ P ⁻¹' ((c i k).U : Set X)
      rwa [← (c i k).V_eq]
  have hOverlap := disjoint_born_chart_overlap A W K D hWindow hSame hCentres c₀ (c i k)
  have hmem : H ∩ O ∈ ((bornChartBoundary c₀).map (· ∩ O)).filter
      (fun H => decide H.Nonempty) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨H,hH,rfl⟩,by simpa using (show (H ∩ O).Nonempty from ⟨z,hz,hzO⟩)⟩
  rw [hOverlap] at hmem
  obtain ⟨H',hH',hEq⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
  have hzH' : z ∈ H' := by
    have : z ∈ H' ∩ O := hEq ▸ ⟨hz,hzO⟩
    exact this.1
  obtain ⟨b,hb,_⟩ := nonempty_safe_slot_exists_unique_global_member Q (c i k).V (Ex i) k
    (bornChartBoundary (c i k)) (hExW i k) (hExB i k)
    (fun H hH => disjoint_born_chart_subset A D hD W K hGeo (c i k) hH) H' hH' ⟨z,hzH',hzQ⟩
  refine ⟨i,b,?_⟩
  have hzTrace : z ∈ ((Subtype.val : Q → Z) '' b.val) ∩ (Q ⊓ (c i k).V : Opens Z) := by
    rw [hb]
    exact ⟨hzH',hzQ⟩
  exact hzTrace.1
end
end Hironaka.HironakaG3DisjointBornCoverage
