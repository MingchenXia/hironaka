import Hironaka.Resolution.HironakaG3DisjointComponentChartChain
import Hironaka.Resolution.HironakaG3DisjointBornChartGeometry
import Hironaka.Resolution.HironakaG3SupportedPartialSNCChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointComponentBornLocalFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry HironakaG3DisjointComponentChartChain
  HironakaG3DisjointBornChartGeometry HironakaG3GenericBornChartOverlap HironakaG3SupportedPartialSNCChain
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower

/-- For an actual finite-visible disjoint atlas, one component's actual born
lists yield a locally finite SNC family over its isolated window, supported
on that component's supplied centre footprint. -/
theorem exists_disjoint_component_born_local_family {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (A F : ι → Set X) (D : κ → Set X)
    (hD : IsLocallyFiniteSNCDivisor n D) (W : ι → Opens X) (K : ι → LocalTowerClass X)
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
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (i : ι)
    (hCompact : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K i U Y T) :
    let Q : Opens Z := ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩
    ∃ (c : ℕ → TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
      (Ex : SNCExhaustion (CMfd.of (n := n) Q)),
      (∀ k, K i (c k).U (c k).Y (c k).T) ∧
      (∀ k, (c k).U ≤ W i) ∧
      (∀ k, Ex.W k = nestedOpens Q (c k).V) ∧
      (∀ k, Ex.B k = (bornChartBoundary (c k)).map ((Subtype.val : Q → Z) ⁻¹' ·)) ∧
      ∃ (ρ : Type) (B : ρ → Set Q), IsLocallyFiniteSNCDivisor n (Q := CMfd.of (n := n) Q) B ∧
        (∀ j, (B j).Nonempty ∧ B j ⊆ (Subtype.val : Q → Z) ⁻¹' (P ⁻¹' F i)) ∧
        (⋃ j, B j) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
  let Q : Opens Z := ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩
  obtain ⟨c,hmem,hUW,hMono,hCover⟩ :=
    disjoint_component_chart_chain A W K D hWindow hCompare hCentres hD.1 hG i hCompact
  have hVQ (k : ℕ) : (c k).V ≤ Q := by
    intro z hz
    have hzU : P z ∈ (c k).U := by
      have hh : z ∈ ((c k).V : Set Z) := hz
      rwa [(c k).V_eq] at hh
    exact hUW k hzU
  have hUmono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U := fun {j k} hjk x hx => by
    obtain ⟨z,rfl⟩ := hG.2.2.1 x
    have hzj : z ∈ (c j).V := (c j).mem_V hx
    have hzk := hMono j k hjk hzj
    rw [(c k).V_eq] at hzk
    exact hzk
  have hNested : ∀ {j k : ℕ}, j ≤ k →
      ((bornChartBoundary (c k)).map (· ∩ ((c j).V : Set Z))).filter
        (fun H => decide H.Nonempty) = (bornChartBoundary (c j)).filter
          (fun H => decide H.Nonempty) := fun {j k} hjk => by
    have hov := disjoint_born_chart_overlap A W K D hWindow hSame hCentres (c j) (c k)
    have hpre : P ⁻¹' (((c j).U ⊓ (c k).U : Opens X) : Set X) = ((c j).V : Set Z) := by
      rw [(c j).V_eq]
      ext y
      exact ⟨fun h => h.1,fun h => ⟨h,hUmono hjk h⟩⟩
    rw [hpre] at hov
    have hself : (bornChartBoundary (c j)).map (· ∩ ((c j).V : Set Z)) = bornChartBoundary (c j) := by
      conv_rhs => rw [← List.map_id (bornChartBoundary (c j))]
      exact List.map_congr_left fun H hH => inter_eq_left.mpr (disjoint_born_chart_subset A D hD W K hGeo (c j) hH)
    rw [hself] at hov
    exact hov.symm
  obtain ⟨Ex,hExW,hExB,ρ,B,hSNC,hSupport,hUnion⟩ :=
    supported_partial_snc_chain Q (fun k => (c k).V) (fun k => bornChartBoundary (c k)) (P ⁻¹' F i)
      hVQ (fun {j k} => hMono j k) hCover
      (by intro k H hH; exact disjoint_born_chart_subset A D hD W K hGeo (c k) hH)
      (fun k => disjoint_born_chart_snc A D hD W K hGeo (c k)) hNested
      (by intro k H hH; exact disjoint_born_chart_over_component A F D W K hBornCentres i (c k) (hmem k) hH)
  exact ⟨c,Ex,hmem,hUW,hExW,hExB,ρ,B,hSNC,hSupport,hUnion⟩
end
end Hironaka.HironakaG3DisjointComponentBornLocalFamily
