import Hironaka.Resolution.HironakaG8CompleteEmbeddedAtlas
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons
import Hironaka.Resolution.HironakaG3REmbeddedNC

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompleteEmbeddedAtlasBoundary

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers
  HironakaG8CompleteEmbeddedAtlas HironakaG3RTowerClass HironakaG3RChartOfMember
  HironakaG3GenericBornChartOverlap G3UniversePhysicalClassComparisons
  HironakaG3REmbeddedGlobalSNC HironakaG3REmbeddedNC HironakaEmbeddedAnalytic
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation

/-- A compatible exhaustion by actual complete charts determines its global born labels. -/
theorem complete_embedded_atlas_global_members {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    {K : LocalTowerClass X} {P : Z → X} (h : CompleteEmbeddedAtlas W K P) (Ex : SNCExhaustion Z)
    (hCharts : ∀ k, ∃ c : TowerChart K Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c) :
    let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
    IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
    (⋃ j, B j) = P ⁻¹' singularSet (n := n) W ∧
    HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  have hTrace (k : ℕ) : (⋃ H ∈ Ex.B k, H) = (Ex.W k : Set Z) ∩ exceptionalLocus n P := by
    obtain ⟨c,hV,hB⟩ := hCharts k
    rw [hV,hB]
    exact (h.chartGeometry c).2.2
  have hSupport : (⋃ k, ⋃ H ∈ Ex.B k, H) = P ⁻¹' singularSet (n := n) W := by
    rw [← h.exceptional_eq]
    ext z
    constructor
    · intro hz
      obtain ⟨k,hk⟩ := mem_iUnion.mp hz
      rw [hTrace k] at hk
      exact hk.2
    · intro hz
      obtain ⟨k,hk⟩ := Ex.cover z
      refine mem_iUnion.mpr ⟨k,?_⟩
      rw [hTrace k]
      exact ⟨hk,hz⟩
  refine ⟨⟨Ex.locallyFinite_globalMember,fun i => Ex.isClosed_globalMember i.2,Ex.coordinates_globalMember⟩,
    fun i => i.2.1,Ex.iUnion_globalMember.trans hSupport,?_⟩
  apply SNCExhaustion'.hasNormalCrossingsWithBoundary Ex
  intro k
  obtain ⟨c,hV,hB⟩ := hCharts k
  rw [hV,hB]
  exact (h.chartGeometry c).2.1

/-- The born slots of complete charts give a compatible SNC exhaustion of the same map. -/
theorem complete_embedded_atlas_indexed_boundary {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    {K : LocalTowerClass X} {P : Z → X} (h : CompleteEmbeddedAtlas W K P)
    (hPhysical : HasPhysicalComparisons K)
    (hWindows : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T) :
    ∃ Ex : SNCExhaustion Z,
      (∀ k, ∃ c : TowerChart K Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c) ∧
      let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
      IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
      (⋃ j, B j) = P ⁻¹' singularSet (n := n) W ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let L := CompactExhaustion.choice X
  let U (k : ℕ) : Opens X := ⟨interior (L (k+1)),isOpen_interior⟩
  choose Y T hT using fun k : ℕ => hWindows (U k) (L (k+1)) (L.isCompact (k+1)) interior_subset
  let c (k : ℕ) := chartOfMember (physical_comparisons_to_comparisons hPhysical) (T k) (hT k)
    h.glued.2.2.2 h.glued.1.continuous
  have hUmono {j k : ℕ} (hjk : j ≤ k) : (c j).U ≤ (c k).U :=
    interior_mono (L.subset (Nat.succ_le_succ hjk))
  have hVmono {j k : ℕ} (hjk : j ≤ k) : ((c j).V : Set Z) ⊆ (c k).V := by
    intro z hz
    apply (c k).mem_V
    apply hUmono hjk
    rw [(c j).V_eq] at hz
    exact hz
  have hCover (z : Z) : ∃ k, z ∈ (c k).V := by
    obtain ⟨k,hk⟩ := L.exists_mem (P z)
    exact ⟨k,(c k).mem_V (L.subset_interior_succ k hk)⟩
  have hSub {k : ℕ} {H : Set Z} (hH : H ∈ bornChartBoundary (c k)) : H ⊆ (c k).V := by
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hH
    rintro _ ⟨y,_,rfl⟩
    exact ((c k).φ y).property
  have hNested {j k : ℕ} (hjk : j ≤ k) :
      ((bornChartBoundary (c k)).map (· ∩ ((c j).V : Set Z))).filter
        (fun H => decide H.Nonempty) = (bornChartBoundary (c j)).filter (fun H => decide H.Nonempty) := by
    obtain ⟨β,hβ⟩ := hPhysical (c j).U (c k).U (c j).Y (c k).Y (c j).T (c k).T (c j).mem (c k).mem
    have hov := born_chart_overlap_of_physical (c j) (c k) β hβ
    have hPre : P ⁻¹' ((((c j).U ⊓ (c k).U : Opens X) : Set X)) = ((c j).V : Set Z) := by
      rw [inf_eq_left.mpr (hUmono hjk),(c j).V_eq]
    have hSelf : (bornChartBoundary (c j)).map (· ∩ ((c j).V : Set Z)) = bornChartBoundary (c j) := by
      conv_rhs => rw [← List.map_id (bornChartBoundary (c j))]
      exact List.map_congr_left fun _ hH => inter_eq_left.mpr (hSub hH)
    rw [hPre,hSelf] at hov
    exact hov.symm
  let Ex : SNCExhaustion Z :=
    { W := fun k => (c k).V
      B := fun k => bornChartBoundary (c k)
      mono := hVmono
      cover := hCover
      sub := hSub
      snc := fun k => (h.chartGeometry (c k)).1
      nested := hNested }
  have hC (k : ℕ) : ∃ c : TowerChart K Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c :=
    ⟨c k,rfl,rfl⟩
  exact ⟨Ex,hC,complete_embedded_atlas_global_members h Ex hC⟩

end
end Hironaka.HironakaG8CompleteEmbeddedAtlasBoundary
