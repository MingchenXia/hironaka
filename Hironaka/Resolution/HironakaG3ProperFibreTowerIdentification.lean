import Hironaka.Resolution.HironakaG3ProperFibreActualFiniteTower
import Hironaka.Resolution.HironakaG3ProperFibreComplementChart
import Hironaka.Resolution.HironakaG3FibreChartLocalCover
import Hironaka.Resolution.HironakaG3TowerRestrictedQIdentification
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3ProperFibreTowerIdentification
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3RTowerClass HironakaG3FiniteDisjointTowerMerge
  HironakaG3ProperFibreActualFiniteTower HironakaG3ProperFibreComplementChart
  HironakaG3FibreChartLocalCover HironakaG3RigidOverLocalGlue
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  MaxLocusLocal RestrictEmptyTower HironakaG3FiniteVisibleAtlas HironakaG3DisjointLocalTowerAtlas

theorem proper_fibre_tower_identification_with_provenance_over_compact {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
    (C : ι → Set Z) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (W : ι → Opens Z) (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      K i U B T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B), K i U B T)
    (D : κ → Set Z) (hD : LocallyFinite D) {π : Z → X} (hπ : IsProperMap π)
    {σ : Y → Z} (hσ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y σ)
    (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    ∃ s : Finset ι,
      (∀ i, (C i ∩ π ⁻¹' (U : Set X)).Nonempty → i ∈ s) ∧
      let A : Opens Z := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.continuous⟩
      ∃ (c : {j // j ∈ s} → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y σ),
        ∃ (hc : ∀ i, (c i).U = W i.val ⊓ A),
        (∀ i, K i.val (c i).U (c i).Y (c i).T) ∧
        ∃ (B : CMfd.{0} n) (M : BlowupTower (CMfd.of (n := n) A) B),
          CentresOver (finiteSupport (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) M ∧
          (∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage M (nestedOpens A (c i).U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
            EmptyAwareTowerIso (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right))
              (restrict (nestedOpens A (c i).U) M) (c i).T φ) ∧
          ∃! Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (window σ hσ.1.continuous A),
            ∀ z, (restrictedBaseMap σ hσ.1.continuous A) (Φ z) = M.proj z := by
  classical
  obtain ⟨s,hLabels,c,hc,hMem,B,M,hM,hCmp,hCharts⟩ :=
    proper_fibre_actual_finite_tower_with_provenance_over_compact C hClosed hLF W hCW hWindow K hCompare hCentres hCompact D hD hπ hσ U L hL hUL
  let A : Opens Z := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.continuous⟩
  obtain ⟨c₀,hc₀,hEmpty,hSupport⟩ :=
    proper_fibre_complement_chart C hClosed hLF W K hWindow hCompare hCentres D hD hπ hσ U L hL hUL s hLabels
  have hc₀' : (c₀.U : Set Z) = (A : Set Z) ∩ (⋃ i, C i)ᶜ := congrArg (fun V : Opens Z => (V : Set Z)) hc₀
  obtain ⟨V,hCover,φ,hφ⟩ := fibre_chart_local_cover C W hCW A s hσ.1.continuous _ c hc c₀ hc₀' hEmpty M hM hSupport hCharts
  refine ⟨s,hLabels,c,hc,hMem,B,M,hM,hCmp,?_⟩
  exact identify_tower_with_restricted_map A M σ hσ.1.continuous hσ.2.2.2 V hCover φ hφ

theorem proper_fibre_tower_identification {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
    (C : ι → Set Z) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (W : ι → Opens Z) (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      K i U B T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B), K i U B T)
    (D : κ → Set Z) (hD : LocallyFinite D) {π : Z → X} (hπ : IsProperMap π)
    {σ : Y → Z} (hσ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y σ) (x : X) :
    ∃ (U : Opens X), x ∈ U ∧
      let A : Opens Z := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.continuous⟩
      ∃ (B : CMfd.{0} n) (M : BlowupTower (CMfd.of (n := n) A) B),
        ∃! Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (window σ hσ.1.continuous A),
          ∀ z, (restrictedBaseMap σ hσ.1.continuous A) (Φ z) = M.proj z := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨interior L,isOpen_interior⟩
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxL
  have hUL : (U : Set X) ⊆ L := interior_subset
  obtain ⟨_s,_hLabels,_c,_hc,_hMem,B,M,_hM,_hPhysical,hΦ⟩ :=
    proper_fibre_tower_identification_with_provenance_over_compact C hClosed hLF W hCW hWindow K hCompare
      hCentres hCompact D hD hπ hσ U L hL hUL
  exact ⟨U,hxU,B,M,hΦ⟩

end
end Hironaka.HironakaG3ProperFibreTowerIdentification
