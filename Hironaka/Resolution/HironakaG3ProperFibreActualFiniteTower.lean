import Hironaka.Resolution.HironakaG3ProperFibrePhysicalFiniteTower
import Hironaka.Resolution.HironakaG3ProperFibreComponentWindows
import Hironaka.Resolution.HironakaG3ComponentChartClosedExtension
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3ProperFibreActualFiniteTower
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  RestrictEmptyTower MarkedIdealTowerTransport HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3ProperFibreComponentWindows HironakaG3ComponentChartClosedExtension
  HironakaG3FiniteDisjointTowerMerge MaxLocusLocal

theorem proper_fibre_actual_finite_tower_with_provenance_over_compact {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
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
          (∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage M (nestedOpens A (W i.val)))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
            ∀ z, (((c i).T.proj (φ z) : (c i).U) : Z) = ((M.proj z.val : A) : Z)) := by
  classical
  obtain ⟨s,hLabels,c,hc,hMem,B,M,hM,hCmp⟩ :=
    HironakaG3ProperFibrePhysicalFiniteTower.proper_fibre_physical_finite_tower_over_compact
      C hClosed hLF W hCW hWindow K hCompare hCentres hCompact D hD hπ hσ U L hL hUL
  refine ⟨s,hLabels,c,hc,hMem,B,M,hM,hCmp,?_⟩
  intro i
  obtain ⟨φ,hφ⟩ := hCmp i
  let A : Opens Z := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.continuous⟩
  have hVeq : nestedOpens A (c i).U = nestedOpens A (W i.val) := by
    rw [hc i]
    apply Opens.ext
    ext z
    change (z.val ∈ W i.val ∧ z.val ∈ A) ↔ z.val ∈ W i.val
    exact and_iff_left z.property
  let δ := opensCongr (n := n) (congrArg (openPreimage M) hVeq.symm)
  refine ⟨δ.trans φ,?_⟩
  intro z
  have hp := HironakaG3EmptyAwareHistory.emptyAware_proj_comm hφ (δ z)
  have hh := congrArg Subtype.val hp
  change (((c i).T.proj (φ (δ z)) : (c i).U) : Z) =
    ((((restrict (nestedOpens A (c i).U) M).proj (δ z) : nestedOpens A (c i).U) : A) : Z) at hh
  have hproj := congrArg Subtype.val (proj_restrict (nestedOpens A (c i).U) M (δ z))
  exact hh.trans hproj

theorem proper_fibre_actual_finite_tower {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
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
    ∃ (U : Opens X) (L : Set X) (s : Finset ι), x ∈ U ∧ IsCompact L ∧ (U : Set X) ⊆ L ∧
      (∀ i, (C i ∩ π ⁻¹' (U : Set X)).Nonempty → i ∈ s) ∧
      let A : Opens Z := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.continuous⟩
      ∃ (c : {j // j ∈ s} → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y σ),
        (∀ i, (c i).U = W i.val ⊓ A) ∧
        ∃ (B : CMfd.{0} n) (M : BlowupTower (CMfd.of (n := n) A) B),
          CentresOver (finiteSupport (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) M ∧
          ∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage M (nestedOpens A (W i.val)))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
            ∀ z, (((c i).T.proj (φ z) : (c i).U) : Z) = ((M.proj z.val : A) : Z) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨interior L,isOpen_interior⟩
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxL
  have hUL : (U : Set X) ⊆ L := interior_subset
  obtain ⟨s,hLabels,c,hc,_hMem,B,M,hM,_hPhysical,hCharts⟩ :=
    proper_fibre_actual_finite_tower_with_provenance_over_compact C hClosed hLF W hCW hWindow K hCompare
      hCentres hCompact D hD hπ hσ U L hL hUL
  exact ⟨U,L,s,hxU,hL,hUL,hLabels,c,hc,B,M,hM,hCharts⟩

end
end Hironaka.HironakaG3ProperFibreActualFiniteTower
