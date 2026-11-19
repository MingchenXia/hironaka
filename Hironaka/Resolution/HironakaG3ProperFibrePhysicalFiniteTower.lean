import Hironaka.Resolution.HironakaG3ProperFibreComponentWindows
import Hironaka.Resolution.HironakaG3ComponentChartClosedExtension
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3ProperFibrePhysicalFiniteTower
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  RestrictEmptyTower MarkedIdealTowerTransport HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3ProperFibreComponentWindows HironakaG3ComponentChartClosedExtension
  HironakaG3FiniteDisjointTowerMerge HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition MaxLocusLocal

theorem proper_fibre_physical_finite_tower_over_compact {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
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
          ∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage M (nestedOpens A (c i).U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
            EmptyAwareTowerIso (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right))
              (restrict (nestedOpens A (c i).U) M) (c i).T φ := by
  classical
  obtain ⟨s,hLabels,hCharts⟩ := proper_fibre_component_windows_over_compact C hLF W hCW hWindow K hCompare hCentres hCompact D hD hπ hσ U L hL hUL
  refine ⟨s,hLabels,?_⟩
  let A : Opens Z := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.continuous⟩
  let I := {j // j ∈ s}
  choose c hc hMem hFoot using fun i : I => hCharts i.val i.property
  refine ⟨c,hc,hMem,?_⟩
  have hExt : ∀ i : I, ∃ (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) A) B),
      CentresOver ((Subtype.val : A → Z) ⁻¹' C i.val) T ∧
      ∃ e : (transport (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right)) (c i).T).target
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage T (nestedOpens A (c i).U),
        IsTowerIso (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right))
          (restrict (nestedOpens A (c i).U) T) (c i).T
          (e.symm.trans (transport (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right)) (c i).T).back) := by
    intro i
    exact component_chart_closed_extension (C i.val) (hClosed i.val) A (W i.val) (hCW i.val)
      _ (c i) (hc i) (hCentres i.val (c i).U (c i).Y (c i).T (hMem i))
  choose B T hOver hPhysical using hExt
  let F : I → Set A := fun i => (Subtype.val : A → Z) ⁻¹' C i.val
  let W' : I → Opens A := fun i => nestedOpens A (c i).U
  have hF : ∀ i, IsClosed (F i) := fun i => (hClosed i.val).preimage continuous_subtype_val
  have hFW : ∀ i, F i ⊆ W' i := by
    intro i z hz
    change z.val ∈ (c i).U
    rw [hc i]
    exact ⟨hCW i.val hz, z.property⟩
  have hW : ∀ i j, i ≠ j → Disjoint (W' i : Set A) (F j) := by
    intro i j hij
    have hv : i.val ≠ j.val := by intro h; apply hij; exact Subtype.ext h
    apply Set.disjoint_left.mpr
    intro z hz hzF
    change z.val ∈ (c i).U at hz
    rw [hc i] at hz
    exact Set.disjoint_left.mp ((hWindow i.val j.val hv).symm) hz.1 hzF
  obtain ⟨B',M,hM,hCmp⟩ := finite_disjoint_towers_physical_comparisons F hF W' hFW hW B T hOver s.attach
  refine ⟨B',M,hM,?_⟩
  intro i
  obtain ⟨e,he⟩ := hPhysical i
  obtain ⟨φ,hφ⟩ := hCmp i (Finset.mem_attach s i)
  let β := nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right)
  let ξ := e.symm.trans (transport β (c i).T).back
  refine ⟨φ.trans ξ,?_⟩
  simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans hφ (emptyAware_of_isTowerIso he)

theorem proper_fibre_physical_finite_tower {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
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
        ∃ (hc : ∀ i, (c i).U = W i.val ⊓ A),
        (∀ i, K i.val (c i).U (c i).Y (c i).T) ∧
        ∃ (B : CMfd.{0} n) (M : BlowupTower (CMfd.of (n := n) A) B),
          CentresOver (finiteSupport (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach) M ∧
          ∀ i, ∃ φ : (CMfd.of (n := n) (openPreimage M (nestedOpens A (c i).U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).Y,
            EmptyAwareTowerIso (nestedOpensDiffeo (n := n) (show (c i).U ≤ A by rw [hc i]; exact inf_le_right))
              (restrict (nestedOpens A (c i).U) M) (c i).T φ := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨interior L,isOpen_interior⟩
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxL
  have hUL : (U : Set X) ⊆ L := interior_subset
  obtain ⟨s,hLabels,hCharts⟩ :=
    proper_fibre_physical_finite_tower_over_compact C hClosed hLF W hCW hWindow K hCompare hCentres hCompact
      D hD hπ hσ U L hL hUL
  exact ⟨U,L,s,hxU,hL,hUL,hLabels,hCharts⟩

end
end Hironaka.HironakaG3ProperFibrePhysicalFiniteTower
