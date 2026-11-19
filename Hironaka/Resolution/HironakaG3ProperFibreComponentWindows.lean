import Hironaka.Resolution.HironakaG3DisjointVisibleMemberChart
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ProperFibreComponentWindows
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3DisjointVisibleMemberChart
  RestrictEmptyTower

theorem proper_fibre_component_windows_over_compact {n : ℕ} {X Z Y : CMfd.{0} n} {ι κ : Type*}
    (C : ι → Set Z) (hLF : LocallyFinite C) (W : ι → Opens Z)
    (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A),
      K i U A T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A), K i U A T)
    (D : κ → Set Z) (hD : LocallyFinite D) {P : Z → X} (hP : IsProperMap P)
    {Q : Y → Z} (hQ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y Q)
    (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    ∃ s : Finset ι,
      (∀ i, (C i ∩ P ⁻¹' (U : Set X)).Nonempty → i ∈ s) ∧
      ∀ i ∈ s, ∃ c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y Q,
        c.U = W i ⊓ ⟨P ⁻¹' (U : Set X), U.isOpen.preimage hP.continuous⟩ ∧
        K i c.U c.Y c.T ∧ C i ∩ P ⁻¹' (U : Set X) ⊆ (c.U : Set Z) := by
  have hLP : IsCompact (P ⁻¹' L) := hP.isCompact_preimage hL
  let s := (hLF.finite_nonempty_inter_compact hLP).toFinset
  refine ⟨s,?_,?_⟩
  · intro i ⟨z,hzC,hzU⟩
    apply (hLF.finite_nonempty_inter_compact hLP).mem_toFinset.mpr
    exact ⟨z,hzC,hUL hzU⟩
  · intro i _hi
    let V : Opens Z := W i ⊓ ⟨P ⁻¹' (U : Set X),U.isOpen.preimage hP.continuous⟩
    have hVL : (V : Set Z) ⊆ P ⁻¹' L := fun z hz => hUL hz.2
    obtain ⟨A,T,hT⟩ := hCompact i V (P ⁻¹' L) hLP hVL
    obtain ⟨c,hc,hMem⟩ := disjoint_visible_chart_of_member C W K D hWindow hCompare hCentres hD hQ
      i V inf_le_left (P ⁻¹' L) hLP hVL A T hT
    refine ⟨c,hc,hMem,?_⟩
    rw [hc]
    intro z hz
    exact ⟨hCW i hz.1,hz.2⟩

theorem proper_fibre_component_windows {n : ℕ} {X Z Y : CMfd.{0} n} {ι κ : Type*}
    (C : ι → Set Z) (hLF : LocallyFinite C) (W : ι → Opens Z)
    (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (K : ι → LocalTowerClass Z) (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A),
      K i U A T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (hCompact : ∀ (i : ι) (U : Opens Z) (L : Set Z), IsCompact L → (U : Set Z) ⊆ L →
      ∃ (A : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) A), K i U A T)
    (D : κ → Set Z) (hD : LocallyFinite D) {P : Z → X} (hP : IsProperMap P)
    {Q : Y → Z} (hQ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y Q) (x : X) :
    ∃ (U : Opens X) (L : Set X) (s : Finset ι), x ∈ U ∧ IsCompact L ∧ (U : Set X) ⊆ L ∧
      (∀ i, (C i ∩ P ⁻¹' (U : Set X)).Nonempty → i ∈ s) ∧
      ∀ i ∈ s, ∃ c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y Q,
        c.U = W i ⊓ ⟨P ⁻¹' (U : Set X), U.isOpen.preimage hP.continuous⟩ ∧
        K i c.U c.Y c.T ∧ C i ∩ P ⁻¹' (U : Set X) ⊆ (c.U : Set Z) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨L,hL,hxL⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨interior L,isOpen_interior⟩
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hxL
  have hUL : (U : Set X) ⊆ L := interior_subset
  obtain ⟨s,hLabels,hCharts⟩ :=
    proper_fibre_component_windows_over_compact C hLF W hCW hWindow K hCompare hCentres hCompact D hD hP hQ U L hL hUL
  exact ⟨U,L,s,hxU,hL,hUL,hLabels,hCharts⟩

end
end Hironaka.HironakaG3ProperFibreComponentWindows
