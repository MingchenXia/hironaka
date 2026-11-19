import Hironaka.Resolution.HironakaG3DisjointVisibleComplementChart
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3ProperFibreComplementChart
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3DisjointVisibleComplementChart HironakaG3FiniteDisjointTowerMerge
  RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

theorem proper_fibre_complement_chart {n : ℕ} {X Z Y : CMfd.{0} n} {ι : Type u} {κ : Type v}
    (C : ι → Set Z) (hClosed : ∀ i, IsClosed (C i)) (hLF : LocallyFinite C)
    (W : ι → Opens Z) (K : ι → LocalTowerClass Z)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set Z))
    (hCompare : ∀ i, HasComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens Z) (B : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) B),
      K i U B T → CentresOver ((Subtype.val : U → Z) ⁻¹' C i) T)
    (D : κ → Set Z) (hD : LocallyFinite D) {π : Z → X} (hπ : IsProperMap π)
    {σ : Y → Z} (hσ : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Y σ)
    (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) (s : Finset ι)
    (hLabels : ∀ i, (C i ∩ π ⁻¹' (U : Set X)).Nonempty → i ∈ s) :
    let A : Opens Z := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.continuous⟩
    let O : Opens Z := ⟨(A : Set Z) ∩ (⋃ i, C i)ᶜ,
      A.isOpen.inter (hLF.isClosed_iUnion hClosed).isOpen_compl⟩
    ∃ c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Y σ,
      c.U = O ∧ IsEmptyTower c.T ∧
      finiteSupport (n := n) (X := CMfd.of (n := n) A)
        (fun i : {j // j ∈ s} => (Subtype.val : A → Z) ⁻¹' C i.val) s.attach =
        (Subtype.val : A → Z) ⁻¹' (⋃ i, C i) := by
  classical
  dsimp only
  let A : Opens Z := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.continuous⟩
  let O : Opens Z := ⟨(A : Set Z) ∩ (⋃ i, C i)ᶜ,
    A.isOpen.inter (hLF.isClosed_iUnion hClosed).isOpen_compl⟩
  have hOL : (O : Set Z) ⊆ π ⁻¹' L := fun z hz => hUL hz.1
  obtain ⟨c,hc,hEmpty⟩ := disjoint_visible_complement_chart C W K D hWindow hCompare hCentres hD hσ
    O (fun z hz => hz.2) (π ⁻¹' L) (hπ.isCompact_preimage hL) hOL
  refine ⟨c,hc,hEmpty,?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i,_,hi⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion.mpr ⟨i.val,hi⟩
  · intro hz
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
    have his : i ∈ s := hLabels i ⟨z.val,hi,z.property⟩
    exact Set.mem_iUnion₂.mpr ⟨⟨i,his⟩,Finset.mem_attach s _,hi⟩
end
end Hironaka.HironakaG3ProperFibreComplementChart
