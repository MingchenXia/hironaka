import Hironaka.Resolution.HironakaG3SeparatedAvoidingGeometry
import Hironaka.Resolution.HironakaG3DisjointAtlasCommonGood
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedAvoidingGood
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows HironakaG3IndexedAvoidingBoundaryClass
  HironakaG3RBoundaryEmbedded HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointAtlasCommonGood

theorem iso_mono {n : ℕ} {X Y : CMfd.{0} n} {f : Y → X} {U V : Set X}
    (hUV : U ⊆ V) (h : IsIsomorphismOver n f V) : IsIsomorphismOver n f U := by
  constructor
  · refine ⟨fun _ hx => hx,?_,?_⟩
    · intro y hy z hz he
      exact h.1.2.1 (hUV hy) (hUV hz) he
    · intro x hx
      obtain ⟨y,_,hy⟩ := h.1.2.2 (hUV hx)
      refine ⟨y,?_,hy⟩
      change f y ∈ U
      rw [hy]
      exact hx
  · exact Set.disjoint_left.mpr fun z hz hz' => (Set.disjoint_left.mp h.2) (hUV hz) hz'

/-- Every actual avoiding-window history is an isomorphism over the original
boundary-relative good locus of its component. -/
theorem indexed_avoiding_member_original_good {n : ℕ} {X Y : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (r : ℕ) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (U : Opens X) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : indexedAvoidingBoundaryClass C r D U Y T) :
    IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹'
      (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ j, D j)ᶜ) := by
  obtain ⟨R,_hVis,hStop⟩ := hT
  let E := (R.sort (· ≤ ·)).map D
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ E, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    have hjS : j ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)
  have hgeo := bdry_stopped_geometry hC.analytic hr hpure (sorted_boundary_snc D hD R) hAvoid U T hStop
  apply iso_mono _ hgeo.2.2.2.2.2.1
  intro u hu
  change (u : X) ∉ (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ j, D j) at hu
  change (u : X) ∉ (C \ regularLocus (n := n) C r ∪ C ∩ ⋃ H ∈ E, H)
  intro hbad
  apply hu
  rcases hbad with hbad | ⟨hxC,hB⟩
  · exact Or.inl hbad
  · refine Or.inr ⟨hxC,?_⟩
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hB
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    exact mem_iUnion.mpr ⟨j,hxH⟩

theorem separated_avoiding_original_good {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) {P : Z → X}
    (hG : IsGluedFrom (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) Z P) :
    IsIsomorphismOver n P (⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j))ᶜ := by
  apply disjoint_atlas_isomorphism_over_common_good C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D) _ ?_ hG
  intro i U Y T hT
  apply iso_mono _ (indexed_avoiding_member_original_good (C i) (r i) D (hC i) hD (hS i) (hr i) (hpure i) U T hT)
  intro u hu
  change (u : X) ∉ ⋃ i, (C i \ regularLocus (n := n) (C i) (r i)) ∪ (C i ∩ ⋃ j, D j) at hu
  change (u : X) ∉ (C i \ regularLocus (n := n) (C i) (r i) ∪ C i ∩ ⋃ j, D j)
  intro hbad
  exact hu (mem_iUnion.mpr ⟨i,hbad⟩)

end
end Hironaka.HironakaG3SeparatedAvoidingGood
