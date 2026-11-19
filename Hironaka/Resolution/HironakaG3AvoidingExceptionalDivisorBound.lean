import Hironaka.Resolution.HironakaG3IndexedAvoidingChartBoundarySupport
import Hironaka.Resolution.HironakaG3EmptyAwareBornSlots
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AvoidingExceptionalDivisorBound
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaDisjointFiniteControlledHistory
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3IndexedAvoidingBoundaryClass HironakaG3RBoundaryEmbedded
  HironakaEmbeddedBoundary HironakaPrincipalizationBoundary HironakaG3EmptyAwareBornSlots

/-- Actual zero-containing stopped histories have their exceptional divisor
supported over the original boundary or their actual exceptional locus. -/
theorem indexed_avoiding_exceptional_divisor_bound {n r : ℕ} {X Y : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅) (hr : r < n)
    (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (U : Opens X) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : indexedAvoidingBoundaryClass C r D U Y T) :
    (exceptionalDivisor T).support ⊆
      T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (⋃ j, D j)) ∪ exceptionalLocus n T.proj := by
  obtain ⟨R,_hVis,hStop⟩ := hT
  let E := (R.sort (· ≤ ·)).map D
  let J := GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) C)
  let M := fullMarked (E.map ((Subtype.val : U → X) ⁻¹' ·)) J
  have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
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
  have hg := bdry_stopped_geometry hC.analytic hr hpure hE hAvoid U T hStop
  simp only [MarkedIdealBiholomorphism.MarkedIdeal.pullback,preimage_univ] at hg
  have hClosedM : ∀ H ∈ M.E, IsClosed H := by
    intro H hH
    change H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·) at hH
    obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
    obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hH'
    exact (hD.2.1 j).preimage continuous_subtype_val
  have hBorn : (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong M T).E.drop E.length, H := by
    have hh := support_exceptionalDivisor_eq_biUnion_drop M hClosedM T
    simpa [M,fullMarked] using hh
  intro y hy
  rw [hBorn] at hy
  have hy' := hg.2.2.1 hy
  rcases hy' with hsing | ⟨_hC,hboundary⟩
  · exact Or.inr (hg.2.2.2.1 hsing)
  · left
    obtain ⟨H,hH,hmem⟩ := mem_iUnion₂.mp hboundary
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    exact mem_iUnion.mpr ⟨j,hmem⟩
end
end Hironaka.HironakaG3AvoidingExceptionalDivisorBound
