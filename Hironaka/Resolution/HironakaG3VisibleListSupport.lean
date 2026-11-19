import Hironaka.Resolution.HironakaG3SeparatedVisibleChartSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VisibleListSupport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaDisjointFiniteControlledHistory HironakaG3RBoundaryOverlap
  HironakaActualLocallyFiniteBoundary HironakaEmbeddedBoundary

theorem visible_list_transformed_support {n : ℕ} {X : CMfd.{0} n} {κ : Type*}
    (D : κ → Set X) (hD : ∀ i, IsClosed (D i)) (U : Opens X) (E : List (Set X))
    (hMembers : ∀ H ∈ E, ∃ i, H = D i)
    (hVis : ∀ i, (D i ∩ (U : Set X)).Nonempty → D i ∈ E)
    (J : GermIdeal n (CMfd.of (n := n) U)) {Y : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) :
    (⋃ H ∈ (geoTransformAlong (fullMarked (E.map ((Subtype.val : U → X) ⁻¹' ·)) J) T).E, H) =
      T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (⋃ i, D i)) ∪ (exceptionalDivisor T).support := by
  let M := fullMarked (E.map ((Subtype.val : U → X) ⁻¹' ·)) J
  have hE : ∀ H ∈ M.E, IsClosed H := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    obtain ⟨i,rfl⟩ := hMembers K hK
    exact (hD i).preimage continuous_subtype_val
  have hTrace : (Subtype.val : U → X) ⁻¹' (⋃ H ∈ E, H) = (Subtype.val : U → X) ⁻¹' (⋃ i, D i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hx
      obtain ⟨i,rfl⟩ := hMembers H hH
      exact mem_iUnion.mpr ⟨i,hxH⟩
    · intro hx
      obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨D i,hVis i ⟨x,hxi,x.property⟩,hxi⟩
  change (⋃ H ∈ (geoTransformAlong M T).E, H) = _
  rw [biUnion_E_geoTransformAlong M hE T]
  change T.proj ⁻¹' (⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), H) ∪ _ = _
  rw [← preimage_biUnion_list,hTrace]
end
end Hironaka.HironakaG3VisibleListSupport
