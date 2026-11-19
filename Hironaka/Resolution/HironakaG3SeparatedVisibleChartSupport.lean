import Hironaka.Resolution.HironakaG3SeparatedVisibleChartBoundary
import Hironaka.Resolution.HironakaG3IndexedAvoidingChartBoundarySupport
import Hironaka.Resolution.HironakaG3IndexedBoundaryWindowSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedVisibleChartSupport
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaDisjointFiniteControlledHistory
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RBoundaryOverlap HironakaG3RBoundaryEmbedded
  HironakaEmbeddedBoundary HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3IndexedBoundaryWindowSupport HironakaG3IndexedAvoidingBoundaryClass
  HironakaG3IndexedAvoidingChartBoundaryOverlap HironakaG3IndexedAvoidingChartBoundarySupport
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SeparatedVisibleChartWindow
  HironakaG3SeparatedVisibleChartBoundary RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

/-- Full support after a tower depends on a visible finite boundary window,
not on its extra invisible labels or its marked ideal. -/
theorem visible_window_transformed_support {n : ℕ} {X : CMfd.{0} n} {κ : Type*} [LinearOrder κ]
    (D : κ → Set X) (hD : ∀ i, IsClosed (D i)) (U : Opens X) (R : Finset κ)
    (hVis : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ R)
    (J : GermIdeal n (CMfd.of (n := n) U)) {Y : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) :
    (⋃ H ∈ (geoTransformAlong (fullMarked (((R.sort (· ≤ ·)).map D).map
        ((Subtype.val : U → X) ⁻¹' ·)) J) T).E, H) =
      T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (⋃ i, D i)) ∪ (exceptionalDivisor T).support := by
  let E := (R.sort (· ≤ ·)).map D
  let M := fullMarked (E.map ((Subtype.val : U → X) ⁻¹' ·)) J
  have hE : ∀ H ∈ M.E, IsClosed H := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hK
    exact (hD i).preimage continuous_subtype_val
  have hInter : (⋃ H ∈ E, H) ∩ (U : Set X) = (⋃ i, D i) ∩ (U : Set X) := by
    ext x
    have hh := Set.ext_iff.mp (indexed_window_support_inter D ∅ R U (fun i _ => hVis i)) x
    simpa only [E,mem_inter_iff,mem_iUnion,exists_prop,List.mem_append,List.mem_map,Finset.mem_sort,
      Finset.notMem_empty,false_and,exists_false,or_false] using hh
  have hTrace : (Subtype.val : U → X) ⁻¹' (⋃ H ∈ E, H) = (Subtype.val : U → X) ⁻¹' (⋃ i, D i) := by
    ext x
    have hx := Set.ext_iff.mp hInter (x : X)
    simp only [mem_inter_iff] at hx
    exact ⟨fun h => (hx.mp ⟨h,x.property⟩).1,fun h => (hx.mpr ⟨h,x.property⟩).1⟩
  change (⋃ H ∈ (geoTransformAlong M T).E, H) = _
  rw [biUnion_E_geoTransformAlong M hE T]
  change T.proj ⁻¹' (⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), H) ∪ _ = _
  rw [← preimage_biUnion_list,hTrace]

private theorem empty_centres_over {n : ℕ} {X : CMfd.{0} n} :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsEmptyTower T → CentresOver (∅ : Set X) T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => ⟨empty_centres_over T h.1, by rw [h.2]; exact empty_subset _⟩

/-- Every actual finite-visible separated chart has precisely the inherited
indexed boundary plus exceptional support, restricted to that chart. -/
theorem separated_visible_chart_boundary_support {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
      (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) :
    (⋃ H ∈ separatedVisibleChartBoundary C r D W c, H) =
      (P ⁻¹' (⋃ i, D i) ∪ exceptionalLocus n P) ∩ c.V := by
  let R := separatedChartWindow C r D W c
  have hSpec := separated_chart_window_spec C r D W c
  have hVis : ∀ i, (D i ∩ (c.U : Set X)).Nonempty → i ∈ R := hSpec.1
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  have hlocal := visible_window_transformed_support D hD.2.1 c.U R hVis J c.T
  rcases hSpec.2 with ⟨i,hUW,hStop⟩ | ⟨_,hEmpty⟩
  · have hK : indexedAvoidingBoundaryClass (C i) (r i) D c.U c.Y c.T := ⟨R,hVis,hStop⟩
    let c' : TowerChart (indexedAvoidingBoundaryClass (C i) (r i) D) Z P :=
      ⟨c.U,c.Y,c.T,hK,c.V,c.V_eq,c.φ,c.proj_φ⟩
    let R' := avoidingChartWindow (C i) (r i) D c'
    have hVis' : ∀ j, (D j ∩ (c'.U : Set X)).Nonempty → j ∈ R' := (Classical.choose_spec c'.mem).1
    let J' := GermIdeal.pullback (m := n) (Subtype.val : c'.U → X) (vanishingIdeal (n := n) (C i))
    have hlocal' := visible_window_transformed_support D hD.2.1 c'.U R' hVis' J' c'.T
    have hEq : (⋃ H ∈ separatedVisibleChartBoundary C r D W c, H) =
        ⋃ H ∈ avoidingChartBoundary (C i) (r i) D c', H := by
      unfold separatedVisibleChartBoundary avoidingChartBoundary
      rw [HironakaG3RPureEmbedded.iUnion_map_image,HironakaG3RPureEmbedded.iUnion_map_image]
      change chartIncl c '' (⋃ H ∈ (geoTransformAlong _ c.T).E, H) =
        chartIncl c' '' (⋃ H ∈ (geoTransformAlong _ c'.T).E, H)
      rw [hlocal,hlocal']
      rfl
    rw [hEq]
    exact avoiding_chart_boundary_support (C i) D (hC i) hD (hS i) (hr i) (hpure i) hP c'
  · have hSupp : (exceptionalDivisor c.T).support = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh := support_exceptionalDivisor_subset_of_centresOver (∅ : Set (CMfd.of (n := n) c.U)) c.T
        (empty_centres_over c.T hEmpty) hy
      exact hh
    have hExc : exceptionalLocus n c.T.proj = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh := HironakaPrincipalization.exceptionalLocus_subset_support c.T hy
      rw [hSupp] at hh
      exact hh
    have hExcChart : exceptionalLocus n P ∩ c.V = ∅ := by
      rw [← range_chartIncl c, ← Set.image_preimage_eq_inter_range, ← exceptionalLocus_chart c hP, hExc]
      simp
    unfold separatedVisibleChartBoundary
    rw [HironakaG3RPureEmbedded.iUnion_map_image,hlocal,hSupp,union_empty,
      HironakaG3RBoundaryEmbedded.image_chartIncl_preimage]
    ext z
    have hz : z ∉ exceptionalLocus n P ∩ c.V := by rw [hExcChart]; exact notMem_empty z
    simp only [mem_inter_iff,mem_union] at hz ⊢
    tauto
end
end Hironaka.HironakaG3SeparatedVisibleChartSupport
