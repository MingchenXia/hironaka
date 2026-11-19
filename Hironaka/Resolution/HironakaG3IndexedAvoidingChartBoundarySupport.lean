import Hironaka.Resolution.HironakaG3IndexedAvoidingChartBoundaryOverlap
import Hironaka.Resolution.HironakaG3IndexedBoundaryWindowSupport
import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedAvoidingChartBoundarySupport
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RBoundaryEmbedded
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3IndexedBoundaryWindowSupport
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3IndexedAvoidingChartBoundaryOverlap

/-- Actual zero-containing chart support is the inherited support plus the actual exceptional locus. -/
theorem avoiding_chart_boundary_support {n : ℕ} {X Z : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (indexedAvoidingBoundaryClass C r D) Z P) :
    (⋃ H ∈ avoidingChartBoundary C r D c, H) =
      (P ⁻¹' (⋃ i, D i) ∪ exceptionalLocus n P) ∩ c.V := by
  let R := avoidingChartWindow C r D c
  let E := (R.sort (· ≤ ·)).map D
  let G := ⋃ i, D i
  let A := fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·))
    (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) C))
  have hc := Classical.choose_spec c.mem
  change (∀ i, (D i ∩ (c.U : Set X)).Nonempty → i ∈ R) ∧ bdryClass C r E c.U c.Y c.T at hc
  have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ E, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiS : i ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  have hInter : (⋃ H ∈ E, H) ∩ (c.U : Set X) = G ∩ (c.U : Set X) := by
    ext x
    have hh := Set.ext_iff.mp (indexed_window_support_inter D ∅ R c.U (fun i _ => hc.1 i)) x
    simpa only [E,G,mem_inter_iff,mem_iUnion,exists_prop,List.mem_append,List.mem_map,Finset.mem_sort,Finset.notMem_empty,false_and,exists_false,or_false] using hh
  have hTrace : (Subtype.val : c.U → X) ⁻¹' (⋃ H ∈ E, H) = (Subtype.val : c.U → X) ⁻¹' G := by
    ext x
    have hx := Set.ext_iff.mp hInter (x : X)
    simp only [mem_inter_iff] at hx
    exact ⟨fun h => (hx.mp ⟨h,x.property⟩).1,fun h => (hx.mpr ⟨h,x.property⟩).1⟩
  have hg := bdry_stopped_geometry hC.analytic hr hpure hE hAvoid c.U c.T hc.2
  simp only [MarkedIdealBiholomorphism.MarkedIdeal.pullback, preimage_univ] at hg
  change _ ∧ _ ∧ _ ∧ _ ∧ (⋃ H ∈ (geoTransformAlong A c.T).E, H) = _ ∧ _ at hg
  have hlocal : (⋃ H ∈ (geoTransformAlong A c.T).E, H) =
      c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' G) ∪ exceptionalLocus n c.T.proj := by
    change (⋃ H ∈ (geoTransformAlong _ c.T).E, H) = _
    rw [hg.2.2.2.2.1,hTrace]
    ext y
    constructor
    · rintro (hy | hy)
      · exact Or.inl hy
      · have hy' := hg.2.2.1 hy
        rcases hy' with hsing | ⟨_,hboundary⟩
        · exact Or.inr (hg.2.2.2.1 hsing)
        · exact Or.inl (by rw [← hTrace]; exact hboundary)
    · rintro (hy | hy)
      · exact Or.inl hy
      · exact Or.inr (hg.2.1 hy)
  unfold avoidingChartBoundary
  change (⋃ H ∈ ((geoTransformAlong A c.T).E.map (chartIncl c '' ·)), H) = _
  rw [HironakaG3RPureEmbedded.iUnion_map_image,hlocal,Set.image_union,
    HironakaG3RBoundaryEmbedded.image_chartIncl_preimage]
  have hExc : chartIncl c '' exceptionalLocus n c.T.proj = exceptionalLocus n P ∩ c.V := by
    rw [exceptionalLocus_chart c hP, Set.image_preimage_eq_inter_range, range_chartIncl]
  rw [hExc]
  ext z
  simp only [mem_union,mem_inter_iff]
  tauto
end
end Hironaka.HironakaG3IndexedAvoidingChartBoundarySupport
