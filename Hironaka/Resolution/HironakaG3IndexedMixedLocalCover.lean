import Hironaka.Resolution.HironakaG3IndexedMixedWindowProducer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedLocalCover
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers RestrictEmptyTower NormalCrossings HironakaBaseChange
  HironakaAdmissibleSequence HironakaEmbeddedAnalyticLocal HironakaG3FiniteMixedBadLocus
  HironakaG3MixedOrderedSeparation HironakaG3IndexedMixedWindowProducer HironakaActualLocallyFiniteBoundary

/-- Simultaneously locally finite component and boundary families provide
compact-enclosed source windows containing every visible label, with an actual
admissible canonical separator tower on each window. -/
theorem indexed_mixed_local_cover {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hV : LocallyFinite (fun i => (V i).carrier))
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) (x : X) :
    ∃ (U : Opens X) (s : Finset ι) (r : Finset κ), x ∈ U ∧
      (∀ i, ((V i).carrier ∩ (U : Set X)).Nonempty → i ∈ s) ∧
      (∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ r) ∧
      let l := s.sort (· ≤ ·)
      let W : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y) (Ef : List (Set Y)),
        CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
          (l.map (fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim))) T Ef ∧
        CentresOver ((Subtype.val : U → X) ⁻¹' mixedBadLocus W) T ∧
        IsAdmissibleBlowupSequence n U (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
          ((Subtype.val : U → X) ⁻¹' mixedBadLocus W) Y T.proj Ef ∧ IsSNCDivisor n Ef ∧
        (List.finRange l.length).Pairwise (fun a c =>
          Disjoint (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' (W a).carrier))
            (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' (W c).carrier))) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨A,hAx,hAfin⟩ := hV x
  obtain ⟨B,hBx,hBfin⟩ := hD.1 x
  obtain ⟨O,hOA,hOo,hxO⟩ := mem_nhds_iff.mp hAx
  obtain ⟨P,hPB,hPo,hxP⟩ := mem_nhds_iff.mp hBx
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  let U : Opens X := ⟨O ∩ P ∩ interior K,(hOo.inter hPo).inter isOpen_interior⟩
  let s := hAfin.toFinset
  let r := hBfin.toFinset
  have hxU : x ∈ U := ⟨⟨hxO,hxP⟩,mem_interior_iff_mem_nhds.mpr hxK⟩
  have hs : ∀ i, ((V i).carrier ∩ (U : Set X)).Nonempty → i ∈ s := by
    intro i ⟨z,hzV,hzU⟩
    apply hAfin.mem_toFinset.mpr
    exact ⟨z,hzV,hOA hzU.1.1⟩
  have hr : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ r := by
    intro i ⟨z,hzD,hzU⟩
    apply hBfin.mem_toFinset.mpr
    exact ⟨z,hzD,hPB hzU.1.2⟩
  have hRange : range (Subtype.val : U → X) ⊆ K := by
    rintro _ ⟨z,rfl⟩
    exact interior_subset z.property.2
  refine ⟨U,s,r,hxU,hs,hr,?_⟩
  exact sorted_window_producer (B₀ := CMfd.of (n := n) U) V hDim hDistinct D hD s r
    (Subtype.val : U → X) (isOpenHoloEmbedding_val (n := n) U) ⟨K,hK,hRange⟩
end
end Hironaka.HironakaG3IndexedMixedLocalCover
