import Hironaka.Resolution.HironakaEmbeddedResolution
import Hironaka.Resolution.HironakaG8StageRankCoherence

/-! Closed centre components retain the local centre geometry. Proper
projection detects exactly which of those components are compact. -/
set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Topology
namespace Hironaka.HironakaG8CentreComponentCompactness

open Hironaka.BlowupSequences BlowupTowers
  HironakaEmbeddedAnalytic HironakaEmbeddedResolution CodimOneSupport
  NormalCrossings

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem isClosed_centreComponent {C : Set Y} (hC : IsClosed C) {c : Y} (hc : c ∈ C) :
    IsClosed (connectedComponentIn C c) := by
  rw [connectedComponentIn_eq_image hc]
  exact hC.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent

theorem centreComponent_isClosedSubmanifold {C : Set Y} (hC : IsClosedSubmanifold n C)
    {c : Y} (hc : c ∈ C) : IsClosedSubmanifold n (connectedComponentIn C c) := by
  refine ⟨isClosed_centreComponent hC.1 hc,?_⟩
  intro x hx
  obtain ⟨d,hd⟩ := hC.2 x (connectedComponentIn_subset C c hx)
  exact ⟨d,regularAtDim_of_eventually_mem_iff
    ((eventually_mem_connectedComponentIn_iff hC hx).mono fun _ h => h.symm) hd⟩

/-- The exact local dimension and old-boundary normal crossings are retained
by passage to a connected component. -/
theorem centreComponent_regular_and_crossings {C : Set Y} (hC : IsClosedSubmanifold n C)
    {E : List (Set Y)} (hCross : HasNormalCrossings n C E) {c : Y} (hc : c ∈ C) :
    IsClosedSubmanifold n (connectedComponentIn C c) ∧
    HasNormalCrossings n (connectedComponentIn C c) E ∧
    ∀ x ∈ connectedComponentIn C c, ∀ d,
      RegularAtDim (n := n) (connectedComponentIn C c) x d ↔ RegularAtDim (n := n) C x d := by
  refine ⟨centreComponent_isClosedSubmanifold hC hc,hasNormalCrossings_connectedComponentIn hC hCross c,?_⟩
  intro x hx d
  have h := eventually_mem_connectedComponentIn_iff hC hx
  exact ⟨regularAtDim_of_eventually_mem_iff h,
    regularAtDim_of_eventually_mem_iff (h.mono fun _ h' => h'.symm)⟩

/-- Compactness of the original projected footprint of a closed component
is exactly compactness of the component on the current physical manifold. -/
theorem compact_centreComponent_image_iff (T : BlowupTower X Y)
    {C : Set Y} (hC : IsClosed C) {c : Y} (hc : c ∈ C) :
    IsCompact (T.proj '' connectedComponentIn C c) ↔
      IsCompact (connectedComponentIn C c) := by
  constructor
  · intro h
    have hK := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage h
    apply hK.of_isClosed_subset (isClosed_centreComponent hC hc)
    exact subset_preimage_image _ _
  · intro h
    exact h.image T.contMDiff_proj.continuous

/-- A germ-preserving closed cut of a centre contains each component it hits.
This is the obstruction to cutting a noncompact connected component into
compact pieces by an exhaustion while keeping the same local centre. -/
theorem centreComponent_subset_of_closed_local_cut {C D : Set Y}
    (hD : IsClosed D) {c : Y} (hc : c ∈ C) (hcD : c ∈ D)
    (hLocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ D) :
    connectedComponentIn C c ⊆ D := by
  let S : Set Y := connectedComponentIn C c
  obtain ⟨U,hU,hEq⟩ : ∃ U : Set Y, IsOpen U ∧ S ∩ U = S ∩ D := by
    let U := interior {y : Y | y ∈ C → y ∈ D}
    refine ⟨U,isOpen_interior,?_⟩
    ext y
    exact ⟨fun ⟨hy,hyU⟩ => ⟨hy,(interior_subset hyU) (connectedComponentIn_subset C c hy)⟩,
      fun ⟨hy,hyD⟩ => ⟨hy,mem_interior_iff_mem_nhds.mpr (hLocal y hyD)⟩⟩
  have hPre : IsPreconnected S := isPreconnected_connectedComponentIn
  have hComp : S ⊆ D ∪ Uᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl ((show y ∈ S ∩ D from hEq ▸ ⟨hy,hyU⟩)).2
    · exact Or.inr hyU
  have hDisj : S ∩ (D ∩ Uᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy,hyD,hyN⟩
    exact hyN ((show y ∈ S ∩ U from hEq.symm ▸ ⟨hy,hyD⟩)).2
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hPre D Uᶜ hD hU.isClosed_compl hComp hDisj with h | h
  · exact h
  · have hcS : c ∈ S := mem_connectedComponentIn hc
    exact ((h hcS) ((show c ∈ S ∩ U from hEq.symm ▸ ⟨hcS,hcD⟩)).2).elim

/-- Equal local dimensions already force a closed submanifold cut of a
centre to contain the whole component through each point of the cut. -/
theorem centreComponent_subset_of_closed_sameDimension {C D : Set Y}
    (hD : IsClosedSubmanifold n D) (hDC : D ⊆ C)
    {c : Y} (hc : c ∈ D)
    (hDim : ∀ x ∈ D, ∃ d, RegularAtDim (n := n) D x d ∧ RegularAtDim (n := n) C x d) :
    connectedComponentIn C c ⊆ D := by
  apply centreComponent_subset_of_closed_local_cut hD.1 (hDC hc) hc
  intro x hx
  obtain ⟨d,hd,hc⟩ := hDim x hx
  exact eventually_mem_of_locDimGE
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hD)
    hc (Eventually.of_forall fun _ hy => hDC hy)
    (AnalyticDimensionBasics.locDimGE_of_regularAtDim hd)

/-- An equal-dimensional closed subcentre through a noncompact component
has a noncompact source footprint, even after proper physical projection. -/
theorem noncompact_projected_sameDimension_subcentre (T : BlowupTower X Y)
    {C D : Set Y} (hD : IsClosedSubmanifold n D) (hDC : D ⊆ C)
    {c : Y} (hc : c ∈ D) (hC : IsClosed C)
    (hDim : ∀ x ∈ D, ∃ d, RegularAtDim (n := n) D x d ∧ RegularAtDim (n := n) C x d)
    (hNoncompact : ¬ IsCompact (connectedComponentIn C c)) :
    ¬ IsCompact (T.proj '' D) := by
  intro hK
  have hComp := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
  apply hNoncompact
  apply hComp.of_isClosed_subset (isClosed_centreComponent hC (hDC hc))
  exact (centreComponent_subset_of_closed_sameDimension hD hDC hc hDim).trans
    (subset_preimage_image T.proj D)

end Hironaka.HironakaG8CentreComponentCompactness
