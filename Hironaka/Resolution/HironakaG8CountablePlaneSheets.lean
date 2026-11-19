import Hironaka.Blowup.BlowupTowers

/-! # A countable disjoint union of actual complex coordinate planes -/
set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CountablePlaneSheets

open BlowupTowers

abbrev PlaneSheets := ℕ × ComplexModel 2

/-- The actual chart of an entire open-and-closed sheet. -/
def sheetChart (i : ℕ) : OpenPartialHomeomorph PlaneSheets (ComplexModel 2) where
  toFun := Prod.snd
  invFun v := (i,v)
  source := {i} ×ˢ univ
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => ⟨mem_singleton i, mem_univ _⟩
  left_inv' _ hp := Prod.ext (mem_singleton_iff.mp hp.1).symm rfl
  right_inv' := fun _ _ => rfl
  open_source := (isOpen_discrete _).prod isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_snd.continuousOn
  continuousOn_invFun := (continuous_const.prodMk continuous_id).continuousOn

instance : ChartedSpace (ComplexModel 2) PlaneSheets where
  atlas := range sheetChart
  chartAt p := sheetChart p.1
  mem_chart_source p := ⟨mem_singleton p.1,mem_univ _⟩
  chart_mem_atlas p := ⟨p.1,rfl⟩

instance : IsComplexManifold 2 PlaneSheets where
  toIsManifold := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact contDiff_id.contDiffOn

noncomputable abbrev sheetManifold : CMfd.{0} 2 := CMfd.of PlaneSheets

/-- A compact subset only sees finitely many of the disjoint open sheets. -/
theorem finite_sheets_meeting_compact (K : Set PlaneSheets) (hK : IsCompact K) :
    {i : ℕ | (K ∩ ({i} ×ˢ univ)).Nonempty}.Finite := by
  have hImage := (hK.image continuous_fst).finite_of_discrete
  refine hImage.subset ?_
  rintro i ⟨p,hp,hpi⟩
  exact ⟨p,hp,mem_singleton_iff.mp hpi.1⟩

/-- A subset defined by actual analytic subsets separately on each sheet
is analytic in the preferred charts of the countable plane union. -/
theorem isComplexAnalyticSubset_sheetwise (W : ℕ → Set (ComplexModel 2))
    (hW : ∀ i, IsComplexAnalyticSubset (n := 2) (W i)) :
    IsComplexAnalyticSubset (n := 2) {x : PlaneSheets | x.2 ∈ W x.1} := by
  intro x
  obtain ⟨p⟩ := hW x.1 x.2
  refine ⟨{
    generatorCount := p.generatorCount
    generator := p.generator
    coordinateNeighborhood := p.coordinateNeighborhood
    isOpen_coordinateNeighborhood := p.isOpen_coordinateNeighborhood
    center_mem_coordinateNeighborhood := p.center_mem_coordinateNeighborhood
    coordinateNeighborhood_subset_target := subset_univ _
    generator_holomorphic := p.generator_holomorphic
    zeroLocus := ?_ }⟩
  intro y hy hyN
  have hyx : y.1 = x.1 := mem_singleton_iff.mp hy.1
  change y.2 ∈ W y.1 ↔ ∀ i, p.generator i y.2 = 0
  rw [hyx]
  exact p.zeroLocus (mem_chart_source _ y.2) hyN

end Hironaka.HironakaG8CountablePlaneSheets
