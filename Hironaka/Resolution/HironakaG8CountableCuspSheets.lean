import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Resolution.HironakaSharpActualCurveOverlapMaps

set_option autoImplicit false
open Set Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CountableCuspSheets
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource
  BlowupRestrictOpen MaxLocusLocal AnalyticSubsetOpens

abbrev CuspSheets := ℕ × ComplexModel 3

/-- Each whole clopen sheet is an actual ambient chart. -/
def sheetChart (i : ℕ) : OpenPartialHomeomorph CuspSheets (ComplexModel 3) where
  toFun := Prod.snd
  invFun z := (i,z)
  source := {i} ×ˢ univ
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => ⟨mem_singleton i,mem_univ _⟩
  left_inv' _ hp := Prod.ext (mem_singleton_iff.mp hp.1).symm rfl
  right_inv' := fun _ _ => rfl
  open_source := (isOpen_discrete _).prod isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_snd.continuousOn
  continuousOn_invFun := (continuous_const.prodMk continuous_id).continuousOn

instance : ChartedSpace (ComplexModel 3) CuspSheets where
  atlas := range sheetChart
  chartAt p := sheetChart p.1
  mem_chart_source p := ⟨mem_singleton p.1,mem_univ _⟩
  chart_mem_atlas p := ⟨p.1,rfl⟩

instance : IsComplexManifold 3 CuspSheets where
  toIsManifold := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact contDiff_id.contDiffOn

abbrev sheetManifold : CMfd.{0} 3 := CMfd.of CuspSheets

/-- The finite prefix consists of every entire sheet up to index m. -/
def prefixOpen (m : ℕ) : Opens CuspSheets :=
  ⟨Prod.fst ⁻¹' Set.Iic m,(isOpen_discrete _).preimage continuous_fst⟩

theorem prefixOpen_isClosed (m : ℕ) : IsClosed (prefixOpen m : Set CuspSheets) :=
  (isClosed_discrete (Set.Iic m)).preimage continuous_fst

theorem prefixOpen_mono : Monotone prefixOpen := by
  intro i j hij z hz
  exact hz.trans hij

theorem prefixOpen_point_cover (z : CuspSheets) : ∃ m, z ∈ prefixOpen m :=
  ⟨z.1,show z.1 ≤ z.1 from le_rfl⟩

/-- Compact subsets of the actual ambient see a bounded range of
discrete sheet indices. -/
theorem prefixOpen_compact_cofinal (K : Set CuspSheets) (hK : IsCompact K) :
    ∃ m, K ⊆ (prefixOpen m : Set CuspSheets) := by
  obtain ⟨m,hm⟩ := ((hK.image continuous_fst).finite_of_discrete).bddAbove
  refine ⟨m,fun z hz => ?_⟩
  exact hm ⟨z,hz,rfl⟩

def sheetOpen (i : ℕ) : Opens CuspSheets :=
  ⟨(sheetChart i).source,(sheetChart i).open_source⟩

theorem sheetOpen_isClosed (i : ℕ) : IsClosed (sheetOpen i : Set CuspSheets) :=
  (isClosed_singleton : IsClosed ({i} : Set ℕ)).prod isClosed_univ

theorem sheetOpen_le_prefix {i m : ℕ} (hi : i ≤ m) : sheetOpen i ≤ prefixOpen m := by
  intro z hz
  have h : z.1 = i := mem_singleton_iff.mp hz.1
  change z.1 ≤ m
  rwa [h]

/-- Literal sheet coordinate substitution. -/
def sheetBiholomorph (i : ℕ) :
    sheetOpen i ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ ComplexModel 3 where
  toEquiv :=
    { toFun := fun z => z.val.2
      invFun := fun z => ⟨(i,z),mem_singleton i,mem_univ z⟩
      left_inv := fun z => Subtype.ext (Prod.ext (mem_singleton_iff.mp z.property.1).symm rfl)
      right_inv := fun _ => rfl }
  contMDiff_toFun := by
    have h := contMDiffOn_chart (I := 𝓘(ℂ,ComplexModel 3)) (n := ∞)
      (x := ((i,0) : CuspSheets))
    exact contMDiff_restrict (U := sheetOpen i) h
  contMDiff_invFun := by
    intro z
    apply (ContMDiffAt.subtypeVal_comp_iff (sheetOpen i) _ z).mp
    have h := contMDiffOn_chart_symm (I := 𝓘(ℂ,ComplexModel 3)) (n := ∞)
      (x := ((i,0) : CuspSheets))
    exact h.contMDiffAt (show (sheetChart i).target ∈ 𝓝 z from univ_mem)

/-- The cusp exponent can vary independently on each clopen sheet. -/
def sheetCusps (p : ℕ → ℕ) : Set CuspSheets := {z | z.2 ∈ embeddedCuspSet (p z.1)}

theorem sheetCusps_isAnalytic (p : ℕ → ℕ) :
    IsComplexAnalyticSubset (n := 3) (sheetCusps p) := by
  intro x
  obtain ⟨q⟩ := embedded_cusp_isAnalytic (p x.1) x.2
  refine ⟨{
    generatorCount := q.generatorCount
    generator := q.generator
    coordinateNeighborhood := q.coordinateNeighborhood
    isOpen_coordinateNeighborhood := q.isOpen_coordinateNeighborhood
    center_mem_coordinateNeighborhood := q.center_mem_coordinateNeighborhood
    coordinateNeighborhood_subset_target := subset_univ _
    generator_holomorphic := q.generator_holomorphic
    zeroLocus := ?_ }⟩
  intro y hy hyN
  have hyx : y.1 = x.1 := mem_singleton_iff.mp hy.1
  change y.2 ∈ embeddedCuspSet (p y.1) ↔ ∀ i, q.generator i y.2 = 0
  rw [hyx]
  exact q.zeroLocus (mem_chart_source _ y.2) hyN

theorem sheetCusps_isClosed (p : ℕ → ℕ) : IsClosed (sheetCusps p) :=
  (sheetCusps_isAnalytic p).isClosed

theorem sheetCusps_preimage_sheet (p : ℕ → ℕ) (i : ℕ) :
    (Subtype.val : sheetOpen i → CuspSheets) ⁻¹' sheetCusps p =
      sheetBiholomorph i ⁻¹' embeddedCuspSet (p i) := by
  ext z
  change z.val.2 ∈ embeddedCuspSet (p z.val.1) ↔ z.val.2 ∈ embeddedCuspSet (p i)
  rw [mem_singleton_iff.mp z.property.1]

/-- The actual occurrence of a whole sheet inside the finite prefix. -/
def prefixSheetOpen (m i : ℕ) : Opens (prefixOpen m) :=
  nestedOpens (prefixOpen m) (sheetOpen i)

def prefixSheetBiholomorph {m i : ℕ} (hi : i ≤ m) :
    prefixSheetOpen m i ≃ₘ⟮𝓘(ℂ,ComplexModel 3),𝓘(ℂ,ComplexModel 3)⟯ ComplexModel 3 :=
  (nestedOpensDiffeo (n := 3) (sheetOpen_le_prefix hi)).trans (sheetBiholomorph i)

/-- The actual prefix restriction and the actual sheet chart recover
exactly the original local embedded cusp. -/
theorem sheetCusps_preimage_prefix_sheet (p : ℕ → ℕ) {m i : ℕ} (hi : i ≤ m) :
    (Subtype.val : prefixSheetOpen m i → prefixOpen m) ⁻¹'
      ((Subtype.val : prefixOpen m → CuspSheets) ⁻¹' sheetCusps p) =
        prefixSheetBiholomorph hi ⁻¹' embeddedCuspSet (p i) := by
  ext z
  change z.val.val.2 ∈ embeddedCuspSet (p z.val.val.1) ↔
    z.val.val.2 ∈ embeddedCuspSet (p i)
  rw [mem_singleton_iff.mp z.property.1]

end
end Hironaka.HironakaG8CountableCuspSheets

#print axioms Hironaka.HironakaG8CountableCuspSheets.prefixOpen_compact_cofinal
#print axioms Hironaka.HironakaG8CountableCuspSheets.sheetCusps_isAnalytic
#print axioms Hironaka.HironakaG8CountableCuspSheets.sheetCusps_preimage_prefix_sheet
