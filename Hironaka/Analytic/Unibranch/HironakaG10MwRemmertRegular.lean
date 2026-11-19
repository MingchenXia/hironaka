import Hironaka.Analytic.Unibranch.OriginalSmoothNativeModel
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Analytic.RankDegeneracy
import Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim

/-!
# Native Remmert, item 5.1: the regular locus of a native space as complex manifolds (lane G10MW)

For a native reduced complex space `Y` and `d : ℕ`:

* `regLocus Y d` — the intrinsic regular points of dimension `d` (`intrinsicRegularAtDim`); it is open;
* `RegChart Y d` — a regular chart (an open immersion of the native model of an open `O ⊆ ℂ^d` over the complex
  point); `RegChart.chart` — the induced chart of the subtype `regLocus Y d`;
* the instances `ChartedSpace (ComplexModel d) (regLocus Y d)`, `IsManifold 𝓘(ℂ, ComplexModel d) ∞`, and, for
  second-countable `Y`, `IsComplexManifold d (regLocus Y d)`;
* for a native morphism `φ : Y ⟶ ofClosedAnalytic C hC` into a closed analytic subset of a complex manifold `M`:
  `pointMap φ : Y.obj.left → M`, its restriction `regPointMap φ d`, which is holomorphic (`contMDiff_regPointMap`),
  and the native rank `nativeRankAt φ d y` (the library rank `RankDegeneracy.rankAt` of `regPointMap φ d` on
  `univ`);
* `NativePureDim Y d` — every intrinsic regular point has dimension `d`;
* `rankDegeneracy φ d r` — `Sing(Y) ∪ {y ∈ Reg_d | nativeRankAt d φ y < r}` (the set of item 5.3);
* the statements `NativeProperImage` (Remmert for reduced complex spaces, the goal of item 5) and
  `NativeProperImageCore` (its core, item 5.0: second-countable source of bounded dimension, manifold target).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open IsManifold ChartedSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaEmbeddedNativeMorphism HironakaIntrinsicMorphismGluingAnalytic
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace

noncomputable section

variable (Y : SourceReducedComplexSpace) (d : ℕ)

/-- The intrinsic regular points of dimension `d`. -/
def regLocus : Set Y.obj.left := {y | intrinsicRegularAtDim Y.obj y d}

/-- **Pure dimension `d`**: every intrinsic regular point has dimension `d`. -/
def NativePureDim : Prop := ∀ (y : Y.obj.left) (j : ℕ), intrinsicRegularAtDim Y.obj y j → j = d

/-- A regular chart of dimension `d`. -/
structure RegChart where
  domain : Opens (ComplexModel d)
  map : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) domain ⟶ Y.obj.left
  openImmersion : LocallyRingedSpace.IsOpenImmersion map
  overPoint : map ≫ Y.obj.hom = ambientPointMap d domain
  nonempty : Nonempty domain

variable {Y d}

theorem RegChart.mem_regLocus (D : RegChart Y d) (v : D.domain) : D.map.base v ∈ regLocus Y d :=
  ⟨D.domain, D.map, D.openImmersion, D.overPoint, v, rfl⟩

theorem exists_regChart {y : Y.obj.left} (hy : y ∈ regLocus Y d) :
    ∃ D : RegChart Y d, y ∈ range D.map.base := by
  obtain ⟨O, i, hi, hp, v, hv⟩ := hy
  exact ⟨⟨O, i, hi, hp, ⟨v⟩⟩, v, hv⟩

theorem isOpen_regLocus : IsOpen (regLocus Y d) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨D, hD⟩ := exists_regChart hy
  refine ⟨range D.map.base, ?_, D.openImmersion.base_open.isOpen_range, hD⟩
  rintro _ ⟨v, rfl⟩
  exact D.mem_regLocus v

/-- The point map of a regular chart, into the regular locus. -/
def RegChart.pointMap (D : RegChart Y d) : D.domain → regLocus Y d :=
  fun v => ⟨D.map.base v, D.mem_regLocus v⟩

theorem RegChart.isOpenEmbedding_pointMap (D : RegChart Y d) : IsOpenEmbedding D.pointMap := by
  refine ((isOpen_regLocus (Y := Y) (d := d)).isOpenEmbedding_subtypeVal.of_comp_iff _).mp ?_
  exact D.openImmersion.base_open

/-- The chart of the regular locus induced by a regular chart. -/
def RegChart.chart (D : RegChart Y d) : OpenPartialHomeomorph (regLocus Y d) (ComplexModel d) := by
  letI := D.nonempty
  exact (D.isOpenEmbedding_pointMap.toOpenPartialHomeomorph D.pointMap).symm.trans
    (D.domain.openPartialHomeomorphSubtypeCoe D.nonempty)

theorem RegChart.chart_source (D : RegChart Y d) : D.chart.source = range D.pointMap := by
  simp [RegChart.chart]

theorem RegChart.chart_target (D : RegChart Y d) : D.chart.target = D.domain := by
  simp [RegChart.chart]

theorem RegChart.chart_pointMap (D : RegChart Y d) (v : D.domain) : D.chart (D.pointMap v) = v.val := by
  have := D.nonempty
  change ((D.isOpenEmbedding_pointMap.toOpenPartialHomeomorph D.pointMap).symm
    (D.pointMap v)).val = v.val
  rw [D.isOpenEmbedding_pointMap.toOpenPartialHomeomorph_left_inv]

theorem RegChart.chart_symm (D : RegChart Y d) (v : ComplexModel d) (hv : v ∈ D.domain) :
    D.chart.symm v = D.pointMap ⟨v, hv⟩ := by
  apply D.chart.injOn (D.chart.map_target (D.chart_target ▸ hv))
    (D.chart_source ▸ (show D.pointMap (⟨v, hv⟩ : D.domain) ∈ range D.pointMap from ⟨_, rfl⟩))
  rw [D.chart.right_inv (D.chart_target ▸ hv), D.chart_pointMap]

/-- The chosen regular chart at a regular point. -/
def regChartAt (y : regLocus Y d) : RegChart Y d := Classical.choose (exists_regChart y.property)

theorem mem_range_regChartAt (y : regLocus Y d) : y ∈ range (regChartAt y).pointMap := by
  obtain ⟨v, hv⟩ := Classical.choose_spec (exists_regChart y.property)
  exact ⟨v, Subtype.ext hv⟩

/-- The charted-space structure of the regular locus. -/
instance regChartedSpace : ChartedSpace (ComplexModel d) (regLocus Y d) where
  atlas := range (fun y => (regChartAt y).chart)
  chartAt y := (regChartAt y).chart
  mem_chart_source y := (regChartAt y).chart_source ▸ mem_range_regChartAt y
  chart_mem_atlas y := mem_range_self y

theorem chartAt_regLocus (y : regLocus Y d) :
    chartAt (ComplexModel d) y = (regChartAt y).chart := rfl

private theorem transition_contDiff (D E : RegChart Y d) :
    ContDiffOn ℂ ∞ (D.chart.symm.trans E.chart) (D.chart.symm.trans E.chart).source := by
  let O : Opens (ComplexModel d) :=
    ⟨(D.chart.symm.trans E.chart).source, (D.chart.symm.trans E.chart).open_source⟩
  have hOD : (O : Set (ComplexModel d)) ⊆ D.domain := by
    intro z hz
    exact D.chart_target ▸ hz.1
  let a : O → D.domain := Opens.inclusion hOD
  let A := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) a (contMDiff_inclusion hOD)
  let F := A ≫ D.map
  have := E.openImmersion
  have hRange : range F.base ⊆ range E.map.base := by
    rintro _ ⟨z, rfl⟩
    have hz : D.chart.symm z.val ∈ E.chart.source := z.property.2
    rw [RegChart.chart_source, D.chart_symm z.val (hOD z.property)] at hz
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, congrArg Subtype.val hw⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift E.map F hRange
  have hfac : L ≫ E.map = F := LocallyRingedSpace.IsOpenImmersion.lift_fac E.map F hRange
  have hLp : L ≫ ambientPointMap d E.domain = ambientPointMap d O := by
    rw [← E.overPoint, ← Category.assoc, hfac]
    change (A ≫ D.map) ≫ Y.obj.hom = ambientPointMap d O
    rw [Category.assoc, D.overPoint]
    exact (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel d))
      (IN := 𝓘(ℂ, ComplexModel d)) (IP := 𝓘(ℂ, ComplexModel 0))
      (contMDiff_inclusion hOD) contMDiff_const).symm
  have hSmooth := contMDiff_native_morphism L hLp
  have hPoint (z : O) : (L.base z).val = (D.chart.symm.trans E.chart) z.val := by
    have hi : E.map.base (L.base z) = D.map.base (a z) :=
      congrArg (fun f => f.base z) hfac
    have hp : E.pointMap (L.base z) = D.pointMap (a z) := Subtype.ext hi
    change (L.base z).val = E.chart (D.chart.symm z.val)
    rw [D.chart_symm z.val (hOD z.property)]
    change (L.base z).val = E.chart (D.pointMap (a z))
    rw [← hp, E.chart_pointMap]
  intro z hz
  have hS : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (fun z : O => (D.chart.symm.trans E.chart) z.val) ⟨z, hz⟩ := by
    rw [show (fun z : O => (D.chart.symm.trans E.chart) z.val) =
      (fun z : O => (L.base z).val) from funext (fun z => (hPoint z).symm)]
    exact (contMDiff_subtype_val.comp hSmooth).contMDiffAt
  exact (contMDiffAt_subtype_iff.mp hS).contDiffAt.contDiffWithinAt

instance isManifold_regLocus : IsManifold 𝓘(ℂ, ComplexModel d) ∞ (regLocus Y d) := by
  apply isManifold_of_contDiffOn 𝓘(ℂ, ComplexModel d) ∞ (regLocus Y d)
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa only [mfld_simps] using transition_contDiff (regChartAt x) (regChartAt y)

instance isComplexManifold_regLocus [SecondCountableTopology Y.obj.left] :
    IsComplexManifold d (regLocus Y d) := by
  have : T2Space Y.obj.left := Y.property.1
  exact IsComplexManifold.mk

/-! ### Native morphisms into closed analytic subsets of manifolds -/

section Maps

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M] {C : Set M} {hC : IsComplexAnalyticSubset (n := k) C}

/-- The point map of a native morphism into `(C, 𝒪_M/𝓘_C)`, as a map into `M`. -/
def pointMap (φ : Y ⟶ ofClosedAnalytic C hC) : Y.obj.left → M :=
  fun y => (φ.hom.left.base y).val

theorem continuous_pointMap (φ : Y ⟶ ofClosedAnalytic C hC) : Continuous (pointMap φ) :=
  continuous_subtype_val.comp φ.hom.left.base.hom.continuous

variable (d) in
/-- Its restriction to the regular locus of dimension `d`. -/
def regPointMap (φ : Y ⟶ ofClosedAnalytic C hC) : regLocus Y d → M :=
  fun y => pointMap φ y.val

/-- A regular chart followed by `φ` is holomorphic. -/
theorem contMDiff_pointMap_comp (D : RegChart Y d) (φ : Y ⟶ ofClosedAnalytic C hC) :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
      (fun v : D.domain => pointMap φ (D.map.base v)) := by
  let F : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) D.domain ⟶
      actualSubspaceLocallyRingedSpace (n := k) C := D.map ≫ φ.hom.left
  have hw : φ.hom.left ≫ (ofClosedAnalytic C hC).obj.hom = Y.obj.hom := Over.w φ.hom
  have hF : F ≫ subspacePointMap (n := k) C = ambientPointMap d D.domain := by
    change (D.map ≫ φ.hom.left) ≫ (ofClosedAnalytic C hC).obj.hom = _
    rw [Category.assoc, hw, D.overPoint]
  exact contMDiff_native_source_pointMap F hF

/-- **The restriction of a native morphism to the regular locus is holomorphic.** -/
theorem contMDiff_regPointMap (φ : Y ⟶ ofClosedAnalytic C hC) :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞ (regPointMap d φ) := by
  intro y
  let D := regChartAt y
  have hsrc : y ∈ D.chart.source := mem_chart_source (ComplexModel d) y
  -- the map read through the inverse chart
  have hinv : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
      (regPointMap d φ ∘ D.chart.symm) D.chart.target := by
    intro z hz
    have hzD : z ∈ (D.domain : Set (ComplexModel d)) := D.chart_target ▸ hz
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
        (fun w : D.domain => (regPointMap d φ ∘ D.chart.symm) w.val) ⟨z, hzD⟩ := by
      rw [show (fun w : D.domain => (regPointMap d φ ∘ D.chart.symm) w.val) =
        (fun v : D.domain => pointMap φ (D.map.base v)) from funext fun w => by
          simp only [Function.comp_apply, D.chart_symm w.val w.property]
          rfl]
      exact (contMDiff_pointMap_comp D φ).contMDiffAt
    exact (contMDiffAt_subtype_iff.mp h1).contMDiffWithinAt
  have hchart : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ D.chart D.chart.source :=
    contMDiffOn_chart (x := y)
  have hcomp : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
      ((regPointMap d φ ∘ D.chart.symm) ∘ D.chart) D.chart.source :=
    hinv.comp hchart (fun z hz => D.chart.map_source hz)
  have heq : Set.EqOn ((regPointMap d φ ∘ D.chart.symm) ∘ D.chart) (regPointMap d φ) D.chart.source :=
    fun z hz => by simp only [Function.comp_apply, D.chart.left_inv hz]
  exact ((hcomp.congr fun z hz => (heq hz).symm).contMDiffAt
    (D.chart.open_source.mem_nhds hsrc))

variable (d) in
/-- **The native rank** of `φ` at a regular point of dimension `d`: the rank of the differential of the
holomorphic map `regPointMap d φ` on the manifold `regLocus Y d`. -/
def nativeRankAt [SecondCountableTopology Y.obj.left] (φ : Y ⟶ ofClosedAnalytic C hC)
    (y : regLocus Y d) : ℕ :=
  RankDegeneracy.rankAt (n := d) (n' := k) (regPointMap d φ) univ y

variable (d) in
/-- **The rank-degeneracy set** `S_r(φ) = Sing(Y) ∪ {y ∈ Reg_d(Y) | rank_y φ < r}` (item 5.3). -/
def rankDegeneracy [SecondCountableTopology Y.obj.left] (φ : Y ⟶ ofClosedAnalytic C hC) (r : ℕ) :
    Set Y.obj.left :=
  intrinsicSingularLocus Y.obj ∪ {y | ∃ h : y ∈ regLocus Y d, nativeRankAt d φ ⟨y, h⟩ < r}

end Maps

/-! ### The statements -/

/-- **Remmert's proper mapping theorem for reduced complex spaces** (item 5 of the hF1 route). -/
def NativeProperImage : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X) (P : Set Y.obj.left), Y.IsAnalyticSubset P →
    AnalyticDimensionBasics.ProperOn f.hom.left.base P → X.IsAnalyticSubset (f.hom.left.base '' P)

/-- **The core** (item 5.0): a second-countable native source of bounded native dimension and a proper native
morphism into a closed analytic subset of a complex manifold. -/
def NativeProperImageCore : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left] (m : ℕ),
    HironakaG10EpNativeDim.NativeDimLE Y univ m →
    ∀ (k : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
      [IsComplexManifold k M] (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C)
      (φ : Y ⟶ ofClosedAnalytic C hC), IsProperMap (pointMap φ) →
      IsComplexAnalyticSubset (n := k) (range (pointMap φ))

end

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular
