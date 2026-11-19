import Hironaka.Resolution.HironakaActualHSSingularBlowupRestart
import Hironaka.Resolution.HironakaActualLimitCarrierGeometry

/-!
# Pure dimension of actual centre-relative strict transforms

Only original analyticity and actual pure dimension are inputs. Every genuine
smooth blowup is allowed; components contained in its centre may disappear.
The limit is the independently defined actual strict-transform intersection.
Blueprint: `hironaka-actual-pure-strict-transforms.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualPureStrictTransforms

noncomputable section

open Hironaka.BlowupSequences AnalyticDimensionBasics
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  HironakaActualHSSingularBlowupRestart HironakaLocallyFiniteResolutionSequence
  ResolutionInvariantSeq HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry

attribute [local instance] limitChartedSpace

variable {n : ℕ}

local instance {X : CMfd.{u} n} (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) :=
  limitSpace_isComplexManifold s hLF

/-- The literal centre-relative strict transform retains actual pure dimension
under EVERY genuine smooth blowup, allowing contained components to disappear. -/
theorem isPureDim_geoStrictTransform
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {B C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hB : IsComplexAnalyticSubset (n := n) B) {q : ℕ}
    (hpure : IsPureDim (n := n) B q) :
    IsPureDim (n := n) (geoStrictTransform π C B) q := by
  have hdense := actualPure_subset_closure_regularLocus hB hpure
  apply actualPure_of_subset_closure_regularLocus
  apply closure_minimal _ isClosed_closure
  rintro z ⟨hzB, hzC⟩
  have hzE : z ∉ exceptionalLocus n π := fun hz =>
    hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz)
  rw [mem_closure_iff_nhds]
  intro N hN
  have hN' : N ∩ π ⁻¹' Cᶜ ∈ 𝓝 z :=
    inter_mem hN ((hπ.1.1.preimage hπ.contMDiff.continuous).isOpen_compl.mem_nhds hzC)
  have himage : π '' (N ∩ π ⁻¹' Cᶜ) ∈ 𝓝 (π z) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hπ.contMDiff hzE]
    exact image_mem_map hN'
  obtain ⟨_, ⟨y, ⟨hyN, hyC⟩, rfl⟩, hyreg⟩ :=
    mem_closure_iff_nhds.mp (hdense hzB) _ himage
  exact ⟨y, hyN, regularAtDim_geoStrictTransform_of_notMem hπ hB.isClosed hyC hyreg⟩

/-- Every actual finite centre-relative history preserves the initial analytic
carrier's pure dimension. No centre-avoidance or admissibility certificate is input. -/
theorem isPureDim_strictAlong {X : CMfd.{u} n} {B : Set X}
    (hB : IsComplexAnalyticSubset (n := n) B) {q : ℕ}
    (hpure : IsPureDim (n := n) B q) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsPureDim (n := n) (strictAlong T B) q := by
  intro Y T
  induction T with
  | refl => exact hpure
  | @step Y Z T C π hπ ih =>
    exact isPureDim_geoStrictTransform hπ (isComplexAnalyticSubset_strictAlong hB T) ih

/-- Pure dimension holds on the independently defined true locally finite
limit carrier, by its actual stable-prefix regularity dictionary. -/
theorem isPureDim_limitStrictTransform {X : CMfd.{u} n}
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B) {q : ℕ}
    (hpure : IsPureDim (n := n) B q) :
    IsPureDim (n := n) (limitStrictTransform s hLF B) q := by
  intro z j hz
  obtain ⟨x, y, rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  exact isPureDim_strictAlong hB hpure (s.stage (stableIndex s hLF x)).2 y.val j
    ((regularAtDim_limitStrictTransform_local_iff s hLF hB.isClosed x y j).mp hz)

end
end Hironaka.HironakaActualPureStrictTransforms
