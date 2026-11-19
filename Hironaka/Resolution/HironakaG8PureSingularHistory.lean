import Hironaka.Resolution.HironakaG3PureGlobalComponents
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorOriginalRegular
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule

/-! Actual singular-centred histories preserve the dimension of the dense
pure regular locus. A smoothed strict carrier thus has that same dimension. -/

set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8PureSingularHistory

open Hironaka.BlowupSequences BlowupTowers
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG3PureGlobalComponents
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular

/-- The pure regular locus remains dense in the literal strict transform
of any actual history with intrinsically singular centres. -/
theorem dense_pure_regular_of_singular_history {n d : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d)) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    let A := strictTransform n T.proj W
    A ⊆ closure (regularLocus (n := n) A d) := by
  let A := strictTransform n T.proj W
  let G := singularSet (n := n) W
  have hGood : W ⊆ closure (W \ G) := hPure.trans (closure_mono (fun y hy =>
    ⟨hy.2.1, fun hs => (mem_singularSet_iff.mp hs).2 d hy⟩))
  have hIso := (actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)).2.1
  have hDense := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff
    T.contMDiff_proj hW.isClosed hGood
  refine hDense.trans (closure_mono ?_)
  intro y hy
  have hyW := HironakaAdmissibleCalculus.strictTransform_subset_preimage
    T.contMDiff_proj.continuous hW.isClosed hy.1
  have hyNonExc : y ∉ exceptionalLocus n T.proj :=
    fun he => Set.disjoint_left.mp hIso.2 hy.2 he
  have hyReg : ∃ k, RegularAtDim (n := n) W (T.proj y) k := by
    by_contra h
    exact hy.2 (mem_singularSet_iff.mpr ⟨hyW, fun k hk => h ⟨k, hk⟩⟩)
  obtain ⟨k, hk⟩ := hyReg
  have hd := regular_dimension_of_dense_pure W hPure hk
  exact (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus
    T.contMDiff_proj hW.isClosed hyNonExc d).mpr (hd ▸ hk)

/-- A smooth strict transform after actual singular-centred blowups is
regular of the original pure dimension at every point. -/
theorem pure_dim_of_smooth_singular_history {n d : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d)) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W)) :
    ∀ y ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) y d := by
  intro y hy
  obtain ⟨k, hk⟩ := hSmooth.2 y hy
  exact (regular_dimension_of_dense_pure _ (dense_pure_regular_of_singular_history hW hPure T hStage) hk) ▸ hk

end Hironaka.HironakaG8PureSingularHistory
