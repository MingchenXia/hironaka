import Hironaka.Resolution.HironakaG8BornBoundaryNoncontainment
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaResolutionSpace

/-! With a dense complement of the initial divisor in the analytic carrier,
every actual full-boundary singular prefix supports a fresh native phase. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8DenseBoundaryRestart

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence
  RestrictEmptyTower HironakaG8IntrinsicSingularBlockSchedule HironakaG8BornBoundaryNoncontainment

/-- When the initial boundary has dense complement in the carrier,
original regular points away from the boundary are also dense there. -/
theorem dense_off_original_boundary_and_singular
    {n : ℕ} {X : CMfd.{0} n} {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {B : Set X} (hClosed : IsClosed B) (hDense : W ⊆ closure (W \ B)) :
    W ⊆ closure (W \ (B ∪ singularSet (n := n) W)) := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨y, hyU, hyW, hyB⟩ := mem_closure_iff.mp (hDense hx) U hU hxU
  have hWS := HironakaResolutionSpace.subset_closure_diff_singularSet hW
  obtain ⟨z, ⟨hzU, hzB⟩, hzW, hzS⟩ :=
    mem_closure_iff.mp (hWS hyW) (U ∩ Bᶜ) (hU.inter hClosed.isOpen_compl) ⟨hyU, hyB⟩
  exact ⟨z, hzU, hzW, fun h => h.elim hzB hzS⟩

/-- If the initial carrier is the closure of its complement of the original
boundary, the same is true of the current carrier and full accumulated
boundary along any original singular-centred test. -/
theorem strict_transform_dense_off_accumulated_boundary
    {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj W)) T) :
    let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
    let A := strictTransform n T.proj W
    A ⊆ closure (A \ ⋃ H ∈ (geoTransformAlong M T).E, H) := by
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  let S := singularSet (n := n) W
  let O : Opens X := ⟨Sᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hOver : CentresOver S T := by
    simpa [O] using centresOver_compl_of_centresAvoid O T
      (intrinsic_singular_history_avoids_regular_open hW O disjoint_compl_right T hStage)
  have hAdm := isAdmissibleBlowupSequence_proj M S T hTest hOver
  have hBound := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hAdm hE.1
  have hJoint := dense_off_original_boundary_and_singular hW
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE.1) hDense
  have hLift := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff
    T.contMDiff_proj hW.isClosed hJoint
  exact hLift.trans (closure_mono (fun _ hy => ⟨hy.1, fun h => hy.2 (hBound h)⟩))

/-- Dense initial complement derives the needed incident noncontainment
from the literal history, including inherited and born members. -/
theorem boundary_noncontainment_at_current_singular_of_dense_complement
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj W)) T) :
    let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
    let A := strictTransform n T.proj W
    ∀ B ∈ (geoTransformAlong M T).E, ∀ x ∈ singularSet (n := n) A, x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A := by
  let M : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  let A := strictTransform n T.proj W
  let F := (geoTransformAlong M T).E
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hF : IsSNCDivisor n F :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTest).isSNCDivisor
  have hA : IsComplexAnalyticSubset (n := n) A :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense T hTest hStage
  change ∀ B ∈ F, ∀ x ∈ singularSet (n := n) A, x ∈ B → ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A
  intro B hB x hx hxB
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
  have hBsm := hi ▸ MonomialPart.isClosedSubmanifold_get hn hF i
  have hBInv := hi ▸ HironakaNormalCrossingsFiniteMarkedCompletion.isInvertible_vanishingIdeal_snc_member hF i
  have hBsub : B ⊆ ⋃ H ∈ F, H := fun y hy => mem_iUnion₂.mpr ⟨B, hB, hy⟩
  have hAvoid : A ⊆ closure (A \ B) :=
    hADense.trans (closure_mono (sdiff_subset_sdiff_right hBsub))
  have hNZ := isNonzeroAlongAt_vanishingIdeal_of_singular hA hx
  have hZero := HironakaActualStrictDivisorZeroExponent.vanishingIdeal_divExpAlong_eq_zero
    (CartanIrreducible.cartanCoherence A hA) hBsm hBInv hAvoid x hNZ
  exact boundary_germ_noncontainment_of_zero_reduced_exponent hxB hNZ hZero

end Hironaka.HironakaG8DenseBoundaryRestart
