import Hironaka.Resolution.HironakaG8CountablePlaneArrangement
import Hironaka.Resolution.HironakaG8NativePhaseOccupiedFibre

/-! # Failure of an attained global native maximum on the plane sheets -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NoGlobalPlaneProfile

open Hironaka.HolomorphicIdealSheaves BlowupTowers HironakaEmbeddedAnalytic BlowupTowerTransforms
  HironakaG8CountablePlaneSheets HironakaG8CountablePlaneArrangement
  HironakaHolomorphicJetChartInvariance HironakaG8NativePhaseCertificate
  HironakaG8NativePhaseOccupiedFibre HironakaG8StageRankCoherence
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8ClosedNativeTestGlobalization HironakaG3CentresOverGenericFactor
  HironakaAdmissibleSequence RestrictEmptyTower

local notation "A" => countablePlaneArrangement
local notation "HS" => hilbertSamuelAt (vanishingIdeal (n := 2) A)

/-- Every actual singular origin is exceeded by the next sheet. -/
theorem exists_larger_singular_plane_profile (x : PlaneSheets)
    (hx : x ∈ singularSet (n := 2) A) :
    ∃ y ∈ singularSet (n := 2) A, toLex (HS x) < toLex (HS y) := by
  rcases x with ⟨i,x⟩
  have hx0 : x = 0 := by
    rw [countablePlaneArrangement_singularSet] at hx
    exact hx
  subst x
  refine ⟨(i+1,0),?_,?_⟩
  · rw [countablePlaneArrangement_singularSet]
    rfl
  · exact countablePlaneArrangement_origin_profile_strictMono (Nat.lt_succ_self i)

/-- The whole singular locus has no attained Hilbert–Samuel maximum. -/
theorem no_attained_maximum_on_countable_plane_arrangement :
    ¬ ∃ x ∈ singularSet (n := 2) A,
      ∀ y ∈ singularSet (n := 2) A, toLex (HS y) ≤ toLex (HS x) := by
  rintro ⟨x,hx,hMax⟩
  obtain ⟨y,hy,hlt⟩ := exists_larger_singular_plane_profile x hx
  exact (not_le_of_gt hlt) (hMax y hy)

set_option maxHeartbeats 700000 in
/-- A native phase bounded above by its own label on the entire original
singular locus has no occupied projected centre on this analytic example. -/
theorem unoccupied_whole_maximal_native_phase
    {Y : CMfd.{0} 2} {E : List (Set sheetManifold)} {H : ℕ → ℕ}
    {T : BlowupTower sheetManifold Y}
    (hPhase : ActualNativePhase A E H T)
    (hUpper : ∀ x ∈ singularSet (n := 2) A, toLex (HS x) ≤ toLex H) :
    baseCentreFootprint T = ∅ := by
  let V : Opens sheetManifold := ⟨(singularSet (n := 2) A)ᶜ,
    (isClosed_singularSet isComplexAnalyticSubset_countablePlaneArrangement.isClosed).isOpen_compl⟩
  have hAvoid : CentresAvoid V T :=
    (actual_singular_history_original_regular_protection A
      isComplexAnalyticSubset_countablePlaneArrangement T
      (intrinsic_stage_native_history (X := sheetManifold) A T hPhase.singular)).1
  have hSing : baseCentreFootprint T ⊆ singularSet (n := 2) A := by
    have hSub := (centresOver_iff_baseCentreFootprint_subset T).mp
      (centresOver_compl_of_centresAvoid V T hAvoid)
    change baseCentreFootprint T ⊆ (singularSet (n := 2) A)ᶜᶜ at hSub
    rwa [compl_compl] at hSub
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hX := hSing hx
  obtain ⟨y,hy,hlt⟩ := exists_larger_singular_plane_profile x hX
  have hEq := (centresOver_iff_baseCentreFootprint_subset T).mp hPhase.supports hx
  change HS x = H at hEq
  rw [← hEq] at hUpper
  exact (not_le_of_gt hlt) (hUpper y hy)

end Hironaka.HironakaG8NoGlobalPlaneProfile
