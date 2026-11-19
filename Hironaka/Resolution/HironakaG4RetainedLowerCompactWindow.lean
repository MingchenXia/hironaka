import Hironaka.Resolution.HironakaActualRetainedBornResidualSeed
import Hironaka.Resolution.HironakaCanonicalSharpBadHistoryFullGeometry
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumLocalDriver

/-! The defect-free retained tuple supplies the actual lower native marked
problem and its whole-boundary canonical history near any compact enclosure. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedLowerCompactWindow

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerSplit BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaG4PreparedCentreCoordinates HironakaG4ResidualInductionInputs
  HironakaActualRetainedBornResidualSeed HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaActualSharpBadMaximumProcessedSlice HironakaCanonicalSharpBadHistoryFullGeometry
  HironakaOriginalNCMarkedStratumLocalDriver HironakaOriginalNCMarkedStratumHistoryValue
  HironakaOriginalNCOldStratumStrictEquality
  HironakaSharpActualFiniteChronologicalHistory RestrictEmptyTower
  HironakaOriginalOldBranchOpenHistory HironakaAdmissibleSequence
  CoefficientIdealRestriction HironakaG4OriginalSelectedLowerBoundaryHistory RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X : CMfd.{u} n}

/-- The true zero defect gives order at most one and exclusion of a shared
proper germ for the same retained residual ideals. -/
theorem retained_row_conditions_of_empty_distinct_defect (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅) :
    (∀ x ∈ N, ∀ j, ordinaryTraceOrder N (oldResidualPart N old born j) x ≤ 1) ∧
    ∀ x ∈ N, ∀ i j : Fin old.length, i ≠ j →
      ¬(oldResidualPart N old born i).mem x 1 → ¬(oldResidualPart N old born j).mem x 1 →
      ¬∀ g, (oldResidualPart N old born i).mem x g ↔ (oldResidualPart N old born j).mem x g := by
  classical
  let J := oldResidualPart N old born
  have hRows := retainedResidualMarked_geometry hn hN hFull hTr hDense
  have hNo (x : X) : x ∉ actualFamilyDistinctDefect N J :=
    fun h => (show x ∈ (∅ : Set X) from hEmpty ▸ h).elim
  have hWitness (x : X) (hx : x ∈ N) :=
    actual_distinct_defect_iff_witness hN (fun i => (hRows i).1.isCoherent)
      (fun i => (hRows i).2.1) (fun i => (hRows i).2.2) hx
  refine ⟨?_, ?_⟩
  · intro x hx j
    apply Nat.le_of_not_gt
    intro hj
    exact hNo x ((hWitness x hx).mpr (Or.inl ⟨j, hj⟩))
  · intro x hx i j hne hi hj hEqual
    have hi' : i ∈ actualProperPositions J x := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hj' : j ∈ actualProperPositions J x := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    exact hNo x ((hWitness x hx).mpr (Or.inr ⟨i, j, hne, hi', hj', hEqual⟩))

/-- Recover the actual upper tests and support for a canonical lower
history on a literal open. The same readback applies to single steps
and to terminal native histories. -/
theorem retained_lower_canonical_geometry {N L B : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (j : Fin old.length) (hLN : L ⊆ N) (hOwn : L ⊆ old.get j)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hMN : M.N = L) (hME : M.E = [])
    (hCos : M.cosupp = B) (U : Opens X) {Y : CMfd.{u} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hCan : let v := (Subtype.val : U → X)
      let MU := MarkedIdeal.pullback v M
      IsCanonical MU
        (markedStratumHistoryValue MU (v ⁻¹' (⋃ D ∈ old.eraseIdx j.val ++ born, D))) T) :
    let v := (Subtype.val : U → X)
    let MU := MarkedIdeal.pullback v M
    let oldU := old.map (v ⁻¹' ·)
    let bornU := born.map (v ⁻¹' ·)
    IsOriginalBranchTestTower MU (v ⁻¹' (⋃ D ∈ old.eraseIdx j.val ++ born, D)) T ∧
      IsGeoTestTower (geometricTemplate (v ⁻¹' N) bornU) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (oldU ++ bornU)) T ∧
      CentresOver (v ⁻¹' B) T ∧
      ∀ r : ℕ, IsSNCDivisor n
        ((oldU ++ bornU).map (strictAlong (head T r)) ++ (geoTransformAlong MU (head T r)).E) := by
  let F := old.eraseIdx j.val ++ born
  let H := ⋃ D ∈ F, D
  let XU := CMfd.of (n := n) U
  let v := (Subtype.val : U → X)
  let MU := MarkedIdeal.pullback v M
  let oldU := old.map (v ⁻¹' ·)
  let bornU := born.map (v ⁻¹' ·)
  let jU : Fin oldU.length := Fin.cast (List.length_map _).symm j
  have hjU : oldU.get jU = v ⁻¹' old.get j := by simp [oldU, jU]
  have hFU : oldU.eraseIdx jU.val ++ bornU = F.map (v ⁻¹' ·) := by
    simp [F, oldU, bornU, jU, List.map_append, List.eraseIdx_map]
  have hHU : v ⁻¹' H = ⋃ D ∈ oldU.eraseIdx jU.val ++ bornU, D := by
    rw [hFU]
    ext x
    simp [H]
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hFull
  have hMU : IsInvDomain n MU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hCan' : IsCanonical MU
      (markedStratumHistoryValue MU (⋃ D ∈ oldU.eraseIdx jU.val ++ bornU, D)) T := by
    rw [← hHU]
    exact hCan
  have hOwnU : MU.N ⊆ oldU.get jU := by
    rw [hjU]
    change v ⁻¹' M.N ⊆ _
    rw [hMN]
    exact preimage_mono hOwn
  have hMEU : MU.E = [] := by
    change M.E.map (v ⁻¹' ·) = []
    rw [hME,List.map_nil]
  obtain ⟨hTest, hBranch, hWhole, hSNC⟩ := canonical_empty_native_history_full_geometry
    (X := XU) MU hMU hMEU oldU bornU hFullU jU hOwnU T hCan'
  rw [← hHU] at hBranch
  have hCosU : MU.cosupp = v ⁻¹' B := by
    change (MarkedIdeal.pullback v M).cosupp = v ⁻¹' B
    rw [cosupp_pullback_val M
      (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent h) U, hCos]
  have hOver := centresOver_cosupp MU hMU.isWellFormed.isClosedSubmanifold_N
    hMU.isWellFormed.isCoherent T hTest
  rw [hCosU] at hOver
  have hCentres : CentresIn (v ⁻¹' L) T := by
    have hCN := centresIn_of_isGeoTestTower_withN (X := XU) MU MU.N T hTest
    change CentresIn (v ⁻¹' M.N) T at hCN
    rwa [hMN] at hCN
  have hLTest : IsGeoTestTower (geometricTemplate (v ⁻¹' L) (oldU ++ bornU)) T :=
    (restrict_tower (boundaryGeometry (X := XU) (oldU ++ bornU)) rfl
      IdealWeightPowers.isCoherent_unitIdeal (S := v ⁻¹' L)
      (show IsClosedSubmanifold n (v ⁻¹' L) from by
        rw [← hMN]; exact hMU.isWellFormed.isClosedSubmanifold_N) T hWhole hCentres).1
  let G := geometricTemplate (X := XU) (v ⁻¹' N) bornU
  have hG : G.IsWellFormed :=
    ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U, IdealWeightPowers.isCoherent_unitIdeal,
      isSNCDivisor_of_sublist hFullU (List.sublist_append_right oldU bornU),
      isTransverse_preimage (pullsBackCoordinates_val U) hTr⟩
  have hUpper : IsGeoTestTower G T :=
    (actual_zero_mark_test_of_lower_test G hG rfl (preimage_mono hLN)
      (List.sublist_append_right oldU bornU) T hLTest).1
  exact ⟨hBranch, hUpper, hWhole, hOver, hSNC⟩

/-- A finite canonical lower history over an arbitrary compact enclosure.
The entire upper boundary is tested by this same tower, including the
omitted selected old divisor, and its centres lie over the literal lower
sharp bad locus, which is contained in the upper sharp bad locus. -/
theorem exists_retained_lower_canonical_window_on_compact (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (j : Fin old.length) {K : Set X} (hK : IsCompact K) :
    let L := N ∩ (oldResidualPart N old born j).zeroLocus
    let F := old.eraseIdx j.val ++ born
    let B := originalSharpBadLocus (n := n) L F
    let M : MarkedIdeal n X := ⟨L, [], vanishingIdeal (n := n) B, 1⟩
    B ⊆ originalSharpBadLocus (n := n) N (old ++ born) ∧
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let v := (Subtype.val : U → X)
      let MU := MarkedIdeal.pullback v M
      let HU := v ⁻¹' (⋃ D ∈ F, D)
      let oldU := old.map (v ⁻¹' ·)
      let bornU := born.map (v ⁻¹' ·)
      IsGeoResolution MU T ∧ IsCanonical MU (markedStratumHistoryValue MU HU) T ∧
      IsOriginalBranchTestTower MU HU T ∧ IsGeoTestTower (geometricTemplate (v ⁻¹' N) bornU) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (oldU ++ bornU)) T ∧
      CentresOver (v ⁻¹' B) T ∧
      ∀ r : ℕ, IsSNCDivisor n
        ((oldU ++ bornU).map (strictAlong (head T r)) ++ (geoTransformAlong MU (head T r)).E) := by
  let L := N ∩ (oldResidualPart N old born j).zeroLocus
  let F := old.eraseIdx j.val ++ born
  let B := originalSharpBadLocus (n := n) L F
  let M : MarkedIdeal n X := ⟨L, [], vanishingIdeal (n := n) B, 1⟩
  let H := ⋃ D ∈ F, D
  obtain ⟨hOrd, hDistinct⟩ := retained_row_conditions_of_empty_distinct_defect hn hN hFull hTr hDense hEmpty
  obtain ⟨_, _, hOwn, _, _, hM, hCos, hH⟩ :=
    sharp_bad_native_domain_of_retained_rows hn hN hFull hTr hDense hOrd hDistinct j
  have hBad : B ⊆ originalSharpBadLocus (n := n) N (old ++ born) :=
    originalSharpBadLocus_residual_subset hn hN hFull hTr hDense j
  obtain ⟨U, hKU, Y, T, hRes, hCan, _, _⟩ :=
    exists_markedStratum_local_canonical_resolving_tower M hM hH K hK
  obtain ⟨hBranch, hUpper, hWhole, hOver, hSNC⟩ :=
    retained_lower_canonical_geometry hN hFull hTr j (L := L) inter_subset_left hOwn
      M hM rfl rfl hCos U T hCan
  exact ⟨hBad, U, hKU, Y, T, hRes, hCan, hBranch, hUpper, hWhole, hOver, hSNC⟩

end
end Hironaka.HironakaG4RetainedLowerCompactWindow
