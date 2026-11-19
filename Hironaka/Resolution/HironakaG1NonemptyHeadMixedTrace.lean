import Hironaka.Resolution.HironakaG1LaterMixedPairedSaturation
import Hironaka.Invariant.ContactEquivalenceStage
import Hironaka.Resolution.HironakaPrincipalization

/-! # Mixed maxima at upper heads with no inherited born incidence -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1NonemptyHeadMixedTrace

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong BoundaryCount
  HomogenizedGlueingTower MemberInterTowerAlong TangentDirectionAlong
  NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaG1LaterPositiveBranchOrder HironakaG1LaterPositiveStratumCentres
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterMixedPairedSaturation

set_option maxHeartbeats 900000 in
/-- A genuine source tangent on the actual tested bar record and the two
endpoint trace identities supply the paired saturation geometry. The
endpoint tangent is obtained along that test, rather than supplied
as another premise. -/
theorem pairedSaturation_of_tested_source_trace {n : ℕ} {X Y Z : CMfd.{0} n}
    (J : MarkedIdeal n X) (R : BlowupTower X Z)
    (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (hR : IsGeoTestTower J R)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d (⊤ : Opens X) u)
    (A : MarkedIdeal n Y) (E : List (Set Y)) (i : Z → Y) (w : Z)
    (hw : w ∈ (geoTransformAlong J R).cosupp) (hy : i w ∈ A.cosupp)
    (hCos : ∀ᶠ x in 𝓝 w, x ∈ (geoTransformAlong J R).cosupp ↔ i x ∈ A.cosupp)
    (hTrace : ∀ᶠ x in 𝓝 w, x ∈ strictAlong R (J.N ∩ {z | u z = 0}) ↔
      i x ∈ A.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D) :
    PairedSaturation (geoTransformAlong J R) A E i w := by
  let B := geoTransformAlong J R
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ R hR
  have hdB : 1 ≤ B.d := (d_geoTransformAlong J R).symm ▸ hd
  obtain ⟨W, hwW, _, v, hv, hNew⟩ := ContactEquivalenceStage.exists_isTangentDirectionAlong_stage
    J hJ.isClosedSubmanifold_N hJ.isCoherent hd ⊤ hu R hR (B.cosupp_subset_N hw) (mem_univ _)
  refine ⟨hB, hdB, hw, hy, W, v, hwW, hv, hCos, ?_⟩
  filter_upwards [W.isOpen.mem_nhds hwW, hTrace] with x hxW hx
  rw [hNew]
  exact ⟨fun h => hx.mp h.1, fun h => ⟨hx.mpr h, hxW⟩⟩

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n+1)}
  (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)

local notation "X₀" => CMfd.of (n := n+1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) P
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))


/-- Tests and endpoint trace identities on the exact masked companion
history. Only a tangent direction at its source is part of the input. -/
def HasTestedPairedSourceTrace (y : Y) (F : LaterPositiveRead Q T y k s) : Prop :=
  let r := regimeRun (stepRegime P (s+1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n+1) O
  let B := CMfd.of (n := n+1) (openPreimage S O)
  let L : MarkedIdeal (n+1) A := lowerMarkedM (X := X₀) P (s+1) H p
  let V : BlowupTower A B := restrict O S
  ∀ hp : p ∈ O,
    let z : openPreimage S O := ⟨y, hp⟩
    let j := regimeRun (OrdRegime L F.order) V z
    let H' := head V j
    let S' := tail V j
    let O' := ordMask (geoTransformAlong L H') F.order
    let J := barMarked (compAt L F.order H')
    ∀ hp' : S'.proj z ∈ O',
      let w : openPreimage S' O' := ⟨z, hp'⟩
      let R := restrict O' S'
      let i : openPreimage S' O' → Y := fun x => x.val.val
      let A := geoTransformAlong (barMarked SEC) T
      J.IsWellFormed ∧ 1 ≤ J.d ∧ IsGeoTestTower J R ∧
      w ∈ (geoTransformAlong J R).cosupp ∧ y ∈ A.cosupp ∧
      ∃ u : O' → ℂ,
        IsTangentDirectionAlong J.N J.ideal J.d univ u ∧
        (∀ᶠ x in 𝓝 w, x ∈ (geoTransformAlong J R).cosupp ↔ i x ∈ A.cosupp) ∧
        (∀ᶠ x in 𝓝 w, x ∈ strictAlong R (J.N ∩ {z | u z = 0}) ↔
          i x ∈ A.N ∧ ∀ D ∈ origMembers SEC T, y ∈ D → i x ∈ D)

set_option maxHeartbeats 1200000 in
/-- The endpoint geometry follows from a tested source tangent and the
actual strict carrier and threshold traces on its suffix. -/
theorem HasTestedPairedSourceTrace.to_paired
    (y : Y) (F : LaterPositiveRead Q T y k s) (h : HasTestedPairedSourceTrace Q T y F) :
    HasPairedSaturation Q T y F := by
  unfold HasPairedSaturation
  intro r H S p O A B L V hp z j H' S' O' J hp' w R
  let i : openPreimage S' O' → Y := fun x => x.val.val
  let K := geoTransformAlong (barMarked SEC) T
  obtain ⟨hJ, hd, hR, hw, hy, u, hu, hCos, hTrace⟩ := h hp hp'
  exact pairedSaturation_of_tested_source_trace (barMarked J) R hJ hd hR u hu
    K (origMembers SEC T) i w hw hy hCos hTrace


/-- The head count is zero exactly when none of the actual strict
transforms of its non-original members meets the endpoint. -/
theorem upperHeadNonOriginalBoundaryCount_eq_zero_iff_off_endpoint (y : Y) :
    upperHeadNonOriginalBoundaryCount Q T s y = 0 ↔
      let r := regimeRun (stepRegime P (s+1)) T y
      let H := head T r
      let B := geoTransformAlong (barMarked P) H
      ∀ D ∈ B.E, D ∉ origMembers P H → y ∉ strictAlong (tail T r) D := by
  classical
  let r := regimeRun (stepRegime P (s+1)) T y
  let H := head T r
  let S := tail T r
  let B := geoTransformAlong (barMarked P) H
  let E := B.E.filter (fun D => decide (D ∉ origMembers P H))
  change boundaryCount (E.map (strictAlong S)) y = 0 ↔
    ∀ D ∈ B.E, D ∉ origMembers P H → y ∉ strictAlong S D
  rw [boundaryCount_map, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h D hD hNew
    have hMem : D ∈ E := List.mem_filter.mpr ⟨hD, decide_eq_true hNew⟩
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hMem
    exact h (Finset.mem_univ j)
  · intro h j _
    obtain ⟨hj, hNew⟩ := List.mem_filter.mp (List.get_mem E j)
    exact h _ hj (of_decide_eq_true hNew)

/-- At a genuine upper head the earlier born divisors may already exist.
If they miss the actual head projection they cannot contribute any
endpoint incidence in the companion. -/
theorem upperHeadNonOriginalBoundaryCount_eq_zero_of_off_head
    (hQ : IsInvDomain (k+1) Q) (y : Y)
    (hOff :
      let r := regimeRun (stepRegime P (s+1)) T y
      let H := head T r
      let B := geoTransformAlong (barMarked P) H
      ∀ D ∈ B.E, D ∉ origMembers P H → (tail T r).proj y ∉ D) :
    upperHeadNonOriginalBoundaryCount Q T s y = 0 := by
  classical
  let r := regimeRun (stepRegime P (s+1)) T y
  let H := head T r
  let S := tail T r
  let B := geoTransformAlong (barMarked P) H
  let E := B.E.filter (fun D => decide (D ∉ origMembers P H))
  have hP := properNormalMarked_isInvDomain Q hQ
  have hClosed₀ : ∀ D ∈ (barMarked (X := X₀) P).E, IsClosed D :=
    hP.isWellFormed.isSNCDivisor.1
  have hClosed : ∀ D ∈ B.E, IsClosed D :=
    HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong (X := X₀)
      (barMarked (X := X₀) P) hClosed₀ H
  change boundaryCount (E.map (strictAlong S)) y = 0
  rw [boundaryCount_map, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro j _
  have hj := List.get_mem E j
  obtain ⟨hJ, hOld⟩ := List.mem_filter.mp hj
  exact fun h => hOff _ hJ (of_decide_eq_true hOld)
    (strictAlong_subset_preimage S (hClosed _ hJ) h)

set_option maxHeartbeats 900000 in
/-- The per-anchor paired saturation criterion yields equality of mixed
maxima when the upper head birth count is zero at each anchor. The
actual heads may be nonempty and need not agree. -/
theorem later_positive_mixed_max_eq_of_zero_head_counts
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T) (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1) (hAttain : (E₀).Nonempty)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (hCounts : ∀ a : S₀, upperHeadNonOriginalBoundaryCount Q T s a.val = 0)
    (hPaired : ∀ a : S₀, HasPairedSaturation Q T a.val (F a)) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  have hZero (a : S₀) : (ofLex (F a).companion).1 = 0 :=
    (laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)).trans (hCounts a)
  have hSpecial (a : S₀) : (ofLex (F a).companion).2 = ⊤ ↔ a ∈ E₀ := by
    have hLev := HironakaG8MemberLoci.level_eq_of_E_eq (A := P) (B := SEC) rfl T a.val
    have hPos : 0 < level SEC T a.val := by
      rw [← hLev, a.property.2]
      exact Nat.succ_pos s
    exact laterPositiveRead_leaf_top_iff_of_paired_saturation Q T a.val (F a)
      (hZero a) hPos (hPaired a)
  exact later_positive_mixed_max_eq_of_boundary_trace Q T hQ hT hCan hMax hSecCan
    hBound hAttain F 0 (fun a ha => ⟨hZero a, (hSpecial a).mpr ha⟩)
    (fun a ha => Or.inr ⟨hZero a, lt_top_iff_ne_top.mpr (fun h => ha ((hSpecial a).mp h))⟩)

set_option maxHeartbeats 950000 in
/-- The mixed maxima agree on actual, possibly nonempty and distinct,
upper heads whose non-original slots miss the endpoints after strict
transform, when
the tested source tangents have the stated strict paired traces. -/
theorem later_positive_mixed_max_eq_of_tested_zero_birth_traces
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T) (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1) (hAttain : (E₀).Nonempty)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (hOffEndpoint : ∀ a : S₀,
      let r := regimeRun (stepRegime P (s+1)) T a.val
      let H := head T r
      let B := geoTransformAlong (barMarked P) H
      ∀ D ∈ B.E, D ∉ origMembers P H → a.val ∉ strictAlong (tail T r) D)
    (hTraces : ∀ a : S₀, HasTestedPairedSourceTrace Q T a.val (F a)) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  exact later_positive_mixed_max_eq_of_zero_head_counts Q T hQ hT hCan hMax hSecCan
    hBound hAttain F hNS
    (fun a => (upperHeadNonOriginalBoundaryCount_eq_zero_iff_off_endpoint Q T a.val).mpr
      (hOffEndpoint a))
    (fun a => HasTestedPairedSourceTrace.to_paired Q T a.val (F a) (hTraces a))


end
end Hironaka.HironakaG1NonemptyHeadMixedTrace
