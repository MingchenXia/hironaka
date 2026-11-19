import Hironaka.Resolution.HironakaG1ActualPrescribedCompanionTrace
import Hironaka.Resolution.HironakaG1ActualLaterOrderRun
import Hironaka.Resolution.HironakaG1LaterMixedUpperBornTrace

/-! # A single actual companion chart for the mixed special comparison -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1MixedOneChartSpecial
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong HomogenizedGlueingTower
  TangentDirectionAlong NonmonomialOrderTail GeneralValue CodimOneSupportAlong
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1PositiveNormalPhase HironakaG1ActualLaterOrderRun
  HironakaG1MixedSelectedThresholdTrace HironakaG1MixedPrescribedSelectedTrace
  HironakaG1ActualPrescribedCompanionTrace HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG1LaterPositiveStratumCentres
  HironakaG1LaterPositiveBranchOrder

set_option maxHeartbeats 1400000 in
/-- The genuine tested selected suffix transports the local source normal
contact. Source window class matching supplies the section threshold on
that contact, and the companion bar changes neither carrier nor tested
cosupport. No endpoint germ assumption is needed. -/
theorem selected_zero_special_iff_of_tested_local_source
    {n k l s o : ℕ} {X Y Z : CMfd.{0} n} (hn : 0 < n)
    (P Sec : MarkedIdeal n X) (hP : IsInvDomain k P) (hSec : IsInvDomain k Sec)
    (hClass : LocWPEquiv P Sec) (hE : P.E = Sec.E) (hN : Sec.N ⊆ P.N)
    (H : BlowupTower X Y) (R : BlowupTower Y Z) (hT : IsGeoTestTower P (H.append R))
    (y : Z) (hLevel : level P (H.append R) y = level P H (R.proj y))
    (hPos : 0 < level Sec (H.append R) y) (hp : R.proj y ∈ maskA P H (R.proj y)) :
    let W := maskA P H (R.proj y)
    let A := CMfd.of (n := n) W
    let L : MarkedIdeal n A := lowerMarkedM (X := X) P (s+1) H (R.proj y)
    let V := restrict W R
    let O : Opens A := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) o
    let J : MarkedIdeal n (CMfd.of (n := n) O) := compAt (X := A) L o .refl
    let S := restrict O V
    let i : openPreimage V O → Z := fun x => x.val.val
    L.IsWellFormed → IsGeoTestTower L V → IsInvDomain l J →
    LocWPEquiv J (MarkedIdeal.pullback (Subtype.val : O → W) L) →
    ∀ w : openPreimage V O, i w = y →
      w ∈ (geoTransformAlong J S).cosupp → level J S w = 0 →
      ∀ (Ω : Opens (CMfd.of (n := n) O)) (u : O → ℂ),
      S.proj w ∈ Ω → IsTangentDirectionAlong J.N J.ideal J.d Ω u →
      (∀ x ∈ J.N, x ∈ Ω →
        (u x = 0 ↔ x.val.val ∈ (geoTransformAlong (barMarked Sec) H).N)) →
      (IsSpecial J S w ↔ IsSpecial Sec (H.append R) y) := by
  intro W A L V O J S i hL hLV hJ hPair w hwy hw hZero Ω u hΩ hu hPrescribed
  let B := geoTransformAlong J S
  let C := geoTransformAlong (barMarked Sec) (H.append R)
  let E := origMembers Sec (H.append R)
  have hS : IsGeoTestTower J S :=
    ((hPair.wEquiv.2 S).1).mpr (isGeoTestTower_restrict (U := O)
      hL.isClosedSubmanifold_N hL.isCoherent V hLV)
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ.isWellFormed S hS
  have hd : 1 ≤ B.d := (d_geoTransformAlong J S).symm ▸ hJ.one_le_d
  have hi : Topology.IsOpenEmbedding i :=
    (openPreimage R W).isOpen.isOpenEmbedding_subtypeVal.comp
      (openPreimage V O).isOpen.isOpenEmbedding_subtypeVal
  have hThreshold (x : openPreimage V O) :
      x ∈ B.cosupp ↔ i x ∈ C.cosupp ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D := by
    rw [hwy]
    exact selected_threshold_of_source_window_class (s := s)
      hn P Sec hP hSec hClass hE H R hT y hLevel hp hLV O J hPair x
  have hSecT : IsGeoTestTower (barMarked Sec) (H.append R) :=
    ((hClass.trans (bar_local_any_boundary Sec hSec)).wEquiv.2 (H.append R)).1.mp hT
  have hLevSec : level Sec (H.append R) y = level Sec H (R.proj y) :=
    (level_eq_of_E_eq hE (H.append R) y).symm.trans
      (hLevel.trans (level_eq_of_E_eq hE H (R.proj y)))
  have hCarrier : J.N = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H (R.proj y) :=
    initial_order_companion_carrier_selected (s := s) (o := o) P H (R.proj y)
  have hTrace : ∀ᶠ x in 𝓝 w, x ∈ strictAlong S (J.N ∩ {z | u z = 0}) ↔
      i x ∈ C.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D := by
    rw [hwy]
    exact local_prescribed_zero_transports_selected_trace P Sec hSec.isWellFormed
      hN hE H R hSecT y hLevSec W O J hCarrier Ω u hPrescribed w hΩ
  obtain ⟨M, hwM, _, g, hg, hgEq⟩ := ContactEquivalenceStage.exists_isTangentDirectionAlong_stage
    J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d Ω hu
      S hS (B.cosupp_subset_N hw) hΩ
  have hContact : ∀ᶠ x in 𝓝 w, x ∈ B.N ∩ {z | g z = 0} ∩ M ↔
      i x ∈ C.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D := by
    filter_upwards [M.isOpen.mem_nhds hwM, hTrace] with x hxM hx
    rw [hgEq]
    exact ⟨fun h => hx.mp h.1, fun h => ⟨hx.mpr h, hxM⟩⟩
  have hLocal := codimOne_iff_member_of_selected_threshold
    B C E i w hi hB hd hw hwM hg hThreshold hContact
  have hBarN : (geoTransformAlong (barMarked J) S).N = B.N := by
    rw [N_geoTransformAlong, show B.N = strictAlong S J.N from N_geoTransformAlong J S]
    rfl
  have hBarCos : (geoTransformAlong (barMarked J) S).cosupp = B.cosupp :=
    (((bar_local_any_boundary J hJ).wEquiv.2 S).2 hS).symm
  have hBar := CodimOnePartCanonical.codimOnePartAlong_congr hBarN hBarCos
  rw [hwy, ← hBar] at hLocal
  have hNo : ¬ (1 ≤ (0 : ℕ)) := by decide
  have hPos' : 1 ≤ level Sec (H.append R) y := hPos
  simpa only [IsSpecial, hZero, true_and, hNo, false_and, or_false, Nat.ne_of_gt hPos,
    false_or, hPos'] using hLocal

set_option maxHeartbeats 2800000 in
/-- At a real positive padded canonical anchor, the source tangent
window, projection into that window, and one-chart special classifier
are obtained on the actual selected suffix. The remaining pair input
is a source window class match, and the companion level must be zero. -/
theorem actual_initial_order_zero_special_iff_of_source_class
    {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s+1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s+1)) T y
    let H := head T r
    let R := tail T r
    let p := R.proj y
    let W := maskA P H p
    let A := CMfd.of (n := n+1) W
    let L : MarkedIdeal (n+1) A := lowerMarkedM (X := X) P (s+1) H p
    let V := restrict W R
    let O : Opens A := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let J : MarkedIdeal (n+1) (CMfd.of (n := n+1) O) := compAt (X := A) L L.d .refl
    let S := restrict O V
    LocWPEquiv (X := CMfd.of (n := n+1) O) J (MarkedIdeal.pullback (Subtype.val : O → W) L) →
    ∀ w : openPreimage V O, w.val.val = y →
      w ∈ (geoTransformAlong J S).cosupp → level J S w = 0 →
      (IsSpecial J S w ↔ IsSpecial Sec T y) := by
  intro X P Sec r H R p W A L V O J S hPair w hwy hw hZero
  obtain ⟨hp, hC, Ω, u, haΩ, hJ, hu, hPrescribed⟩ :=
    exists_actual_initial_companion_prescribed_zero Q hQ T hCan y hy hLevel hNS
  let a : O := ⟨⟨p, hp⟩, hC⟩
  have hProj : S.proj w = a := by
    apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg (fun z : W => z.val) (proj_restrict O V w)
    have h2 := proj_restrict W R w.val
    exact h1.trans (h2.trans (congrArg R.proj hwy))
  have hΩ : S.proj w ∈ Ω := hProj.symm ▸ haΩ
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec₀ : IsInvDomain (k+1) Sec := HironakaActualSectionBoundaryGeometry.section_projected_domain
    (k+1) Q.N Q.E Q.ideal Q.d hQ
  have hSec : IsInvDomain (k+1+1) Sec :=
    ⟨hSec₀.isWellFormed, fun x hx => by
      obtain ⟨j, hj, hreg⟩ := hSec₀.dimLE x hx
      exact ⟨j, Nat.le.step hj, hreg⟩, hSec₀.one_le_d, hSec₀.isNonzeroAlongAt⟩
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarT, hT, hBCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) (k+1)) P hP hMax (Nat.succ_pos n) T hCan
  have hReg := (stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarT
    (hBCos.symm ▸ hy) hNS).1
  rw [hLevel] at hReg
  have hHead : level P H p = s+1 := hReg.1
  have hAppend : H.append R = T := head_append_tail T r
  have hTest : IsGeoTestTower P (H.append R) := hAppend.symm ▸ hT
  have hSame : level P (H.append R) y = level P H p :=
    (hAppend.symm ▸ hLevel).trans hHead.symm
  have hSecE : P.E = Sec.E := rfl
  have hSecN : Sec.N ⊆ P.N := fun _ hx => hx.1
  have hPositive : 0 < level Sec (H.append R) y := by
    rw [hAppend, ← level_eq_of_E_eq hSecE T y, hLevel]
    exact Nat.succ_pos s
  obtain ⟨_, _, _, _, _, _, hL, hCanL, _⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  have hLV := (invFamily (Nat.succ_pos n) (k+1)).isInvValue.isGeoTestTower_of_isCanonical hL V hCanL
  have hLocal : IsSpecial J S w ↔ IsSpecial Sec (H.append R) y :=
    selected_zero_special_iff_of_tested_local_source (n := n+1) (k := k+1+1) (l := k+1)
      (X := X) (Y := (split T r).1) (Z := Y) (s := s) (o := L.d)
      (Nat.succ_pos n) P Sec hP hSec (properNormalMarked_locWPEquiv_section Q hQ) hSecE hSecN
    H R hTest y hSame hPositive hp hL.isWellFormed hLV hJ hPair w hwy hw hZero
    Ω u hΩ hu hPrescribed
  exact hLocal.trans (congrArg (fun K => IsSpecial Sec K y) hAppend).to_iff

section Mixed

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n+1)}
  (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)

local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) P
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))
local notation "countAt" => upperHeadNonOriginalBoundaryCount Q T s


set_option maxHeartbeats 850000 in
/-- Every padded maximum on the highest positive stratum maximizes the
actual surviving upper-head incidence count. Strictly smaller counts are
suppressed regardless of the section branch or of either recursive leaf. -/
theorem later_mixed_padded_max_subset_max_head_count
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val) :
    maxLocus (f T) S₀ ⊆ maxLocus countAt S₀ := by
  intro a ha
  let x : S₀ := ⟨a, ha.1⟩
  refine ⟨ha.1, fun b hb => le_of_not_gt ?_⟩
  intro hlt
  let y : S₀ := ⟨b, hb⟩
  have hx := laterPositiveRead_order_eq_fixed_mark Q T hQ hCan x.val x.property.1
    x.property.2 (hNS x) (F x)
  have hy := laterPositiveRead_order_eq_fixed_mark Q T hQ hCan y.val y.property.1
    y.property.2 (hNS y) (F y)
  have hxCount := laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan
    x.val x.property.1 x.property.2 (hNS x) (F x)
  have hyCount := laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan
    y.val y.property.1 y.property.2 (hNS y) (F y)
  have hLetter : (ofLex (F x).companion).1 < (ofLex (F y).companion).1 := by
    rw [hxCount, hyCount]
    exact hlt
  exact (not_lt_of_ge (ha.2 b hb))
    (LaterPositiveRead.upper_lt_of_companion_level_lt (F x) (F y) (hx.trans hy.symm) hLetter)

set_option maxHeartbeats 950000 in
/-- A discrepancy in the actual surviving upper head incidences already
obstructs mixed maximum agreement in either of the indicated two-anchor
configurations. This needs no comparison of the deeper leaves. -/
theorem later_mixed_max_ne_of_upper_head_birth_mismatch
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    {a b : S₀} (hNSa : ¬ IsSpecial P T a.val) (hNSb : ¬ IsSpecial P T b.val)
    (hb : b ∈ E₀)
    (hMismatch : (a ∈ E₀ ∧ countAt a.val ≠ countAt b.val) ∨
      (a ∉ E₀ ∧ countAt b.val < countAt a.val)) :
    maxLocus (f T) C₀ ≠ maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  have haC := laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan
    a.val a.property.1 a.property.2 hNSa (F a)
  have hbC := laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan
    b.val b.property.1 b.property.2 hNSb (F b)
  apply later_positive_mixed_no_max_eq_of_boundary_mismatch Q T hQ hT hCan hMax hSecCan
    hBound F hb
  rw [haC, hbC]
  exact hMismatch

end Mixed

end
end Hironaka.HironakaG1MixedOneChartSpecial
