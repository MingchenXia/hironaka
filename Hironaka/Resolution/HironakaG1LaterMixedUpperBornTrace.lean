import Hironaka.Resolution.HironakaG1LaterMixedCentreBoundaryTrace
import Hironaka.Resolution.HironakaG1ActualLaterOrderRun

/-! # Which upper members count in a canonical later positive companion -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Classical

namespace Hironaka.HironakaG1LaterMixedUpperBornTrace

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneEmptyPrefix HomogenizedIdealAlong BoundaryCount
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  GeneralValue HomogenizedGlueingTower MemberInterTowerAlong InvDomainRebase
  InvDomainMemberRestriction MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1LaterPositiveSuccessorRead
  HironakaG1ActualLaterSuccessorRead HironakaG1ActualLaterOrderRun
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG1InitialPositiveGeneralRead

private theorem boundaryCount_eq_filter_length {M : Type*} [TopologicalSpace M]
    (E : List (Set M)) (x : M) : boundaryCount E x = (E.filter fun W => decide (x ∈ W)).length := by
  classical
  have hc : boundaryCount E x = (List.finRange E.length).countP (fun i => decide (x ∈ E.get i)) := by
    simpa only [boundaryCount, List.toFinset_finRange] using
      (List.nodup_finRange E.length).card_eq_countP (P := fun i => x ∈ E.get i)
  calc
    _ = ((List.finRange E.length).filter fun i => decide (x ∈ E.get i)).length := by
      rw [hc, List.countP_eq_length_filter]
    _ = (((List.finRange E.length).map E.get).filter fun W => decide (x ∈ W)).length := by
      rw [List.filter_map, List.length_map]
      rfl
    _ = _ := by rw [List.map_get_finRange]

private theorem boundaryCount_restricted_strictAlong {d : ℕ} {X Z : CMfd.{0} d}
    (O : Opens X) (R : BlowupTower X Z) (E : List (Set X)) (z : openPreimage R O) :
    boundaryCount ((E.map ((Subtype.val : O → X) ⁻¹' ·)).map (strictAlong (restrict O R))) z =
      boundaryCount (E.map (strictAlong R)) z.val := by
  rw [List.map_map]
  have hLists : E.map (strictAlong (restrict O R) ∘ ((Subtype.val : O → X) ⁻¹' ·)) =
      E.map (((Subtype.val : openPreimage R O → Z) ⁻¹' ·) ∘ strictAlong R) := by
    apply List.map_congr_left
    intro D _
    exact strictAlong_restrict O R D
  rw [hLists, ← List.map_map]
  exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ _

private theorem retained_nonoriginal_count {d : ℕ} {X Z : CMfd.{0} d}
    (R : BlowupTower X Z) (E E₀ : List (Set X)) (z : Z) (hE : ∀ D ∈ E, IsClosed D) :
    let p := R.proj z
    let L := E.filter (fun D => decide ¬ (D ∈ E₀ ∧ p ∈ D))
    let B := E.filter (fun D => decide (D ∉ E₀))
    boundaryCount (L.map (strictAlong R)) z = boundaryCount (B.map (strictAlong R)) z := by
  classical
  intro p L B
  rw [boundaryCount_eq_filter_length, boundaryCount_eq_filter_length]
  simp only [L, B, List.filter_map, List.length_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro D hD
  by_cases hz : z ∈ strictAlong R D
  · have hp : p ∈ D := strictAlong_subset_preimage R (hE D hD) hz
    simp [hz, hp, p]
  · simp [hz]

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)}
  (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))

/-- Count the strict transforms of non-original upper members already
present at the actual start of the positive nonspecial upper run. -/
def upperHeadNonOriginalBoundaryCount (s : ℕ) (y : Y) : ℕ :=
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong (barMarked P) H
  boundaryCount ((A.E.filter (fun D => decide (D ∉ origMembers P H))).map (strictAlong S)) y

set_option maxHeartbeats 2600000 in
/-- The actual companion level forgets both open masks and all original
upper members. It counts only non-original upper members already present
at the start of the actual selected run and incident after its suffix. -/
theorem laterPositiveRead_companion_level_eq_upperHeadNonOriginal
    (hQ : IsInvDomain (k + 1) Q) (hCan : IsCanonical P f T)
    (y : Y) (hy : y ∈ C₀) (hLevel : level P T y = s + 1)
    (hNS : ¬ IsSpecial P T y) (F : LaterPositiveRead Q T y k s) :
    (ofLex F.companion).1 = upperHeadNonOriginalBoundaryCount Q T s y := by
  classical
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n + 1) O
  let Z := CMfd.of (n := n + 1) (openPreimage S O)
  let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
  let R : BlowupTower A Z := restrict O S
  let K := geoTransformAlong (barMarked P) H
  obtain ⟨hp, _, hE, hp', _, _, _, _, hv⟩ :=
    original_upper_positive_successor_at_initial_order_companion Q hQ T hCan y hy hLevel hNS
  let z : openPreimage S O := ⟨y, hp⟩
  let O' := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
  let J := compAt L L.d (.refl : BlowupTower A A)
  let R' := restrict O' R
  let w : openPreimage R O' := ⟨z, hp'⟩
  let val := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) J R' w
  have hRaw : f T y =
      toLex (s + 1, (positiveSuccessorRead L.d val : WithTop (ValTy (k + 1)))) := hv
  have hCode : positiveSuccessorRead F.order F.companion = positiveSuccessorRead L.d val :=
    WithTop.coe_inj.mp (congrArg (fun t : ℕ ×ₗ WithTop (ValTy (k + 1)) => (ofLex t).2)
      (F.raw_upper.symm.trans hRaw))
  have hc := congrArg (fun a : ValTy (k + 1) => ofLex ((ofLex a).2)) hCode
  have hc' : Sum.inr (F.companion : WithTop (ℕ ×ₗ WithTop (ValTy k))) =
      Sum.inr (val : WithTop (ℕ ×ₗ WithTop (ValTy k))) := hc
  have hComp : F.companion = val := WithTop.coe_inj.mp (Sum.inr.inj hc')
  have hFirst : (ofLex val).1 = level J R' w :=
    Seq.StepOneValueMasked.stepOneInvL_fst (invFamily (Nat.succ_pos n) k) J (lowerMarkedM J) R' w
  have hMembers : origMembers J R' = J.E.map (strictAlong R') := by
    change (geoTransformAlong (barMarked J) R').E.take J.E.length = _
    exact take_E_geoTransformAlong (barMarked J) R'
  have hJCount : boundaryCount (J.E.map (strictAlong R')) w =
      boundaryCount (L.E.map (strictAlong R)) z := by
    change J.E = L.E.map ((Subtype.val : O' → A) ⁻¹' ·) at hE
    rw [hE]
    exact boundaryCount_restricted_strictAlong O' R L.E w
  let L₀ := K.E.filter (fun D => decide ¬ (D ∈ origMembers P H ∧ p ∈ D))
  have hLE : L.E = L₀.map ((Subtype.val : O → _) ⁻¹' ·) := by
    change (memberRestrict K (membersThrough K.E (origMembers P H) p)).E.map
      ((Subtype.val : O → _) ⁻¹' ·) = _
    rw [memberRestrict_membersThrough_E]
  have hLCount : boundaryCount (L.E.map (strictAlong R)) z =
      boundaryCount (L₀.map (strictAlong S)) y := by
    rw [hLE]
    exact boundaryCount_restricted_strictAlong O S L₀ z
  have hP := properNormalMarked_isInvDomain Q hQ
  have hClosed₀ : ∀ D ∈ (barMarked (X := X₀) P).E, IsClosed D :=
    hP.isWellFormed.isSNCDivisor.1
  have hClosed : ∀ D ∈ K.E, IsClosed D :=
    HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong (X := X₀)
      (barMarked (X := X₀) P) hClosed₀ H
  calc
    (ofLex F.companion).1 = level J R' w :=
      (congrArg (fun u : ℕ ×ₗ WithTop (ValTy k) => (ofLex u).1) hComp).trans hFirst
    _ = boundaryCount (J.E.map (strictAlong R')) w :=
      congrArg (fun E => boundaryCount E w) hMembers
    _ = boundaryCount (L.E.map (strictAlong R)) z := hJCount
    _ = boundaryCount (L₀.map (strictAlong S)) y := hLCount
    _ = upperHeadNonOriginalBoundaryCount Q T s y :=
      retained_nonoriginal_count S K.E (origMembers P H) y hClosed

/-- A later endpoint whose positive upper run starts at the original
source has no retained non-original incidence in its padded companion. -/
theorem upperHeadNonOriginalBoundaryCount_eq_zero_of_full_run (y : Y)
    (hRun : regimeRun (stepRegime P (s + 1)) T y = T.length) :
    upperHeadNonOriginalBoundaryCount Q T s y = 0 := by
  let count (A : Σ M : CMfd.{0} (n +1), BlowupTower X₀ M × BlowupTower M Y) :=
    let K := geoTransformAlong (barMarked P) A.2.1
    boundaryCount ((K.E.filter (fun D => decide (D ∉ origMembers P A.2.1))).map
      (strictAlong A.2.2)) y
  change count (split T (regimeRun (stepRegime P (s + 1)) T y)) = 0
  rw [hRun, split_of_length_le T T.length le_rfl]
  have hE : (barMarked (X := X₀) P).E = (P).E := rfl
  have hOld : origMembers P (.refl (X := X₀)) = (P).E := by
    rw [origMembers, geoTransformAlong_refl, hE, List.take_length]
  change boundaryCount ((((barMarked (X := X₀) P).E).filter
    (fun D => decide (D ∉ origMembers P (.refl (X := X₀))))).map (strictAlong T)) y = 0
  rw [hE, hOld]
  have hNone : (P).E.filter (fun D => decide (D ∉ (P).E)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro D hD
    simp [hD]
  rw [hNone]
  simp [boundaryCount_eq_filter_length]


local notation "SEC" => sectionMarked Q
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))

set_option maxHeartbeats 900000 in
/-- If all actual upper runs start at the original source, a geometric
identification of the companion-special locus suffices for equality of
the whole positive mixed maxima. Their actual divisor incidence ties at zero. -/
theorem later_positive_mixed_max_eq_of_shared_initial_head
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hAttain : (E₀).Nonempty)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (hRun : ∀ a : S₀, regimeRun (stepRegime P (s + 1)) T a.val = T.length)
    (hSpecial : ∀ a : S₀, (ofLex (F a).companion).2 = ⊤ ↔ a ∈ E₀) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  have hZero (a : S₀) : (ofLex (F a).companion).1 = 0 :=
    (laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)).trans
        (upperHeadNonOriginalBoundaryCount_eq_zero_of_full_run Q T a.val (hRun a))
  exact later_positive_mixed_max_eq_of_boundary_trace Q T hQ hT hCan hMax hSecCan
    hBound hAttain F 0 (fun a ha => ⟨hZero a, (hSpecial a).mpr ha⟩)
    (fun a ha => Or.inr ⟨hZero a, lt_top_iff_ne_top.mpr (fun h => ha ((hSpecial a).mp h))⟩)

end
end Hironaka.HironakaG1LaterMixedUpperBornTrace
