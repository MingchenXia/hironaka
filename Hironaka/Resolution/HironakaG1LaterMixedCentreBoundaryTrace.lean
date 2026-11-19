import Hironaka.Resolution.HironakaG1LaterPositiveMixedCentreCriterion
import Hironaka.Resolution.HironakaG1ActualLaterSuccessorRead

/-! # Actual companion boundary data in later mixed positive comparisons -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterMixedCentreBoundaryTrace

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong BoundaryCount
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase
  GeneralValue HomogenizedGlueingTower MemberInterTowerAlong
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1LaterPositiveSuccessorRead
  HironakaG1ActualLaterSuccessorRead HironakaG1LaterPositiveMixedCentreCriterion

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)}
  (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))

set_option maxHeartbeats 900000 in
/-- Every realized positive padded tuple on a canonical prefix has the
same true order, the fixed coefficient mark of the starting bar record.
The actual upper run cut and selected old members can vary. -/
theorem laterPositiveRead_order_eq_fixed_mark
    (hQ : IsInvDomain (k + 1) Q) (hCan : IsCanonical P f T)
    (y : Y) (hy : y ∈ C₀) (hLevel : level P T y = s + 1)
    (hNS : ¬ IsSpecial P T y) (F : LaterPositiveRead Q T y k s) :
    F.order = (coeffMarkedAlong (barMarked (X := X₀) P)).d := by
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n + 1) O
  let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
  have h := (original_upper_positive_lower_raw_mark Q hQ T hCan y hy hLevel hNS).2
  obtain ⟨hp, _, hOrder, _⟩ := F.realized
  let z : openPreimage S O := ⟨y, hp⟩
  have hEq : F.order = L.d := hOrder.symm.trans (h z rfl)
  change F.order = (coeffMarkedAlong (barMarked (X := X₀) P)).d
  rw [hEq]
  change (coeffMarkedAlong (geoTransformAlong (barMarked (X := X₀) P) H)).d = _
  simp only [coeffMarkedAlong, CoefficientIdeal.msum, derivMarkedAlong_d, d_geoTransformAlong]

private theorem companion_letter_geometry {m q : ℕ} {A B : CMfd.{0} m}
    (hm : 0 < m) (J : MarkedIdeal m A) (R : BlowupTower A B) (w : B)
    (hJ : IsInvDomain (q + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hm q) J) R)
    (hw : w ∈ (geoTransformAlong J R).cosupp) (o : ℕ) (c : ℕ ×ₗ WithTop (ValTy q))
    (hVal : HironakaG1InitialPositiveGeneralRead.positiveSuccessorRead o
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hm q) J R w) =
        HironakaG1InitialPositiveGeneralRead.positiveSuccessorRead o c) :
    (ofLex c).1 = boundaryCount (J.E.map (strictAlong R)) w ∧
      ((ofLex c).2 = ⊤ ↔ IsSpecial J R w) := by
  let I := invFamily hm q
  let val := Seq.StepOneValueMasked.stepOneInvM I J R w
  have hComp : val = c := by
    have hc := congrArg (fun a : ValTy (q + 1) => ofLex ((ofLex a).2)) hVal
    have hc' : Sum.inr (val : WithTop (ℕ ×ₗ WithTop (ValTy q))) =
        Sum.inr (c : WithTop (ℕ ×ₗ WithTop (ValTy q))) := hc
    exact WithTop.coe_inj.mp (Sum.inr.inj hc')
  have hLevel : (ofLex val).1 = level J R w := by
    rw [show val = Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) R w from rfl]
    exact Seq.StepOneValueMasked.stepOneInvL_fst I J (lowerMarkedM J) R w
  have hMembers : origMembers J R = J.E.map (strictAlong R) := by
    change (geoTransformAlong (barMarked J) R).E.take J.E.length = _
    exact take_E_geoTransformAlong (barMarked J) R
  have hBarTest := Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hm R hCan
  have hwBar : w ∈ (geoTransformAlong (barMarked J) R).cosupp := hBarTest.2.2.symm ▸ hw
  have hLeaf : (ofLex val).2 = ⊤ ↔ IsSpecial J R w := by
    change (ofLex (Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) R w)).2 = ⊤ ↔ _
    by_cases hs : IsSpecial J R w
    · rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial I J (lowerMarkedM J) R hs]
      exact iff_of_true rfl hs
    · rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial I J (lowerMarkedM J) R hs]
      exact iff_of_false
        (Seq.StepOneValueMasked.lowerValueL_ne_top J I hJ.isWellFormed hJ.one_le_d hm
          hMax (lowerMarkedM J) R hBarTest.1 hwBar hs) hs
  rw [← hComp]
  exact ⟨hLevel.trans (by rw [level, hMembers]), hLeaf⟩

set_option maxHeartbeats 900000 in
/-- The actual companion letter has first entry the incidence count of
the strict transforms of all ordered members retained in its own source
record. Its second entry is top precisely on the actual companion special
branch. -/
theorem laterPositiveRead_companion_boundary_trace (y : Y) (F : LaterPositiveRead Q T y k s) :
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let B := CMfd.of (n := n + 1) (openPreimage S O)
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
    let V : BlowupTower A B := restrict O S
    ∃ hp : p ∈ O,
      let z : openPreimage S O := ⟨y, hp⟩
      let j := regimeRun (OrdRegime L F.order) V z
      let H' := head V j
      let S' := tail V j
      let O' := ordMask (geoTransformAlong L H') F.order
      let J := compAt L F.order H'
      ∃ hp' : S'.proj z ∈ O',
        let w : openPreimage S' O' := ⟨z, hp'⟩
        let R := restrict O' S'
        (ofLex F.companion).1 = boundaryCount (J.E.map (strictAlong R)) w ∧
        ((ofLex F.companion).2 = ⊤ ↔ IsSpecial J R w) := by
  intro r H S p O A B L V
  obtain ⟨hp, _, _, hRead⟩ := F.realized
  refine ⟨hp, ?_⟩
  dsimp only
  obtain ⟨hp', hJ, hMax, hCan, hw, hVal⟩ := hRead
  refine ⟨hp', ?_⟩
  let z : openPreimage S O := ⟨y, hp⟩
  let j := regimeRun (OrdRegime L F.order) V z
  let H' := head V j
  let S' := tail V j
  let O' := ordMask (geoTransformAlong L H') F.order
  let w : openPreimage S' O' := ⟨z, hp'⟩
  let R := restrict O' S'
  let J := compAt L F.order H'
  exact companion_letter_geometry (q := k) (Nat.succ_pos n) J R w hJ hMax hCan hw
    F.order F.companion hVal


set_option maxHeartbeats 400000 in
private theorem read_not_special (y : Y) (F : LaterPositiveRead Q T y k s) :
    ¬ IsSpecial P T y := by
  intro h
  have hv : f T y = toLex (level P T y, (⊤ : WithTop (ValTy (k+1)))) :=
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial
      (X := X₀) (invFamily (Nat.succ_pos n) (k + 1)) P (lowerMarkedM (X := X₀) P) T
      (y := y) h
  have he := congrArg (fun z : ℕ ×ₗ WithTop (ValTy (k+1)) => (ofLex z).2)
    (F.raw_upper.symm.trans hv)
  exact WithTop.coe_ne_top he

private theorem all_anchor_order_eq (hQ : IsInvDomain (k + 1) Q) (hCan : IsCanonical P f T)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) (a b : S₀) :
    (F a).order = (F b).order :=
  (laterPositiveRead_order_eq_fixed_mark Q T hQ hCan a.val a.property.1 a.property.2
    (read_not_special Q T a.val (F a)) (F a)).trans
      (laterPositiveRead_order_eq_fixed_mark Q T hQ hCan b.val b.property.1 b.property.2
        (read_not_special Q T b.val (F b)) (F b)).symm

set_option maxHeartbeats 650000 in
/-- The selected true orders cancel across every highest-level padded
nonspecial anchor of a canonical prefix, leaving an exact criterion
expressed solely in the actual companions. -/
theorem later_positive_mixed_max_eq_iff_companions
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hPaddedCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hSpecial : (E₀).Nonempty) (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) :
    (maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp) ↔
      (∀ a ∈ E₀, ∀ b ∈ E₀, (F a).companion = (F b).companion) ∧
      (∀ a ∉ E₀, ∀ b ∈ E₀, (F a).companion < (F b).companion) := by
  have hTie (a b : S₀) : laterTuple (F a) = laterTuple (F b) ↔ (F a).companion = (F b).companion := by
    constructor
    · exact congrArg (fun t : ℕ ×ₗ (ℕ ×ₗ WithTop (ValTy k)) => (ofLex t).2)
    · intro h
      change toLex ((F a).order, (F a).companion) = toLex ((F b).order, (F b).companion)
      rw [all_anchor_order_eq Q T hQ hPaddedCan F a b, h]
  have hLt (a b : S₀) : laterTuple (F a) < laterTuple (F b) ↔ (F a).companion < (F b).companion := by
    change toLex ((F a).order, (F a).companion) < toLex ((F b).order, (F b).companion) ↔ _
    rw [all_anchor_order_eq Q T hQ hPaddedCan F a b]
    simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or]
  rw [later_positive_mixed_max_eq_iff Q T hQ hT hMax hSecCan hBound hSpecial F]
  simp only [hTie, hLt]

set_option maxHeartbeats 650000 in
/-- Divisor trace dominance suffices. Section-special anchors must have
equal actual retained incidence counts and themselves read the companion
top. Section-finite anchors may have smaller retained counts or the same
count with a finite companion leaf. -/
theorem later_positive_mixed_max_eq_of_boundary_trace
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hPaddedCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hSpecial : (E₀).Nonempty) (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) (b : ℕ)
    (hTop : ∀ a ∈ E₀, (ofLex (F a).companion).1 = b ∧ (ofLex (F a).companion).2 = ⊤)
    (hBelow : ∀ a ∉ E₀, (ofLex (F a).companion).1 < b ∨
      (ofLex (F a).companion).1 = b ∧ (ofLex (F a).companion).2 < ⊤) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  apply (later_positive_mixed_max_eq_iff_companions Q T hQ hT hPaddedCan hMax hSecCan
    hBound hSpecial F).mpr
  constructor
  · intro a ha c hc
    exact congrArg toLex (Prod.ext ((hTop a ha).1.trans (hTop c hc).1.symm)
      ((hTop a ha).2.trans (hTop c hc).2.symm))
  · intro a ha c hc
    rw [Prod.Lex.lt_iff, (hTop c hc).1, (hTop c hc).2]
    exact hBelow a ha

/-- A two-anchor divisor mismatch obstructs equality of the whole mixed
maxima. It suffices for two section-special anchors to have different
retained incidence, or for a section-finite anchor to have strictly more
retained incidence than a section-special anchor. -/
theorem later_positive_mixed_no_max_eq_of_boundary_mismatch
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hPaddedCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    {a b : S₀} (hb : b ∈ E₀)
    (hMismatch :
      (a ∈ E₀ ∧ (ofLex (F a).companion).1 ≠ (ofLex (F b).companion).1) ∨
      (a ∉ E₀ ∧ (ofLex (F b).companion).1 < (ofLex (F a).companion).1)) :
    maxLocus (f T) C₀ ≠ maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  intro h
  obtain ⟨hTie, hLt⟩ := (later_positive_mixed_max_eq_iff_companions Q T hQ hT
    hPaddedCan hMax hSecCan hBound ⟨b, hb⟩ F).mp h
  rcases hMismatch with ⟨ha, hne⟩ | ⟨ha, hReverse⟩
  · exact hne (congrArg (fun t : ℕ ×ₗ WithTop (ValTy k) => (ofLex t).1) (hTie a ha b hb))
  · have hReverse' : (F b).companion < (F a).companion :=
      Prod.Lex.lt_iff.mpr (Or.inl hReverse)
    exact (not_lt_of_ge hReverse'.le) (hLt a ha b hb)

end
end Hironaka.HironakaG1LaterMixedCentreBoundaryTrace
