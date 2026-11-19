import Hironaka.Resolution.HironakaG1LaterMixedUpperBornTrace
import Hironaka.Resolution.HironakaG1InitialPositiveSpecialRecoding

/-! # A local geometric criterion for the special branch of both readers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1LaterMixedPairedSaturation

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong
  NonmonomialOrderRegime NonmonomialOrderTail GeneralValue TangentDirectionAlong
  MemberInterLocusAlong CodimOneSupportAlong BoundaryCount
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1LaterMixedCentreBoundaryTrace
  HironakaG1LaterMixedUpperBornTrace HironakaG1InitialPositiveSpecialRecoding

/-- The current contact germ of the actual companion and the actual
selected member germ of the section have the same threshold through
the actual open endpoint map. -/
def PairedSaturation {n : ℕ} {Y Z : CMfd.{0} n}
    (B : MarkedIdeal n Z) (A : MarkedIdeal n Y) (E : List (Set Y)) (i : Z → Y) (w : Z) : Prop :=
  B.IsWellFormed ∧ 1 ≤ B.d ∧ w ∈ B.cosupp ∧ i w ∈ A.cosupp ∧
  ∃ (Ω : Set Z) (u : Z → ℂ),
    w ∈ Ω ∧ IsTangentDirectionAlong B.N B.ideal B.d Ω u ∧
    (∀ᶠ x in 𝓝 w, x ∈ B.cosupp ↔ i x ∈ A.cosupp) ∧
    (∀ᶠ x in 𝓝 w, x ∈ B.N ∩ {z | u z = 0} ∩ Ω ↔
      i x ∈ A.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D)

set_option maxHeartbeats 650000 in
/-- The same actual trace can be saturated or proper. Saturation detects
codimension one in the companion exactly when it detects the member
locus in the section. -/
theorem PairedSaturation.codimOne_iff_member {n : ℕ} {Y Z : CMfd.{0} n}
    {B : MarkedIdeal n Z} {A : MarkedIdeal n Y} {E : List (Set Y)} {i : Z → Y} {w : Z}
    (h : PairedSaturation B A E i w) (hi : Topology.IsOpenEmbedding i) :
    w ∈ codimOnePartAlong B.N B.ideal B.d ↔ i w ∈ memberInterLocus A.N E A.cosupp := by
  obtain ⟨hB, hd, hw, hy, Ω, u, hwΩ, hu, hCos, hContact⟩ := h
  rw [codimOnePartAlong_iff_contact_saturated B hB hd hu hw hwΩ, mem_memberInterLocus_iff,
    and_iff_right hy, ← hi.map_nhds_eq w]
  change (∀ᶠ x in 𝓝 w, x ∈ B.N ∩ {z | u z = 0} ∩ Ω → x ∈ B.cosupp) ↔
    ∀ᶠ x in 𝓝 w, i x ∈ A.N → (∀ D ∈ E, i w ∈ D → i x ∈ D) → i x ∈ A.cosupp
  constructor
  · intro hSat
    filter_upwards [hSat, hCos, hContact] with x hx hc hct hxA hxE
    exact hc.mp (hx (hct.mpr ⟨hxA, hxE⟩))
  · intro hSat
    filter_upwards [hSat, hCos, hContact] with x hx hc hct hxB
    exact hc.mpr (hx (hct.mp hxB).1 (hct.mp hxB).2)

/-- At the two actual endpoints, the paired saturation test recognizes
the companion zero special branch and the upper positive member branch. -/
theorem paired_saturation_special_iff {n : ℕ} {X A Y Z : CMfd.{0} n}
    (Sec : MarkedIdeal n X) (T : BlowupTower X Y)
    (J : MarkedIdeal n A) (R : BlowupTower A Z) (w : Z) (i : Z → Y)
    (hi : Topology.IsOpenEmbedding i)
    (hZero : level J R w = 0) (hPositive : 0 < level Sec T (i w))
    (hSat : PairedSaturation (geoTransformAlong (barMarked J) R)
      (geoTransformAlong (barMarked Sec) T) (origMembers Sec T) i w) :
    IsSpecial J R w ↔ IsSpecial Sec T (i w) := by
  have h := hSat.codimOne_iff_member hi
  have hNo : ¬ (1 ≤ (0 : ℕ)) := by decide
  have hPos : 1 ≤ level Sec T (i w) := hPositive
  simpa only [IsSpecial, hZero, true_and, hNo, false_and, or_false,
    Nat.ne_of_gt hPositive, false_or, hPos] using h

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

/-- Paired contact geometry at the two exact masked cuts used by the
padded reader. The point map is the composition of the restrictions. -/
def HasPairedSaturation (y : Y) (F : LaterPositiveRead Q T y k s) : Prop :=
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
    let J := compAt L F.order H'
    ∀ hp' : S'.proj z ∈ O',
      let w : openPreimage S' O' := ⟨z, hp'⟩
      let R := restrict O' S'
      PairedSaturation (geoTransformAlong (barMarked J) R)
        (geoTransformAlong (barMarked SEC) T) (origMembers SEC T)
        (fun x : openPreimage S' O' => x.val.val) w

private theorem boundary_count_eq_level {d : ℕ} {X Z : CMfd.{0} d}
    (J : MarkedIdeal d X) (R : BlowupTower X Z) (w : Z) :
    boundaryCount (J.E.map (HomogenizedGlueingTower.strictAlong R)) w = level J R w := by
  have h : origMembers J R = J.E.map (HomogenizedGlueingTower.strictAlong R) :=
    MemberInterTowerAlong.take_E_geoTransformAlong (barMarked J) R
  exact congrArg (fun E => boundaryCount E w) h.symm

set_option maxHeartbeats 1100000 in
/-- At the actual level-zero companion, paired saturation recognizes the
section-special classifier for the realized leaf. -/
theorem laterPositiveRead_leaf_top_iff_of_paired_saturation
    (y : Y) (F : LaterPositiveRead Q T y k s)
    (hZero : (ofLex F.companion).1 = 0)
    (hPos : 0 < level SEC T y) (hPair : HasPairedSaturation Q T y F) :
    (ofLex F.companion).2 = ⊤ ↔ IsSpecial SEC T y := by
  let r := regimeRun (stepRegime P (s+1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n+1) O
  let B := CMfd.of (n := n+1) (openPreimage S O)
  let L : MarkedIdeal (n+1) A := lowerMarkedM (X := X₀) P (s+1) H p
  let V : BlowupTower A B := restrict O S
  obtain ⟨hp, hp', hCount, hLeaf⟩ := laterPositiveRead_companion_boundary_trace Q T y F
  let z : openPreimage S O := ⟨y, hp⟩
  let j := regimeRun (OrdRegime L F.order) V z
  let H' := head V j
  let S' := tail V j
  let O' := ordMask (geoTransformAlong L H') F.order
  let J := compAt L F.order H'
  let w : openPreimage S' O' := ⟨z, hp'⟩
  let R := restrict O' S'
  let i : openPreimage S' O' → Y := fun x => x.val.val
  have hi : Topology.IsOpenEmbedding i :=
    (openPreimage S O).isOpen.isOpenEmbedding_subtypeVal.comp
      (openPreimage S' O').isOpen.isOpenEmbedding_subtypeVal
  have hLev : level J R w = 0 :=
    (boundary_count_eq_level J R w).symm.trans (hCount.symm.trans hZero)
  have hPair' : PairedSaturation (geoTransformAlong (barMarked J) R)
      (geoTransformAlong (barMarked SEC) T) (origMembers SEC T) i w := hPair hp hp'
  exact hLeaf.trans (paired_saturation_special_iff SEC T J R w i hi hLev hPos hPair')

set_option maxHeartbeats 900000 in
/-- On a shared initial upper run, the paired local threshold at every
anchor gives equality of the whole mixed maxima. -/
theorem later_positive_mixed_max_eq_of_paired_saturation
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (hAttain : (E₀).Nonempty)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (hRun : ∀ a : S₀, regimeRun (stepRegime P (s+1)) T a.val = T.length)
    (hPair : ∀ a : S₀, HasPairedSaturation Q T a.val (F a)) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  apply later_positive_mixed_max_eq_of_shared_initial_head Q T hQ hT hCan hMax hSecCan
    hBound hAttain F hNS hRun
  intro a
  have hZero : (ofLex (F a).companion).1 = 0 :=
    (laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)).trans
        (upperHeadNonOriginalBoundaryCount_eq_zero_of_full_run Q T a.val (hRun a))
  have hLev := HironakaG8MemberLoci.level_eq_of_E_eq (A := P) (B := SEC) rfl T a.val
  have hPos : 0 < level SEC T a.val := by
    rw [← hLev, a.property.2]
    exact Nat.succ_pos s
  exact laterPositiveRead_leaf_top_iff_of_paired_saturation Q T a.val (F a) hZero hPos (hPair a)

end
end Hironaka.HironakaG1LaterMixedPairedSaturation
