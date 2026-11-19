import Hironaka.Resolution.HironakaG1MixedOneChartSpecial

/-! # Later mixed maxima from actual retained counts and recursive leaves -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterMixedLiveCentres
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres ResolutionDriver StepOneValue
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG1LaterPositiveStratumCentres
  HironakaG1LaterPositiveBranchOrder HironakaG1MixedOneChartSpecial HomogenizedIdealAlong

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

set_option maxHeartbeats 900000 in
/-- First retain the maximal actual head count, then maximize the live
companion leaf on precisely that retained stratum. -/
theorem later_padded_max_eq_max_leaf_on_max_head_count
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val) :
    let H := maxLocus countAt S₀
    let leaf := fun a : H => (ofLex (F ⟨a.val, a.property.1⟩).companion).2
    maxLocus (f T) S₀ = Subtype.val '' maxLocus leaf Set.univ := by
  intro H leaf
  have hSub := later_mixed_padded_max_subset_max_head_count Q T hQ hCan F hNS
  have orderEq (a b : S₀) : (F a).order = (F b).order :=
    (laterPositiveRead_order_eq_fixed_mark Q T hQ hCan a.val a.property.1
      a.property.2 (hNS a) (F a)).trans
      (laterPositiveRead_order_eq_fixed_mark Q T hQ hCan b.val b.property.1
        b.property.2 (hNS b) (F b)).symm
  have countEq (a : S₀) : (ofLex (F a).companion).1 = countAt a.val :=
    laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)
  have leIff (a b : S₀) (h : countAt a.val = countAt b.val) :
      f T a.val ≤ f T b.val ↔ (ofLex (F a).companion).2 ≤ (ofLex (F b).companion).2 :=
    (LaterPositiveRead.upper_leaf_order_iff (F a) (F b) (orderEq a b)
      ((countEq a).trans (h.trans (countEq b).symm))).2.1
  ext x
  constructor
  · intro hx
    have hxH := hSub hx
    refine ⟨⟨x, hxH⟩, ⟨Set.mem_univ _, fun b _ => ?_⟩, rfl⟩
    have hTie := le_antisymm (hxH.2 b.val b.property.1) (b.property.2 x hx.1)
    exact (leIff ⟨b.val, b.property.1⟩ ⟨x, hx.1⟩ hTie).mp (hx.2 b.val b.property.1)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property.1, fun y hy => ?_⟩
    let b : S₀ := ⟨y, hy⟩
    let c : S₀ := ⟨a.val, a.property.1⟩
    rcases lt_or_eq_of_le (a.property.2 y hy) with hlt | heq
    · exact (LaterPositiveRead.upper_lt_of_companion_level_lt (F b) (F c) (orderEq b c)
        ((countEq b).trans_lt (hlt.trans_le (countEq c).symm.le))).le
    · have hb : y ∈ H := ⟨hy, fun z hz => (a.property.2 z hz).trans heq.symm.le⟩
      exact (leIff b c heq).mpr (ha.2 ⟨y, hb⟩ (Set.mem_univ _))

set_option maxHeartbeats 900000 in
/-- At maximal count zero, an attained zero companion special branch
suppresses all finite leaves. The chart's zero-special recognition
identifies the retained maximal leaves with the designated special anchors. -/
theorem later_padded_max_eq_zero_special_of_occupied
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (hChart : ∀ a : S₀, countAt a.val = 0 →
      ((ofLex (F a).companion).2 = ⊤ ↔ a ∈ E₀))
    (hOccupied : ∃ a : S₀, a ∈ E₀ ∧ a.val ∈ maxLocus countAt S₀ ∧ countAt a.val = 0) :
    maxLocus (f T) S₀ = Subtype.val '' E₀ := by
  obtain ⟨a, ha, haMax, haZero⟩ := hOccupied
  have hZero (b : S₀) : countAt b.val = 0 :=
    Nat.eq_zero_of_le_zero ((haMax.2 b.val b.property).trans_eq haZero)
  have hAll (b : S₀) : b.val ∈ maxLocus countAt S₀ :=
    ⟨b.property, fun z hz => by rw [hZero b, hZero ⟨z, hz⟩]⟩
  rw [later_padded_max_eq_max_leaf_on_max_head_count Q T hQ hCan F hNS]
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    let c : S₀ := ⟨b.val, b.property.1⟩
    have hCompare := hb.2 ⟨a.val, haMax⟩ (Set.mem_univ _)
    change (ofLex (F a).companion).2 ≤ (ofLex (F c).companion).2 at hCompare
    rw [(hChart a haZero).mpr ha] at hCompare
    exact ⟨c, (hChart c (hZero c)).mp (top_le_iff.mp hCompare), rfl⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨b.val, hAll b⟩, ⟨Set.mem_univ _, fun c _ => ?_⟩, rfl⟩
    change (ofLex (F ⟨c.val, c.property.1⟩).companion).2 ≤ (ofLex (F b).companion).2
    rw [(hChart b (hZero b)).mpr hb]
    exact le_top

set_option maxHeartbeats 1000000 in
/-- Whole mixed maxima agree exactly when special anchors survive the
count filter and tie the reference live leaf, while all other survivors
have strictly smaller live leaves. Fewer incidences suppress a point
without any hypothesis on its recursive value. -/
theorem later_mixed_max_eq_iff_max_count_and_live_leaf
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref : S₀) (hRef : ref ∈ E₀) :
    let leaf := fun a : S₀ => (ofLex (F a).companion).2
    (maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp) ↔
      ref.val ∈ maxLocus countAt S₀ ∧
      (∀ a ∈ E₀, countAt a.val = countAt ref.val ∧ leaf a = leaf ref) ∧
      (∀ a ∉ E₀, countAt a.val = countAt ref.val → leaf a < leaf ref) := by
  intro leaf
  have hc (a : S₀) : (ofLex (F a).companion).1 = countAt a.val :=
    laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan a.val
      a.property.1 a.property.2 (hNS a) (F a)
  have read (a : S₀) : (F a).companion = toLex (countAt a.val, leaf a) := by
    apply ofLex.injective
    exact Prod.ext (hc a) rfl
  have ltRead (a b : S₀) : (F a).companion < (F b).companion ↔
      countAt a.val < countAt b.val ∨ countAt a.val = countAt b.val ∧ leaf a < leaf b := by
    rw [read a, read b, Prod.Lex.toLex_lt_toLex]
  rw [later_positive_mixed_max_eq_iff_companions Q T hQ hT hCan hMax hSecCan hBound ⟨ref,hRef⟩ F]
  constructor
  · rintro ⟨hTie, hLt⟩
    have hSpecial (a : S₀) (ha : a ∈ E₀) :
        countAt a.val = countAt ref.val ∧ leaf a = leaf ref := by
      have h := congrArg ofLex (hTie a ha ref hRef)
      exact ⟨(hc a).symm.trans ((congrArg Prod.fst h).trans (hc ref)), congrArg Prod.snd h⟩
    refine ⟨⟨ref.property, fun x hx => ?_⟩, hSpecial, fun a ha he => ?_⟩
    · by_cases ha : (⟨x, hx⟩ : S₀) ∈ E₀
      · exact (hSpecial ⟨x, hx⟩ ha).1.le
      · rcases (ltRead ⟨x, hx⟩ ref).mp (hLt ⟨x, hx⟩ ha ref hRef) with h | h
        · exact h.le
        · exact h.1.le
    · rcases (ltRead a ref).mp (hLt a ha ref hRef) with h | h
      · exact ((lt_irrefl _) (he ▸ h)).elim
      · exact h.2
  · rintro ⟨hCount, hTie, hLt⟩
    refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩
    · rw [read a, read b, (hTie a ha).1, (hTie b hb).1, (hTie a ha).2, (hTie b hb).2]
    · apply (ltRead a b).mpr
      rw [(hTie b hb).1, (hTie b hb).2]
      rcases lt_or_eq_of_le (hCount.2 a.val a.property) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hLt a ha h⟩

end Mixed

end
end Hironaka.HironakaG1LaterMixedLiveCentres
