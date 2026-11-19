import Hironaka.Resolution.HironakaG1ChronologicalLeafTies
import Hironaka.Resolution.HironakaG1LaterMixedLiveCentres

/-! # Mixed maxima on supported chronological charts -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1ChronologicalMixedMaxima
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaG8LocalHistory HironakaG11InvBMClass
  DivisorExponentAlong HomogenizedIdealAlong BlowupTowerIsomorphism MaxLocusLocal
  StepOneValue StepOneValueMasked StepOneRegime
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterMixedLiveCentres HironakaG1ChronologicalLeafTies

set_option maxHeartbeats 900000 in
/-- Two different masks of the same supported record and chronological
suffix admit a common chart over their intersection. Both full marked
records, including all ordered members and their exponents, restrict to
the same literal record on that chart. -/
theorem common_chronological_chart_of_overlapping_support {n : ℕ}
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : K.ideal.IsCoherent)
    (T : BlowupTower X Y) (y : Y) (U V : Opens X)
    (hU : T.proj y ∈ U) (hV : T.proj y ∈ V) :
    let W := U ⊓ V
    let z : openPreimage T W := ⟨y, hU, hV⟩
    ∃ (C₁ : ChronologicalChart (K := pullback (Subtype.val : U → X) K)
        (restrict U T) ⟨y,hU⟩ (restrict W T) z)
      (C₂ : ChronologicalChart (K := pullback (Subtype.val : V → X) K)
        (restrict V T) ⟨y,hV⟩ (restrict W T) z),
      C₁.record = pullback (Subtype.val : W → X) K ∧
      C₂.record = pullback (Subtype.val : W → X) K := by
  intro W z
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  let C₁ : ChronologicalChart (K := pullback (Subtype.val : U → X) K)
      (restrict U T) ⟨y,hU⟩ (restrict W T) z :=
    ⟨nestedOpens U W, (nestedOpensDiffeo hWU).symm, _,
      (isTowerIso_restrict_nestedOpens hWU T).symm, rfl⟩
  let C₂ : ChronologicalChart (K := pullback (Subtype.val : V → X) K)
      (restrict V T) ⟨y,hV⟩ (restrict W T) z :=
    ⟨nestedOpens V W, (nestedOpensDiffeo hWV).symm, _,
      (isTowerIso_restrict_nestedOpens hWV T).symm, rfl⟩
  exact ⟨C₁,C₂,pullback_symm_nestedOpensDiffeo hK hWU,pullback_symm_nestedOpensDiffeo hK hWV⟩

/-- A finite recursive leaf read on an actual selected suffix. -/
structure SelectedLeafRead {n k : ℕ} (hn : 0 < n) (leaf : WithTop (ValTy k)) where
  source : CMfd.{0} n
  target : CMfd.{0} n
  record : MarkedIdeal n source
  tower : BlowupTower source target
  point : target
  domain : IsInvDomain k record
  canonical : IsCanonical record ((invFamily hn k).inv record) tower
  cosupp : point ∈ (geoTransformAlong record tower).cosupp
  value : leaf = ((invFamily hn k).inv record tower point : WithTop (ValTy k))

/-- Geometric class comparison of the two selected suffixes at one
common chart point. The native record exponents are normalized by their
marks. -/
def SelectedLeafRead.SameChart {n k : ℕ} {hn : 0 < n}
    {a b : WithTop (ValTy k)} (L : SelectedLeafRead hn a) (R : SelectedLeafRead hn b) : Prop :=
  ∃ (A B : CMfd.{0} n) (S : BlowupTower A B) (z : B)
    (C₁ : ChronologicalChart (K := L.record) L.tower L.point S z)
    (C₂ : ChronologicalChart (K := R.record) R.tower R.point S z),
    C₁.record.d = C₂.record.d ∧ LocWPEquiv C₁.record C₂.record ∧ SameCarrierDim C₁.record C₂.record ∧
      ∀ D ∈ C₁.record.E, ∀ x ∈ C₁.record.cosupp, x ∈ D →
        C₂.record.d * divExpAlong n C₁.record.N C₁.record.ideal D x =
          C₁.record.d * divExpAlong n C₂.record.N C₂.record.ideal D x

/-- Literal record equality on a shared open chart supplies the complete
normalized boundary condition, including inherited and born slots. -/
theorem SelectedLeafRead.sameChart_of_matching_records {n k : ℕ} {hn : 0 < n}
    {a b : WithTop (ValTy k)} (L : SelectedLeafRead hn a) (R : SelectedLeafRead hn b)
    {A B : CMfd.{0} n} {S : BlowupTower A B} {z : B}
    (C₁ : ChronologicalChart (K := L.record) L.tower L.point S z)
    (C₂ : ChronologicalChart (K := R.record) R.tower R.point S z)
    (hRecord : C₁.record = C₂.record) : L.SameChart R := by
  refine ⟨A,B,S,z,C₁,C₂,congrArg MarkedIdeal.d hRecord,?_,?_,?_⟩
  · rw [← hRecord]
    exact LocEquiv.refl Kinds.wp _
  · rw [← hRecord]
    exact fun _ _ _ => Iff.rfl
  · rw [← hRecord]
    intros
    rfl

theorem SelectedLeafRead.eq_of_sameChart {n k : ℕ} {hn : 0 < n}
    {a b : WithTop (ValTy k)} {L : SelectedLeafRead hn a} {R : SelectedLeafRead hn b}
    (h : L.SameChart R) : a = b := by
  obtain ⟨A,B,S,z,C₁,C₂,hd,hClass,hDim,hExp⟩ := h
  rw [L.value, R.value]
  exact congrArg (fun v : ValTy k => (v : WithTop (ValTy k)))
    (chronological_chart_recursive_tie hn C₁ C₂ L.domain R.domain L.canonical R.canonical
      L.cosupp R.cosupp hd hClass hDim hExp)

set_option maxHeartbeats 950000 in
/-- The finite nonzero-level companion letter itself determines which
literal selected suffix supplies the lower read. -/
theorem selectedLeafRead_of_finite_positive_letter {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (hJ : IsInvDomain (k+1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (hy : y ∈ (geoTransformAlong J T).cosupp) (c : ℕ ×ₗ WithTop (ValTy k))
    (hValue : Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y = c)
    (hLevel : (ofLex c).1 = b+1) (hFinite : (ofLex c).2 ≠ ⊤) :
    Nonempty (SelectedLeafRead hn (ofLex c).2) := by
  let I := invFamily hn k
  have hL : level J T y = b+1 := by
    rw [← hLevel, ← hValue]
    exact (Seq.StepOneValueMasked.stepOneInvL_fst I J (lowerMarkedM J) T y).symm
  have hNS : ¬ IsSpecial J T y := by
    intro hSpecial
    apply hFinite
    rw [← hValue]
    change (ofLex (Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) T y)).2 = ⊤
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial I J (lowerMarkedM J) T hSpecial]
    rfl
  obtain ⟨hp, hD, hC, hz, hLeaf⟩ :=
    positive_companion_leaf_at_actual_selected_suffix hn J T y b hJ hMax hCan hy hL hNS
  exact ⟨⟨_, _, _, _, _, hD, hC, hz,
    (congrArg (fun a => (ofLex a).2) hValue).symm.trans hLeaf⟩⟩

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

set_option maxHeartbeats 1000000 in
/-- An actual later positive letter at a nonzero companion level with a
finite leaf produces a selected read on its own chronological suffix. -/
theorem later_positive_selectedLeafRead_of_finite {b : ℕ}
    (a : S₀) (F : LaterPositiveRead Q T a.val k s)
    (hLevel : (ofLex F.companion).1 = b+1) (hFinite : (ofLex F.companion).2 ≠ ⊤) :
    Nonempty (SelectedLeafRead (Nat.succ_pos n) (ofLex F.companion).2) := by
  obtain ⟨hp, hComp⟩ := laterPositiveRead_companion_on_actual_order_mask Q T a.val F
  unfold ActualOrderMaskCompanion at hComp
  obtain ⟨hp', hJ, hMax, hCan, hy, hVal⟩ := hComp
  exact selectedLeafRead_of_finite_positive_letter (Nat.succ_pos n) _ _ _
    hJ hMax hCan hy F.companion hVal hLevel hFinite

set_option maxHeartbeats 1100000 in
/-- On the attained highest positive mixed stratum, common chronological
charts suffice to tie the finite live leaves of the section-special
anchors. Strict comparison is needed only for the section-finite
anchors whose retained count ties the reference count. -/
theorem later_mixed_max_eq_of_selected_chronological_charts
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref : S₀) (hRef : ref ∈ E₀)
    (hCount : ref.val ∈ maxLocus countAt S₀)
    (hSpecialCount : ∀ a ∈ E₀, countAt a.val = countAt ref.val)
    (R : ∀ a ∈ E₀, SelectedLeafRead (Nat.succ_pos n) (ofLex (F a).companion).2)
    (hChart : ∀ a (ha : a ∈ E₀), (R a ha).SameChart (R ref hRef))
    (hBelow : ∀ a ∉ E₀, countAt a.val = countAt ref.val →
      (ofLex (F a).companion).2 < (ofLex (F ref).companion).2) :
    maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp :=
  (later_mixed_max_eq_iff_max_count_and_live_leaf Q T hQ hT hCan hMax hSecCan
    hBound F hNS ref hRef).mpr
    ⟨hCount, fun a ha => ⟨hSpecialCount a ha, SelectedLeafRead.eq_of_sameChart (hChart a ha)⟩, hBelow⟩

set_option maxHeartbeats 1100000 in
/-- A top companion leaf at a tied maximal count on a section-finite
anchor obstructs equality of the whole mixed maxima, even if the
section-special reference itself has a top companion leaf. -/
theorem later_mixed_max_ne_of_tied_count_finite_section_top_companion
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref b : S₀) (hRef : ref ∈ E₀) (hb : b ∉ E₀)
    (hCount : countAt b.val = countAt ref.val)
    (hTop : (ofLex (F b).companion).2 = ⊤) :
    maxLocus (f T) C₀ ≠ maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  intro hEq
  have hStrict := ((later_mixed_max_eq_iff_max_count_and_live_leaf Q T hQ hT hCan hMax hSecCan
    hBound F hNS ref hRef).mp hEq).2.2 b hb hCount
  change (ofLex (F b).companion).2 < (ofLex (F ref).companion).2 at hStrict
  rw [hTop] at hStrict
  exact not_top_lt hStrict

set_option maxHeartbeats 1100000 in
/-- If a tied-count cross-branch pair admits the same finite selected
chart class, the two live leaves tie. The section-finite anchor then
cannot be strictly below the section-special reference point. -/
theorem later_mixed_max_ne_of_tied_count_cross_branch_sameChart
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d) (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref b : S₀) (hRef : ref ∈ E₀) (hb : b ∉ E₀)
    (hCount : countAt b.val = countAt ref.val)
    (L : SelectedLeafRead (Nat.succ_pos n) (ofLex (F b).companion).2)
    (R : SelectedLeafRead (Nat.succ_pos n) (ofLex (F ref).companion).2)
    (hChart : L.SameChart R) :
    maxLocus (f T) C₀ ≠ maxLocus (v T) (geoTransformAlong SEC T).cosupp := by
  intro hEq
  have hStrict := ((later_mixed_max_eq_iff_max_count_and_live_leaf Q T hQ hT hCan hMax hSecCan
    hBound F hNS ref hRef).mp hEq).2.2 b hb hCount
  change (ofLex (F b).companion).2 < (ofLex (F ref).companion).2 at hStrict
  exact (lt_irrefl _) ((SelectedLeafRead.eq_of_sameChart hChart) ▸ hStrict)

end Mixed
end
end Hironaka.HironakaG1ChronologicalMixedMaxima
