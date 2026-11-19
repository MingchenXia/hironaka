import Hironaka.Resolution.HironakaG1LaterLiteralSectionMixedStratum
import Hironaka.Resolution.HironakaG1LaterPositiveStratumCentres
import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG1LaterPositiveCANHistory

/-! # Mixed later positive centre comparison from realized padded tuples -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterPositiveMixedCentreCriterion

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionOrderHistory HironakaG1LaterLiteralSectionMixedStratum
  HironakaG1LaterPositiveBranchOrder HironakaG1LaterPositiveStratumCentres
  HironakaG8MemberLoci HironakaG1SupportedStepOne HironakaG1LaterPositiveCANHistory
  NormalCrossings HomogenizedIdealAlong

private theorem maxLocus_eq_iff_ties_and_strict {A Λ : Type*} [LinearOrder Λ]
    (v : A → Λ) (S E : Set A) (hSub : E ⊆ S) (hE : E.Nonempty) :
    maxLocus v S = E ↔
      (∀ x ∈ E, ∀ y ∈ E, v x = v y) ∧
      (∀ x ∈ S, x ∉ E → ∀ y ∈ E, v x < v y) := by
  constructor
  · intro h
    have hMem : ∀ x ∈ E, x ∈ maxLocus v S := fun _ hx => h.symm ▸ hx
    refine ⟨fun x hx y hy => le_antisymm ((hMem y hy).2 x (hSub hx))
      ((hMem x hx).2 y (hSub hy)), ?_⟩
    intro x hx hne y hy
    apply lt_of_le_of_ne ((hMem y hy).2 x hx)
    intro he
    apply hne
    rw [← h]
    exact ⟨hx, fun z hz => he.symm ▸ (hMem y hy).2 z hz⟩
  · rintro ⟨hTie, hLt⟩
    ext x
    constructor
    · intro hx
      by_contra hNot
      obtain ⟨y, hy⟩ := hE
      exact (not_lt_of_ge (hx.2 y (hSub hy))) (hLt x hx.1 hNot y hy)
    · intro hx
      refine ⟨hSub hx, fun y hy => ?_⟩
      by_cases h : y ∈ E
      · exact (hTie y h x hx).le
      · exact (hLt y hy h x hx).le

section

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)}
  (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)

local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "v" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC
local notation "C₀" => (MarkedIdeal.cosupp (geoTransformAlong P T))
local notation "S₀" => positiveLevelStratum Q T s
local notation "E₀" => Set.ofPred (fun a : S₀ => IsSpecial SEC T (Subtype.val a))

private theorem padded_top_max_locus
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hTop : (positiveLevelStratum Q T s).Nonempty) :
    maxLocus (f T) C₀ = maxLocus (f T) (positiveLevelStratum Q T s) := by
  have hDom (x : Y) (hx : x ∈ C₀) (hxNot : x ∉ positiveLevelStratum Q T s)
      (y : Y) (hy : y ∈ positiveLevelStratum Q T s) : f T x < f T y := by
    have hlt := (lt_of_le_of_ne (hBound x hx) (fun he => hxNot ⟨hx, he⟩)).trans_eq hy.2.symm
    rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
      Seq.StepOneValueMasked.stepOneInvL_fst]
    exact Or.inl hlt
  ext x
  constructor
  · rintro ⟨hx, hMax⟩
    refine ⟨?_, fun y hy => hMax y hy.1⟩
    by_contra hxNot
    obtain ⟨y, hy⟩ := hTop
    exact (not_lt_of_ge (hMax y hy.1)) (hDom x hx hxNot y hy)
  · rintro ⟨hx, hMax⟩
    refine ⟨hx.1, fun y hy => ?_⟩
    by_cases h : y ∈ positiveLevelStratum Q T s
    · exact hMax y h
    · exact (hDom y hy h x hx).le

set_option maxHeartbeats 1200000 in
/-- Once some section-special point attains the highest positive level,
matching the actual mixed section maximum requires exactly ties among its
special anchors and strict padded tuple domination of its finite anchors. -/
theorem later_positive_mixed_max_eq_iff
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hSpecial : (E₀).Nonempty) (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) :
    (maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp) ↔
      (∀ a ∈ E₀, ∀ b ∈ E₀, laterTuple (F a) = laterTuple (F b)) ∧
      (∀ a ∉ E₀, ∀ b ∈ E₀, laterTuple (F a) < laterTuple (F b)) := by
  have hCos : C₀ = (geoTransformAlong SEC T).cosupp :=
    ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 T).2 hT
  have hLevel : ∀ y : Y, level P T y = level SEC T y :=
    level_eq_of_E_eq (A := P) (B := SEC) rfl T
  let i : S₀ → Y := Subtype.val
  have hi : range i = S₀ := Subtype.range_coe
  have hTop : (S₀).Nonempty := by
    obtain ⟨a, _⟩ := hSpecial
    exact ⟨a.val, a.property⟩
  have hAnchor (a : S₀) : i a ∈ (geoTransformAlong SEC T).cosupp ∧ level SEC T (i a) = s + 1 :=
    ⟨hCos ▸ a.property.1, (hLevel a.val).symm.trans a.property.2⟩
  obtain ⟨g, _, _, _, _, _, hgMax⟩ :=
    later_literal_section_mixed_stratum Q hQ T hMax hCan i hAnchor
  have hSecMax := hgMax hSpecial
  rw [hi] at hSecMax
  have hSlice :
      (geoTransformAlong SEC T).cosupp ∩ {y | level SEC T y = s + 1} = S₀ := by
    rw [← hCos]
    ext y
    change (_ ∧ level SEC T y = s + 1) ↔ (_ ∧ level P T y = s + 1)
    rw [← hLevel]
  have hSecAll := later_literal_section_max_locus_highest_level (k := k) Q T
    (geoTransformAlong SEC T).cosupp
    (fun y hy => (hLevel y) ▸ hBound y (hCos.symm ▸ hy))
    (by obtain ⟨a, _⟩ := hSpecial; exact ⟨a.val, (hAnchor a).1, (hAnchor a).2⟩)
  change maxLocus (v T) (geoTransformAlong SEC T).cosupp =
    maxLocus (v T) ((geoTransformAlong SEC T).cosupp ∩ {y | level SEC T y = s + 1}) at hSecAll
  rw [hSlice, hSecMax] at hSecAll
  rw [padded_top_max_locus Q T hBound hTop, hSecAll]
  have hLiftEq :
      maxLocus (f T) S₀ = S₀ ∩ {y | IsSpecial SEC T y} ↔
        maxLocus (fun a : S₀ => f T a.val) univ = E₀ := by
    constructor
    · intro h
      ext a
      constructor
      · intro ha
        have hm : a.val ∈ maxLocus (f T) S₀ :=
          ⟨a.property, fun y hy => ha.2 ⟨y, hy⟩ (mem_univ _)⟩
        rw [h] at hm
        exact hm.2
      · intro ha
        have hm : a.val ∈ maxLocus (f T) S₀ := h.symm ▸ ⟨a.property, ha⟩
        exact ⟨mem_univ _, fun b _ => hm.2 b.val b.property⟩
    · intro h
      ext y
      constructor
      · intro hy
        let a : S₀ := ⟨y, hy.1⟩
        have ha : a ∈ maxLocus (fun a : S₀ => f T a.val) univ :=
          ⟨mem_univ _, fun b _ => hy.2 b.val b.property⟩
        rw [h] at ha
        exact ⟨hy.1, ha⟩
      · rintro ⟨hy, hyS⟩
        let a : S₀ := ⟨y, hy⟩
        have ha : a ∈ maxLocus (fun a : S₀ => f T a.val) univ := h.symm ▸ hyS
        exact ⟨hy, fun z hz => ha.2 ⟨z, hz⟩ (mem_univ _)⟩
  rw [hLiftEq, maxLocus_eq_iff_ties_and_strict _ _ _ (subset_univ _) hSpecial]
  have hEq (a b : S₀) : f T a.val = f T b.val ↔ laterTuple (F a) = laterTuple (F b) := by
    simp only [le_antisymm_iff, upper_le_iff_later_tuple_le (F a) (F b),
      upper_le_iff_later_tuple_le (F b) (F a)]
  have hLt (a b : S₀) : f T a.val < f T b.val ↔ laterTuple (F a) < laterTuple (F b) :=
    upper_lt_iff_later_tuple_lt (F a) (F b)
  simp only [mem_univ, forall_const, hEq, hLt]

variable (hn : 0 < n)
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
  {hWc : IsClosed (zeroPlane U)}
  (N : BlowupTower
    (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
      (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
    (nativeManifold (Nat.le_succ n) V hV))

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "Z₀" => nativeManifold (Nat.le_succ n) V hV
local notation "L₀" => nativePullback (Y := X₀) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) SEC

set_option maxHeartbeats 1200000 in
/-- On a genuine matched prefix the mixed criterion is equivalent to
a history readback, using the actual literal native maximum transport. -/
theorem later_positive_mixed_prefix_read_iff
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E T V hVc hV N)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (hSpecial : (E₀).Nonempty) (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s) :
    PrefixRead (k := k) hn Q T N ↔
      (∀ a ∈ E₀, ∀ b ∈ E₀, laterTuple (F a) = laterTuple (F b)) ∧
      (∀ a ∉ E₀, ∀ b ∈ E₀, laterTuple (F a) < laterTuple (F b)) := by
  have hSec : IsInvDomain (k + 1) SEC :=
    section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hSupport : (SEC).N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) (SEC).E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hNative := (Lift.original_same_bound_step_one_max_loci (q := k)
    (X := X₀) (hk := Nat.le_succ n) (W := zeroPlane U) (hW := zeroPlane_regular U)
    (T := T) (V := V) (hV := hV) (Q := N)
    (Nat.succ_pos n) hn SEC hSec hSupport hTrans hMax hLift hCan).2
  let g := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) L₀ N
  let D := MarkedIdeal.cosupp (n := n) (M := Z₀) (geoTransformAlong (Y := Z₀) L₀ N)
  change (Subtype.val : Z₀ → Y) '' maxLocus g D =
    maxLocus (v T) (geoTransformAlong SEC T).cosupp at hNative
  rw [← later_positive_mixed_max_eq_iff Q T hQ hT hMax hCan hBound hSpecial F]
  constructor
  · intro h
    exact (h.max_image).symm.trans hNative
  · intro h
    exact PrefixRead.exactMax (hNative.trans h.symm)

/-- Different true selected orders at two section-special anchors obstruct
literal native maximum readback on the attained highest stratum. -/
theorem later_positive_mixed_no_prefix_read_of_special_order_lt
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E T V hVc hV N)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    {a b : S₀} (ha : a ∈ E₀) (hb : b ∈ E₀) (hlt : (F a).order < (F b).order) :
    ¬ PrefixRead (k := k) hn Q T N := by
  intro h
  have hTie := ((later_positive_mixed_prefix_read_iff Q T hn N hQ hT hMax hCan hLift
    hBound ⟨a, ha⟩ F).mp h).1 a ha b hb
  exact (ne_of_lt hlt) (congrArg (fun z => (ofLex z).1) hTie)

/-- A section-finite anchor with strictly greater true selected order
than a section-special anchor obstructs literal native readback. -/
theorem later_positive_mixed_no_prefix_read_of_reversed_order
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E T V hVc hV N)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    {a b : S₀} (ha : a ∉ E₀) (hb : b ∈ E₀) (hlt : (F b).order < (F a).order) :
    ¬ PrefixRead (k := k) hn Q T N := by
  intro h
  have hCmp := ((later_positive_mixed_prefix_read_iff Q T hn N hQ hT hMax hCan hLift
    hBound ⟨b, hb⟩ F).mp h).2 a ha b hb
  have hRev : laterTuple (F b) < laterTuple (F a) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
  exact (not_lt_of_ge hRev.le) hCmp

/-- With one section-special anchor, strict domination of every finite
anchor in true selected order already gives literal native readback.
The companion levels and leaves may vary arbitrarily. -/
theorem later_positive_mixed_prefix_read_of_unique_special_order
    (hQ : IsInvDomain (k + 1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E T V hVc hV N)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s + 1)
    (F : ∀ a : S₀, LaterPositiveRead Q T a.val k s)
    (a : S₀) (ha : a ∈ E₀) (hUnique : (E₀).Subsingleton)
    (hOrder : ∀ b ∉ E₀, (F b).order < (F a).order) :
    PrefixRead (k := k) hn Q T N := by
  apply (later_positive_mixed_prefix_read_iff Q T hn N hQ hT hMax hCan hLift
    hBound ⟨a, ha⟩ F).mpr
  refine ⟨fun b hb c hc => congrArg (fun z => laterTuple (F z)) (hUnique hb hc), ?_⟩
  intro b hb c hc
  rw [hUnique hc ha]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hOrder b hb))

end

end
end Hironaka.HironakaG1LaterPositiveMixedCentreCriterion
