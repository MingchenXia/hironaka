import Hironaka.Resolution.HironakaG1LaterMixedCentreBoundaryTrace
import Hironaka.Resolution.HironakaG1LaterMixedUpperBornTrace
import Hironaka.Resolution.HironakaG1ActualLaterSuccessorRead
import Hironaka.Resolution.HironakaG8PowerLowerMarks
import Hironaka.Resolution.HironakaG1LaterMixedLiveCentres

/-! # Actual canonical reads and exact maximum keys at an attained positive level -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1ActualHighestPhaseKeys
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG8MemberLoci
  HironakaG1ActualLaterSuccessorRead HironakaG8PowerLowerMarks
  HironakaG1LaterPositiveBranchOrder HironakaG1LaterPositiveStratumCentres
  HironakaG1LaterMixedCentreBoundaryTrace HironakaG1LaterMixedUpperBornTrace
  HironakaG1LaterLiteralSectionMixedStratum HironakaG1RecursiveMemberValueTransport
  HironakaG1LaterMixedLiveCentres HironakaG1LaterSelectedSectionClass CoefficientIdealRestriction HironakaG1LaterSectionPairOrder

section Positive

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

set_option maxHeartbeats 1000000 in
/-- Every actual nonspecial endpoint at a positive level has a realized
companion read. The true order is the fixed source coefficient mark. -/
theorem later_positive_read_from_canonical
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T)
    (a : S₀) (hNS : ¬ IsSpecial P T a.val) :
    ∃ F : LaterPositiveRead Q T a.val k s,
      F.order = (coeffMarkedAlong (barMarked (X := X₀) P)).d := by
  let m := (coeffMarkedAlong (barMarked (X := X₀) P)).d
  let r := regimeRun (stepRegime P (s+1)) T a.val
  let H := head T r
  let R := tail T r
  let p := R.proj a.val
  let L := lowerMarkedM (X := X₀) P (s+1) H p
  have hM : L.d = m := by
    rw [lowerMarkedM_succ_mark]
    rfl
  have h := original_upper_positive_lower_raw_mark (s := s) Q hQ T hCan a.val
    a.property.1 a.property.2 hNS
  have hmPos : 0 < m := hM ▸ h.1
  have hOrder : LaterPositiveOrderAt Q T a.val s m := by
    unfold LaterPositiveOrderAt
    intro j H' R' p' O A Z L' V z hz
    exact (h.2 z hz).trans hM
  exact exists_laterPositiveRead Q T a.val hQ hCan a.property.1 a.property.2 hNS m hmPos hOrder

/-- Finite keys use the actual retained birth count before the live
recursive leaf. A padded-special source branch has a top key. -/
abbrev PaddedPhaseKey (k : ℕ) := WithTop (ℕ ×ₗ WithTop (ValTy k))

private theorem max_image_of_level_read {A Y Λ : Type*} [LinearOrder Λ]
    (D : Set Y) (l : Y → ℕ) (j : ℕ)
    (g : Y → Λ) (i : A → Y) (K : Type*) [LinearOrder K] (key : A → K)
    (hRange : range i = D ∩ {y | l y = j}) (hTop : Nonempty A)
    (hBound : ∀ y ∈ D, l y ≤ j)
    (hLevel : ∀ x y, l x < l y → g x < g y)
    (hCut : ∀ a b, key a < key b ↔ g (i a) < g (i b)) :
    maxLocus g D = i '' maxLocus key univ := by
  have hAnchor (a : A) : i a ∈ D ∧ l (i a) = j := by
    have h : i a ∈ D ∩ {y | l y = j} := hRange ▸ mem_range_self a
    exact h
  have hLe (a b : A) : key a ≤ key b ↔ g (i a) ≤ g (i b) := by
    simpa only [not_lt] using not_congr (hCut b a)
  ext y
  constructor
  · intro hy
    have hJy : l y = j := by
      by_contra hNe
      obtain ⟨a⟩ := hTop
      have hlt := lt_of_le_of_ne (hBound y hy.1) hNe
      exact not_lt_of_ge (hy.2 _ (hAnchor a).1) (hLevel _ _ (hlt.trans_eq (hAnchor a).2.symm))
    have hR : y ∈ range i := hRange.symm ▸ (show y ∈ D ∩ {y | l y = j} from ⟨hy.1,hJy⟩)
    obtain ⟨a, rfl⟩ := hR
    exact ⟨a, ⟨mem_univ _, fun b _ => (hLe b a).mpr (hy.2 _ (hAnchor b).1)⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(hAnchor a).1, fun y hy => ?_⟩
    rcases lt_or_eq_of_le (hBound y hy) with hp | hp
    · exact (hLevel _ _ (hp.trans_eq (hAnchor a).2.symm)).le
    · have hR : y ∈ range i := hRange.symm ▸ (show y ∈ D ∩ {y | l y = j} from ⟨hy,hp⟩)
      obtain ⟨b, rfl⟩ := hR
      exact (hLe b a).mp (ha.2 b (mem_univ _))

set_option maxHeartbeats 1200000 in
/-- Every highest positive padded stratum has an exact actual phase key.
It retains the top branch and uses the realized finite companion on
all other points. The key computes the original whole maximum locus. -/
theorem padded_maximum_from_actual_highest_keys
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T)
    (hTop : (S₀).Nonempty) (hBound : ∀ y ∈ C₀, level P T y ≤ s+1) :
    ∃ (F : ∀ a : S₀, ¬ IsSpecial P T a.val → LaterPositiveRead Q T a.val k s)
      (key : S₀ → PaddedPhaseKey k),
      (∀ a, key a = ⊤ ↔ IsSpecial P T a.val) ∧
      (∀ a h, key a = (↑(toLex (upperHeadNonOriginalBoundaryCount Q T s a.val,
        (ofLex (F a h).companion).2)) : PaddedPhaseKey k)) ∧
      (∀ a b, key a < key b ↔ f T a.val < f T b.val) ∧
      maxLocus (f T) C₀ = Subtype.val '' maxLocus key univ := by
  classical
  choose F hF using later_positive_read_from_canonical Q T hQ hCan
  let key (a : S₀) : PaddedPhaseKey k :=
    if h : ¬ IsSpecial P T a.val then ((F a h).companion : PaddedPhaseKey k) else ⊤
  have topRead (a : S₀) (ha : IsSpecial P T a.val) :
      f T a.val = toLex (s+1, (⊤ : WithTop (ValTy (k+1)))) := by
    have h := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (X := X₀)
      (invFamily (Nat.succ_pos n) (k+1)) P (lowerMarkedM (X := X₀) P) T ha
    exact h.trans (congrArg (fun j => toLex (j, (⊤ : WithTop (ValTy (k+1))))) a.property.2)
  have hCut (a b : S₀) : key a < key b ↔ f T a.val < f T b.val := by
    by_cases ha : ¬ IsSpecial P T a.val <;> by_cases hb : ¬ IsSpecial P T b.val
    · have hh := LaterPositiveRead.upper_lt_iff (F a ha) (F b hb)
      have hOrder := (hF a ha).trans (hF b hb).symm
      simp only [hOrder, lt_self_iff_false, false_or, true_and] at hh
      change key a < key b ↔ _
      rw [show key a = ↑(F a ha).companion from dif_pos ha,
        show key b = ↑(F b hb).companion from dif_pos hb, WithTop.coe_lt_coe, Prod.Lex.lt_iff]
      exact hh.symm
    · rw [show key a = ↑(F a ha).companion from dif_pos ha, show key b = ⊤ from dif_neg hb,
        (F a ha).raw_upper, topRead b (not_not.mp hb), Prod.Lex.toLex_lt_toLex]
      simp
    · rw [show key a = ⊤ from dif_neg ha, show key b = ↑(F b hb).companion from dif_pos hb,
        topRead a (not_not.mp ha), (F b hb).raw_upper, Prod.Lex.toLex_lt_toLex]
      simp
    · rw [show key a = ⊤ from dif_neg ha, show key b = ⊤ from dif_neg hb,
        topRead a (not_not.mp ha), topRead b (not_not.mp hb)]
      simp
  refine ⟨F, key, ?_, ?_, hCut, ?_⟩
  · intro a
    by_cases ha : ¬ IsSpecial P T a.val
    · simp [key, ha]
    · simp [key, not_not.mp ha]
  · intro a ha
    have hCount := laterPositiveRead_companion_level_eq_upperHeadNonOriginal Q T hQ hCan
      a.val a.property.1 a.property.2 ha (F a ha)
    rw [show key a = ↑(F a ha).companion from dif_pos ha]
    apply congrArg (fun w : ℕ ×ₗ WithTop (ValTy k) => (w : PaddedPhaseKey k))
    exact ofLex.injective (Prod.ext hCount rfl)
  · have hN : Nonempty S₀ := ⟨⟨hTop.choose, hTop.choose_spec⟩⟩
    apply max_image_of_level_read C₀ (level P T) (s+1) (f T) Subtype.val (PaddedPhaseKey k) key
      Subtype.range_coe hN hBound _ hCut
    intro x y hl
    rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
      Seq.StepOneValueMasked.stepOneInvL_fst]
    exact Or.inl hl

set_option maxHeartbeats 1400000 in
/-- On the same occupied highest stratum the literal section maximum
is computed by actual selected contact values, with special anchors
represented by top. Finite witnesses come from the genuine section
history and its canonical given-contact suffix. -/
theorem section_maximum_from_actual_highest_keys
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hCan : IsCanonical SEC v T)
    (hTop : (S₀).Nonempty) (hBound : ∀ y ∈ C₀, level P T y ≤ s+1) :
    ∃ key : S₀ → WithTop (ValTy k),
      (∀ a, key a = ⊤ ↔ IsSpecial SEC T a.val) ∧
      (∀ a : S₀, ¬ IsSpecial SEC T a.val →
        let j := regimeRun (stepRegime SEC (s+1)) T a.val
        let H := head T j
        let R := tail T j
        let p := R.proj a.val
        ∃ (W : Opens (split T j).1) (u : (split T j).1 → ℂ) (hp : p ∈ W),
          let L := positiveMemberOn P H p W
          let S := positiveMemberOn SEC H p W
          let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
          let z : openPreimage R W := ⟨a.val,hp⟩
          LaterSectionComparison (X := CMfd.of (n := n+1) W) Q.d k C S ∧
          IsCanonical C ((invFamily (Nat.succ_pos n) k).inv C) (restrict W R) ∧
          z ∈ (geoTransformAlong C (restrict W R)).cosupp ∧
          key a = ((invFamily (Nat.succ_pos n) k).inv C (restrict W R) z : WithTop (ValTy k))) ∧
      (∀ a b, key a < key b ↔ v T a.val < v T b.val) ∧
      maxLocus (v T) (geoTransformAlong SEC T).cosupp = Subtype.val '' maxLocus key univ := by
  have hCos : C₀ = (geoTransformAlong SEC T).cosupp :=
    ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 T).2 hT
  have hLevel (y : Y) : level P T y = level SEC T y :=
    level_eq_of_E_eq (A := P) (B := SEC) rfl T y
  have hAnchor (a : S₀) : a.val ∈ (geoTransformAlong SEC T).cosupp ∧ level SEC T a.val = s+1 :=
    ⟨hCos ▸ a.property.1, (hLevel a.val).symm.trans a.property.2⟩
  obtain ⟨g, hGTop, hGFinite, hGLt, hGMax, _, _⟩ := later_literal_section_mixed_stratum Q hQ T
    hMax hCan (Subtype.val : S₀ → Y) hAnchor
  refine ⟨g, hGTop, hGFinite, hGLt, ?_⟩
  have hRestr : (geoTransformAlong SEC T).cosupp ∩ {y | level SEC T y = s+1} = S₀ := by
    ext y
    change (_ ∧ level SEC T y = s+1) ↔ (y ∈ C₀ ∧ level P T y = s+1)
    rw [← hCos, ← hLevel]
  have hBound' (y : Y) (hy : y ∈ (geoTransformAlong SEC T).cosupp) : level SEC T y ≤ s+1 :=
    (hLevel y) ▸ hBound y (hCos.symm ▸ hy)
  obtain ⟨a, ha⟩ := hTop
  have hMax' := later_literal_section_max_locus_highest_level (k := k) Q T
    (geoTransformAlong SEC T).cosupp hBound'
    ⟨a, (hAnchor ⟨a,ha⟩).1, (hAnchor ⟨a,ha⟩).2⟩
  change maxLocus (v T) (geoTransformAlong SEC T).cosupp =
    maxLocus (v T) ((geoTransformAlong SEC T).cosupp ∩ {y | level SEC T y = s+1}) at hMax'
  rw [hRestr] at hMax'
  rw [Subtype.range_coe] at hGMax
  exact hMax'.trans hGMax.symm

set_option maxHeartbeats 1300000 in
/-- On an occupied section-special stratum with only finite padded
branches, matching the whole maximum loci requires the actual maximum
count and the realized leaf cuts. The canonical history itself supplies
every companion read used by the criterion. -/
theorem mixed_special_maximum_iff_from_canonical
    (hQ : IsInvDomain (k+1) Q) (hT : IsGeoTestTower P T)
    (hCan : IsCanonical P f T)
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hSecCan : IsCanonical SEC v T)
    (hBound : ∀ y ∈ C₀, level P T y ≤ s+1)
    (hNS : ∀ a : S₀, ¬ IsSpecial P T a.val)
    (ref : S₀) (hRef : IsSpecial SEC T ref.val) :
    ∃ F : ∀ a : S₀, LaterPositiveRead Q T a.val k s,
      let count := upperHeadNonOriginalBoundaryCount Q T s
      let leaf := fun a : S₀ => (ofLex (F a).companion).2
      maxLocus (f T) C₀ = maxLocus (v T) (geoTransformAlong SEC T).cosupp ↔
        ref.val ∈ maxLocus count S₀ ∧
        (∀ a : S₀, IsSpecial SEC T a.val → count a.val = count ref.val ∧ leaf a = leaf ref) ∧
        (∀ a : S₀, ¬ IsSpecial SEC T a.val → count a.val = count ref.val → leaf a < leaf ref) := by
  classical
  have hRead (a : S₀) := later_positive_read_from_canonical Q T hQ hCan a (hNS a)
  let F (a : S₀) := Classical.choose (hRead a)
  exact ⟨F, later_mixed_max_eq_iff_max_count_and_live_leaf Q T hQ hT hCan
    hMax hSecCan hBound F hNS ref hRef⟩

end Positive
end
end Hironaka.HironakaG1ActualHighestPhaseKeys
