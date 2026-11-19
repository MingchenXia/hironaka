import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical
import Hironaka.Invariant.StepOneRestrictOpen

/-! A local carrier criterion for the two original positive special letters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1BornSpecialCarrierCriterion
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal
  ResolutionInvariantSpec StepOneValue StepOneLowerDomain StepOneRestrictOpen StepOneRegime
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci MemberInterLocusAlong
  BoundaryCount InvDomainMemberRestriction MemberInterTowerAlong
  HironakaG1ActualLaterCommonTangent HironakaG1RecursiveMemberValueTransport
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  NonmonomialOrderTail GeneralValue StepOneValueMasked CanonicalCentres
open HomogenizedGlueingTower (N_geoTransformAlong strictAlong)

private theorem outside_closure_diff_iff {X : Type*} [TopologicalSpace X]
    (A Z : Set X) (p : X) : p ∉ closure (A \ Z) ↔ ∀ᶠ y in 𝓝 p, y ∈ A → y ∈ Z := by
  classical
  rw [mem_closure_iff_frequently, Filter.Frequently, not_not]
  exact eventually_congr (Eventually.of_forall fun y => by simp)

/-- The common old-slot incidence cuts both current carriers. The full
ordered transformed boundary, including its born slots, is preserved. At a
positive cosupport anchor, disagreement occurs exactly when holes in the
smaller selected carrier are absent near the anchor and holes outside it
in the larger selected carrier accumulate there. -/
theorem positive_special_carrier_criterion {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (hCar : R.N ⊆ J.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (p : Y)
    (hPos : 0 < level J T p) :
    let A := geoTransformAlong (barMarked J) T
    let B := geoTransformAlong (barMarked R) T
    let E₀ := origMembers J T
    let L := memberRestrict A (membersThrough A.E E₀ p)
    let S := memberRestrict B (membersThrough B.E (origMembers R T) p)
    let Z := A.cosupp
    let D := (L.N \ S.N) \ Z
    A.E = B.E ∧ E₀ = origMembers R T ∧ L.E = S.E ∧
    A.cosupp = B.cosupp ∧ S.N ⊆ L.N ∧
    (IsSpecial J T p ↔ p ∈ Z ∧ p ∉ closure (L.N \ Z)) ∧
    (IsSpecial R T p ↔ p ∈ Z ∧ p ∉ closure (S.N \ Z)) ∧
    ((IsSpecial R T p ∧ ¬ IsSpecial J T p) ↔
      p ∈ Z ∧ p ∉ closure (S.N \ Z) ∧ p ∈ closure D) ∧
    (IsSpecial J T p ↔ IsSpecial R T p ∧ p ∉ closure D) := by
  intro A B E₀ L S Z D
  have hOrig : E₀ = origMembers R T := origMembers_eq_of_E_eq hClass.wEquiv.1 T
  have hE : A.E = B.E := E_geoTransformAlong_eq (show (barMarked J).E = (barMarked R).E from hClass.wEquiv.1) T
  have hLevel := level_eq_of_E_eq hClass.wEquiv.1 T p
  have hPosR : 0 < level R T p := hLevel ▸ hPos
  have hClassJ := bar_local_any_boundary J hJ
  have hClassR := bar_local_any_boundary R hR
  have hCos : A.cosupp = B.cosupp :=
    ((hClassJ.wEquiv.2 T).2 hT).symm.trans (((hClass.trans hClassR).wEquiv.2 T).2 hT)
  have hA₀ : ∀ F ∈ E₀, F ∈ A.E := fun _ h => List.mem_of_mem_take h
  have hB₀ : ∀ F ∈ origMembers R T, F ∈ B.E := fun _ h => List.mem_of_mem_take h
  let Esel : Set Y := {y | ∀ F ∈ E₀, p ∈ F → y ∈ F}
  have hNL : L.N = A.N ∩ Esel := by
    change A.N ∩ memberInter A.E (membersThrough A.E E₀ p) = _
    rw [memberInter_membersThrough hA₀]
  have hNS : S.N = B.N ∩ Esel := by
    change B.N ∩ memberInter B.E (membersThrough B.E (origMembers R T) p) = _
    rw [memberInter_membersThrough hB₀, ← hOrig]
  have hKeep : L.E = S.E := by
    simp only [L, S, memberRestrict_E]
    rw [← hOrig]
    generalize A.E = E at hE ⊢
    rw [← hE]
  have hBA : B.N ⊆ A.N := by
    change (geoTransformAlong (barMarked R) T).N ⊆ (geoTransformAlong (barMarked J) T).N
    rw [N_geoTransformAlong, N_geoTransformAlong]
    exact strictAlong_mono T hCar
  have hSL : S.N ⊆ L.N := by
    rw [hNS, hNL]
    exact inter_subset_inter_left _ hBA
  have hLetter (M : MarkedIdeal n X) (hlM : 0 < level M T p) :
      IsSpecial M T p ↔ p ∈ (geoTransformAlong (barMarked M) T).cosupp ∧
        ∀ᶠ y in 𝓝 p, y ∈ (geoTransformAlong (barMarked M) T).N →
          (∀ F ∈ origMembers M T, p ∈ F → y ∈ F) →
          y ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    unfold IsSpecial
    rw [← mem_memberInterLocus_iff]
    have hOne : 1 ≤ level M T p := hlM
    simp only [Nat.ne_of_gt hlM, false_and, false_or, hOne, true_and]
  have hJiff : IsSpecial J T p ↔ p ∈ Z ∧ p ∉ closure (L.N \ Z) := by
    rw [hLetter J hPos, outside_closure_diff_iff, hNL]
    exact and_congr_right fun _ => eventually_congr (Eventually.of_forall fun _ => and_imp.symm)
  have hRiff : IsSpecial R T p ↔ p ∈ Z ∧ p ∉ closure (S.N \ Z) := by
    rw [hLetter R hPosR, outside_closure_diff_iff, hNS, ← hOrig, ← hCos]
    exact and_congr_right fun _ => eventually_congr (Eventually.of_forall fun _ => and_imp.symm)
  have hUnion : L.N \ Z = (S.N \ Z) ∪ D := by
    ext y
    constructor
    · intro hy
      by_cases h : y ∈ S.N
      · exact Or.inl ⟨h, hy.2⟩
      · exact Or.inr ⟨⟨hy.1, h⟩, hy.2⟩
    · rintro (⟨hyS, hyZ⟩ | ⟨⟨hyL, _⟩, hyZ⟩)
      · exact ⟨hSL hyS, hyZ⟩
      · exact ⟨hyL, hyZ⟩
  have hAgree : IsSpecial J T p ↔ IsSpecial R T p ∧ p ∉ closure D := by
    rw [hJiff, hRiff, hUnion, closure_union, mem_union, not_or, and_assoc]
  refine ⟨hE, hOrig, hKeep, hCos, hSL, hJiff, hRiff, ?_, hAgree⟩
  rw [hAgree, hRiff]
  tauto

set_option maxHeartbeats 1400000 in
/-- The actual localized order companion and its supported reference
obey the carrier criterion throughout their common ordinary test
history. All selected old-slot traces use the literal transformed
boundary of that run. -/
theorem exists_actual_born_special_carrier_criterion {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hl : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let J := compAt L L.d (.refl : BlowupTower A A)
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    (¬ IsSpecial Sec H p) →
    ∃ (a : C) (W : Opens B) (_haW : a ∈ W), a.val.val = p ∧
      let XW := CMfd.of (n := n+1) W
      let Jw := MarkedIdeal.pullback (M' := XW) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := XW) (Subtype.val : W → B) R
      IsInvDomain (k+1) Jw ∧ IsInvDomain k Rw ∧
      LocWPEquiv (X := XW) Jw Rw ∧ Rw.N ⊆ Jw.N ∧
      ∀ {Z : CMfd.{0} (n+1)} (G : BlowupTower XW Z) (_hG : IsGeoTestTower Jw G)
        (z : Z), 0 < level Jw G z →
        let A := geoTransformAlong (barMarked Jw) G
        let B := geoTransformAlong (barMarked Rw) G
        let L := memberRestrict A (membersThrough A.E (origMembers Jw G) z)
        let S := memberRestrict B (membersThrough B.E (origMembers Rw G) z)
        A.E = B.E ∧ L.E = S.E ∧
        (IsSpecial Jw G z ↔ IsSpecial Rw G z ∧
          z ∉ closure ((L.N \ S.N) \ A.cosupp)) := by
  intro X P Sec r H S p O A L C B J R hNSS
  obtain ⟨a, W, u, haW, ha, hJw, hRw, hLoc, _, hTrace, _, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent Q hQ T hCan y hy hl hNS hNSS
  let XW := CMfd.of (n := n+1) W
  let Jw := MarkedIdeal.pullback (M' := XW) (Subtype.val : W → B) J
  let Rw := MarkedIdeal.pullback (M' := XW) (Subtype.val : W → B) R
  have hSub : Rw.N ⊆ Jw.N := fun _ hx => (hTrace ▸ hx).1
  refine ⟨a, W, haW, ha, hJw, hRw, hLoc, hSub, ?_⟩
  intro Z G hG z hz
  have h := positive_special_carrier_criterion Jw Rw hJw hRw hLoc hSub G hG z hz
  exact ⟨h.1, h.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- Both original special letters and their levels are preserved by
simultaneous restriction of the actual test tower to an open. -/
theorem positive_special_letters_restrict {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hLoc : LocWPEquiv J R) (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (U : Opens X) (z : openPreimage T U) :
    let J' := MarkedIdeal.pullback (Subtype.val : U → X) J
    let R' := MarkedIdeal.pullback (Subtype.val : U → X) R
    let S := restrict U T
    level J' S z = level J T z.val ∧ level R' S z = level R T z.val ∧
      (IsSpecial J' S z ↔ IsSpecial J T z.val) ∧
      (IsSpecial R' S z ↔ IsSpecial R T z.val) := by
  intro J' R' S
  have hTJ := ((bar_local_any_boundary J hJ).wEquiv.2 T).1.mp hT
  have hTR := (((hLoc.trans (bar_local_any_boundary R hR)).wEquiv.2 T).1.mp hT)
  have hp := (restrict_facts J U hJ.isWellFormed hJ.one_le_d T hTJ).2.2 z
  have hr := (restrict_facts R U hR.isWellFormed hR.one_le_d T hTR).2.2 z
  exact ⟨hp.1, hr.1, hp.2.1, hr.2.1⟩

set_option maxHeartbeats 1000000 in
/-- A shorter supported run has a precise geometric witness at its first
excluded predecessor. Conversely any such witness within the padded run
forces the supported clock to be strictly shorter. -/
theorem positive_special_run_cutoff_iff {n k l s : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hLoc : LocWPEquiv J R) (hSub : R.N ⊆ J.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (p : Y) :
    let rJ := regimeRun (stepRegime J (s+1)) T p
    let rR := regimeRun (stepRegime R (s+1)) T p
    rR ≤ rJ ∧
    (rR < rJ ↔ ∃ j : ℕ, 1 ≤ j ∧ j ≤ rJ ∧
      let H := head T j
      let a := (tail T j).proj p
      let A := geoTransformAlong (barMarked J) H
      let B := geoTransformAlong (barMarked R) H
      let L := memberRestrict A (membersThrough A.E (origMembers J H) a)
      let S := memberRestrict B (membersThrough B.E (origMembers R H) a)
      a ∈ A.cosupp ∧ a ∉ closure (S.N \ A.cosupp) ∧
        a ∈ closure ((L.N \ S.N) \ A.cosupp)) := by
  intro rJ rR
  have hIncl (j : ℕ) (h : stepRegime R (s+1) (head T j) ((tail T j).proj p)) :
      stepRegime J (s+1) (head T j) ((tail T j).proj p) := by
    have hHead := ((isGeoTestTower_iff_head_tail J T j).mp hT).1
    have hLev := level_eq_of_E_eq hLoc.wEquiv.1 (head T j) ((tail T j).proj p)
    have hl : level J (head T j) ((tail T j).proj p) = s+1 := hLev.trans h.1
    have hc := positive_special_carrier_criterion J R hJ hR hLoc hSub
      (head T j) hHead ((tail T j).proj p) (hl ▸ Nat.succ_pos s)
    exact ⟨hl, fun hJsp => h.2 ((hc.2.2.2.2.2.2.2.2.mp hJsp).1)⟩
  have hLe : rR ≤ rJ := by
    by_contra! hlt
    have hBound := regimeRun_le_length (stepRegime R (s+1)) T p
    have hStop := not_regime_head_regimeRun (stepRegime J (s+1)) T p
      (show rJ < T.length by omega)
    exact hStop (hIncl (rJ+1) (regime_head_of_le_regimeRun (stepRegime R (s+1)) T p
      (rJ+1) (by omega) (show rJ+1 ≤ rR by omega)))
  refine ⟨hLe, ?_⟩
  constructor
  · intro hlt
    let j := rR+1
    let H := head T j
    let a := (tail T j).proj p
    have hj : j ≤ rJ := hlt
    have hJP := regime_head_of_le_regimeRun (stepRegime J (s+1)) T p j (by omega) hj
    have hLvl := level_eq_of_E_eq hLoc.wEquiv.1 H a
    have hlR := hLvl.symm.trans hJP.1
    have hBound := regimeRun_le_length (stepRegime J (s+1)) T p
    have hStop := not_regime_head_regimeRun (stepRegime R (s+1)) T p
      (show rR < T.length by omega)
    have hSpR : IsSpecial R H a := by
      by_contra hn
      exact hStop ⟨hlR, hn⟩
    have hHead := ((isGeoTestTower_iff_head_tail J T j).mp hT).1
    have hc := positive_special_carrier_criterion J R hJ hR hLoc hSub H hHead a
      (hJP.1 ▸ Nat.succ_pos s)
    exact ⟨j, by omega, hj, hc.2.2.2.2.2.2.2.1.mp ⟨hSpR, hJP.2⟩⟩
  · rintro ⟨j, hj, hjJ, hGap⟩
    have hJP := regime_head_of_le_regimeRun (stepRegime J (s+1)) T p j hj hjJ
    have hHead := ((isGeoTestTower_iff_head_tail J T j).mp hT).1
    have hc := positive_special_carrier_criterion J R hJ hR hLoc hSub
      (head T j) hHead ((tail T j).proj p) (hJP.1 ▸ Nat.succ_pos s)
    have hSp := (hc.2.2.2.2.2.2.2.1.mpr hGap).1
    by_contra! hBack
    exact (regime_head_of_le_regimeRun (stepRegime R (s+1)) T p j hj
      (hjJ.trans hBack)).2 hSp

end
end Hironaka.HironakaG1BornSpecialCarrierCriterion
