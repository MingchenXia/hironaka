import Hironaka.Resolution.HironakaG1PositiveNormalPhase
import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory

/-!
# Positive normal Step One chronology

The section can detect additional positive special points. Its lower run
is therefore a suffix of the padded run, and the values have different
second components at a padded nonspecial point that is section-special.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalChronology

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneRegime CanonicalCentres
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaG1PositiveNormalPhase HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionStepOneHistory HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaG8LocalHistory HironakaG8HomStable
open HomogenizedGlueingTower (strictAlong)
open HomogenizedIdealAlong (IsMaximalOrderAlong)

/-- The positive section run is no longer than the padded run. They
agree exactly when the images at every earlier padded run stage are
nonspecial for the section record. -/
theorem positive_normal_section_run {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let rSec := regimeRun (stepRegime Sec (s + 1)) T y
    rSec ≤ r ∧ (rSec = r ↔
      ∀ i, 1 ≤ i → i ≤ r → ¬ IsSpecial Sec (head T i) ((tail T i).proj y)) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let r := regimeRun (stepRegime P (s + 1)) T y
  let rSec := regimeRun (stepRegime Sec (s + 1)) T y
  have hE : P.E = Sec.E := rfl
  have hTest (i : ℕ) : IsGeoTestTower P (head T i) :=
    ((isGeoTestTower_iff_head_tail P T i).mp hT).1
  have hLevel (i : ℕ) :
      level P (head T i) ((tail T i).proj y) = level Sec (head T i) ((tail T i).proj y) :=
    HironakaG8MemberLoci.level_eq_of_E_eq hE (head T i) ((tail T i).proj y)
  have hLe : rSec ≤ r := by
    by_contra! hh
    have hi : r + 1 ≤ rSec := Nat.succ_le_of_lt hh
    have hRs := regime_head_of_le_regimeRun (stepRegime Sec (s + 1)) T y
      (r + 1) (Nat.succ_pos r) hi
    have hLev := (hLevel (r + 1)).trans hRs.1
    have hRp : stepRegime P (s + 1) (head T (r + 1)) ((tail T (r + 1)).proj y) :=
      ⟨hLev, fun hSpecial => hRs.2
        (positive_normal_special_of_padded Q hQ (head T (r + 1)) (hTest (r + 1)) _
          (hLev ▸ Nat.succ_pos s) hSpecial)⟩
    exact not_regime_head_regimeRun (stepRegime P (s + 1)) T y
      (hh.trans_le (regimeRun_le_length (stepRegime Sec (s + 1)) T y)) hRp
  refine ⟨hLe, ?_⟩
  constructor
  · intro hEq i hi hri
    exact (regime_head_of_le_regimeRun (stepRegime Sec (s + 1)) T y i hi (hEq.symm ▸ hri)).2
  · intro hNonspecial
    apply le_antisymm hLe
    by_contra! hh
    have hi : rSec + 1 ≤ r := Nat.succ_le_of_lt hh
    have hRp := regime_head_of_le_regimeRun (stepRegime P (s + 1)) T y
      (rSec + 1) (Nat.succ_pos rSec) hi
    exact not_regime_head_regimeRun (stepRegime Sec (s + 1)) T y
      (hh.trans_le (regimeRun_le_length (stepRegime P (s + 1)) T y))
      ⟨(hLevel (rSec + 1)).symm.trans hRp.1,
        hNonspecial (rSec + 1) (Nat.succ_pos rSec) hi⟩

/-- For a strict shortening of the section run, the preceding stage of
that run is an actual padded test prefix where the projected endpoint
is padded-nonspecial and section-special at the original positive
level. -/
theorem positive_normal_section_run_cutoff {n s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hStrict : regimeRun (stepRegime (sectionMarked Q) (s + 1)) T y <
      regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let rSec := regimeRun (stepRegime Sec (s + 1)) T y
    let i := rSec + 1
    let H := head T i
    let p := (tail T i).proj y
    IsGeoTestTower P H ∧ stepRegime P (s + 1) H p ∧ IsSpecial Sec H p := by
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let rSec := regimeRun (stepRegime Sec (s + 1)) T y
  let i := rSec + 1
  let H := head T i
  let p := (tail T i).proj y
  have hRp : stepRegime P (s + 1) H p := regime_head_of_le_regimeRun
    (stepRegime P (s + 1)) T y i (Nat.succ_pos rSec) (Nat.succ_le_of_lt hStrict)
  have hH := ((isGeoTestTower_iff_head_tail P T i).mp hT).1
  have hRSec : ¬ stepRegime Sec (s + 1) H p :=
    not_regime_head_regimeRun (stepRegime Sec (s + 1)) T y
      (hStrict.trans_le (regimeRun_le_length (stepRegime P (s + 1)) T y))
  have hLevel : level Sec H p = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (show P.E = Sec.E from rfl) H p).symm.trans hRp.1
  exact ⟨hH, hRp, not_not.mp fun hNS => hRSec ⟨hLevel, hNS⟩⟩

private theorem adjacent_split_step {n : ℕ} {X : CMfd.{0} n} :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y) (j : ℕ), j < T.length →
      ∃ (C : Set (split T (j + 1)).1) (π : (split T j).1 → (split T (j + 1)).1)
        (hπ : IsBlowupAlong n C π),
        head T j = BlowupTower.step (head T (j + 1)) C π hπ ∧
        ∀ y : Y, π ((tail T j).proj y) = (tail T (j + 1)).proj y
  | _, .refl, _, hj => (Nat.not_lt_zero _ hj).elim
  | _, .step T C π hπ, 0, _ => by
    cases T <;> exact ⟨C, π, hπ, rfl, fun _ => rfl⟩
  | _, .step T C π hπ, j + 1, hj => by
    have hj' : j < T.length := Nat.lt_of_succ_lt_succ hj
    obtain ⟨D, τ, hτ, hHead, hProj⟩ := adjacent_split_step T j hj'
    exact ⟨D, τ, hτ, hHead, fun y => hProj (π y)⟩

/-- A shorter section run at a section-nonspecial endpoint starts
immediately after an actual blowup whose centre contains the preceding
special point. Both consecutive prefixes and their projections are
the literal splits of the original history. -/
theorem positive_normal_section_restart_centre {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y)
    (hStrict : regimeRun (stepRegime (sectionMarked Q) (s + 1)) T y <
      regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y) :
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime Sec (s + 1)) T y
    let H := head T (r + 1)
    let p := (tail T (r + 1)).proj y
    ∃ (C : Set (split T (r + 1)).1) (π : (split T r).1 → (split T (r + 1)).1)
      (hπ : IsBlowupAlong (n + 1) C π),
      head T r = BlowupTower.step H C π hπ ∧ π ((tail T r).proj y) = p ∧ p ∈ C := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let r := regimeRun (stepRegime Sec (s + 1)) T y
  let H := head T (r + 1)
  let p := (tail T (r + 1)).proj y
  have hLt : r < T.length :=
    hStrict.trans_le (regimeRun_le_length (stepRegime P (s + 1)) T y)
  obtain ⟨C, π, hπ, hHead, hProj⟩ := adjacent_split_step T r hLt
  have hCut := positive_normal_section_run_cutoff Q (s := s) T hT y hStrict
  have hAfter : ¬ IsSpecial Sec (head T r) ((tail T r).proj y) := by
    by_cases hr : r = 0
    · rw [hr]
      cases T <;> exact hSecNS
    · exact (regime_head_of_le_regimeRun (stepRegime Sec (s + 1)) T y r
        (Nat.pos_of_ne_zero hr) le_rfl).2
  have hS : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hCut.1
  have hBar := ((bar_local_any_boundary (X := X) Sec hS).wEquiv.2 H).1.mp hST
  refine ⟨C, π, hπ, hHead, hProj y, ?_⟩
  by_contra hOff
  rw [hHead] at hAfter
  have hOff' : π ((tail T r).proj y) ∉ C := (hProj y).symm ▸ hOff
  have hSpecial : IsSpecial Sec H (π ((tail T r).proj y)) := (hProj y).symm ▸ hCut.2.2
  exact hAfter ((isSpecial_step_iff_of_notMem Sec hS.isWellFormed.isClosedSubmanifold_N
    hS.isWellFormed.isCoherent hS.isWellFormed.isSNCDivisor.1 H hBar C π hπ hOff').2 hSpecial)

private theorem nonspecial_step_value {n k q : ℕ} {X Y : CMfd.{0} n}
    {Λ : Type} [LinearOrder Λ] (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} n q Λ)
    (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (hMax : IsMaximalOrderAlong P.N P.ideal P.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked P) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (barMarked P) T).cosupp)
    (hNS : ¬ IsSpecial P T y) :
    let v := ofLex (Seq.StepOneValueMasked.stepOneInvM R P T y)
    v.1 = level P T y ∧ v.2 ≠ ⊤ := by
  have hFinite := Seq.StepOneValueMasked.lowerValueL_ne_top P R hP.isWellFormed hP.one_le_d
    hn hMax (lowerMarkedM P) T hT hy hNS
  refine ⟨Seq.StepOneValueMasked.stepOneInvL_fst R P (lowerMarkedM P) T y, ?_⟩
  change (ofLex (Seq.StepOneValueMasked.stepOneInvL R P (lowerMarkedM P) T y)).2 ≠ ⊤
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R P (lowerMarkedM P) T hNS]
  exact hFinite

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem native_special_values {n k s qa qb : ℕ} {U : Opens (ComplexModel n)}
    {Λ Γ : Type} [LinearOrder Λ] [LinearOrder Γ]
    (RP : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} (n + 1) qa Λ)
    (RN : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} n qb Γ)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (hSpecial : IsSpecial (sectionMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV))
      (z : nativeManifold (Nat.le_succ n) V hV) (hZero : IsClosed (zeroPlane U)),
      Lift (Nat.le_succ n) (zeroPlane U) hZero (zeroPlane_regular U)
        (sectionMarked Q).E T V hVc hV N ∧ z.val = y ∧
      regimeRun (stepRegime B (s + 1)) N z ≤ regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y ∧
      let v := ofLex (Seq.StepOneValueMasked.stepOneInvM RP
        (properNormalMarked Q) T y)
      v.1 = s + 1 ∧ v.2 ≠ ⊤ ∧
        Seq.StepOneValueMasked.stepOneInvM RN B N z =
          toLex (s + 1, (⊤ : WithTop Γ)) := by
  classical
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hBar := bar_local_any_boundary (X := X) P hP
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    (hBar.wEquiv.2 T).2 hT ▸ hy
  obtain ⟨V, hVc, hV, N, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ T hT
  have hyV : y ∈ V := by
    rw [hLift.carrier]
    exact bar_cosupport_subset_strict_zeroPlane Q hQ T hT hyBar
  let z : nativeManifold (Nat.le_succ n) V hV := ⟨y, hyV⟩
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d
    (T := T) (V := V) (Q := N) hLift
  have hLevelSec : level Sec T y = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (show P.E = Sec.E from rfl) T y).symm.trans hLevel
  have hLevelNative : level B N z = s + 1 := (hChron.2.2.1 z).1.symm.trans hLevelSec
  have hSpecialNative : IsSpecial B N z := (hChron.2.2.1 z).2.mp hSpecial
  have hClock : regimeRun (stepRegime Sec (s + 1)) T y = regimeRun (stepRegime B (s + 1)) N z :=
    hChron.2.2.2.2 (s + 1) z
  have hRun : regimeRun (stepRegime B (s + 1)) N z ≤ regimeRun (stepRegime P (s + 1)) T y :=
    hClock ▸ (positive_normal_section_run Q hQ (s := s) T hT y).1
  have hVal := nonspecial_step_value (X := X) (Y := Y) (Nat.succ_pos n) RP P hP
    (properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent) T ((hBar.wEquiv.2 T).1.mp hT)
    y hyBar hNS
  refine ⟨V, hVc, hV, N, z, _, hLift, rfl, hRun, hVal.1.trans hLevel, hVal.2, ?_⟩
  change Seq.StepOneValueMasked.stepOneInvL RN B (lowerMarkedM B) N z =
    toLex (s + 1, (⊤ : WithTop Γ))
  rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ B _ N hSpecialNative, hLevelNative]

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual lifted history, a section-special, padded-nonspecial
endpoint reads the native top branch and a finite padded branch at the
same positive original level. -/
theorem positive_normal_native_special_values {n k s : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (hSpecial : IsSpecial (sectionMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV))
      (z : nativeManifold (Nat.le_succ n) V hV) (hZero : IsClosed (zeroPlane U)),
      Lift (Nat.le_succ n) (zeroPlane U) hZero (zeroPlane_regular U)
        (sectionMarked Q).E T V hVc hV N ∧ z.val = y ∧
      regimeRun (stepRegime B (s + 1)) N z ≤ regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y ∧
      let v := ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k)
        (properNormalMarked Q) T y)
      v.1 = s + 1 ∧ v.2 ≠ ⊤ ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (Nat.pred k)) B N z =
          toLex (s + 1, (⊤ : WithTop (ValTy (Nat.pred k)))) := native_special_values (invFamily (Nat.succ_pos n) k) (invFamily hn (Nat.pred k))
  Q hQ T hT y hy hLevel hNS hSpecial

end

end Hironaka.HironakaG1PositiveNormalChronology
