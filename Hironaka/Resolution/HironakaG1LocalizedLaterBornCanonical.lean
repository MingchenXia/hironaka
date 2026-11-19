import Hironaka.Resolution.HironakaG1BornSelectedCompanionCanonical
import Hironaka.Resolution.HironakaG1ActualLaterCommonTangent

/-! Exact nested marks and original canonicality on a localized common companion reference. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Classical
namespace Hironaka.HironakaG1LocalizedLaterBornCanonical

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneLowerDomain TangentDirectionAlong DivisorExponentAlong BoundaryCount
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterLocusAlong RelativePrincipalizationSpan
  HomogenizedIdealAlong CoefficientIdealRestriction HironakaG8LocalHistory
  HironakaG1BornSelectedCompanionCanonical HironakaG1RecursiveMemberValueTransport

private theorem positive_special_of_larger_carrier {n k l : ℕ} {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (hRJ : R.N ⊆ J.N) (a : X)
    (hPos : 0 < level J (.refl : BlowupTower X X) a)
    (hS : IsSpecial J (.refl : BlowupTower X X) a) :
    IsSpecial R (.refl : BlowupTower X X) a := by
  let I : BlowupTower X X := .refl
  have hOrig := HironakaG8MemberLoci.origMembers_eq_of_E_eq hClass.wEquiv.1 I
  have hLev := HironakaG8MemberLoci.level_eq_of_E_eq hClass.wEquiv.1 I a
  have hCos : (barMarked J).cosupp = (barMarked R).cosupp :=
    (cosupp_barMarked J hJ.isWellFormed hJ.one_le_d).trans
      (hClass.cosupp_eq_base.trans (cosupp_barMarked R hR.isWellFormed hR.one_le_d).symm)
  rcases hS with ⟨h0, _⟩ | ⟨hP, hMem⟩
  · exact (Nat.ne_of_gt hPos h0).elim
  · refine Or.inr ⟨hLev ▸ hP, ?_⟩
    change a ∈ MemberInterLocusAlong.memberInterLocus R.N (origMembers R I) (barMarked R).cosupp
    rw [← hOrig, ← hCos]
    exact ⟨hMem.1, hMem.2.mono fun _ hz hzR hzE => hz (hRJ hzR) hzE⟩

private theorem initial_level_pullback_open {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (W : Opens X) (a : W) :
    level (MarkedIdeal.pullback (Subtype.val : W → X) P)
      (.refl : BlowupTower (CMfd.of (n := n) W) (CMfd.of (n := n) W)) a =
      level P (.refl : BlowupTower X X) a.val := by
  simp only [level, origMembers, geoTransformAlong_refl]
  change boundaryCount ((P.E.map ((Subtype.val : W → X) ⁻¹' ·)).take
    (P.E.map ((Subtype.val : W → X) ⁻¹' ·)).length) a =
      boundaryCount (P.E.take P.E.length) a.val
  rw [List.take_length, List.take_length, boundaryCount_map]
  rfl

/-- Positive specialness is unchanged on any literal open pullback,
using only ambient coherence and the positive native mark. -/
theorem initial_positive_special_pullback_open_iff {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) (hd : 1 ≤ P.d) (W : Opens X) (a : W)
    (hPos : 0 < level P (.refl : BlowupTower X X) a.val) :
    let A := CMfd.of (n := n) W
    let P' := MarkedIdeal.pullback (M' := A) (Subtype.val : W → X) P
    IsSpecial P' (.refl : BlowupTower A A) a ↔ IsSpecial P (.refl : BlowupTower X X) a.val := by
  intro A P'
  let T : BlowupTower X X := .refl
  let T' : BlowupTower A A := .refl
  have hLvl : level P' T' a = level P T a.val := initial_level_pullback_open P W a
  have hOrig : origMembers P' T' = (origMembers P T).map ((Subtype.val : W → X) ⁻¹' ·) := by
    simp only [origMembers]
    change (P.E.map ((Subtype.val : W → X) ⁻¹' ·)).take
      (P.E.map ((Subtype.val : W → X) ⁻¹' ·)).length =
      (P.E.take P.E.length).map ((Subtype.val : W → X) ⁻¹' ·)
    simp
  have hCos : (barMarked P').cosupp = (Subtype.val : W → X) ⁻¹' (barMarked P).cosupp := by
    rw [cosupp_barMarked P' (IsWellFormed.pullback_val hP W) hd,
      cosupp_pullback_val P
        (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hP.isCoherent hf) W,
      cosupp_barMarked P hP hd]
  dsimp [T, T'] at hLvl hOrig
  unfold IsSpecial
  simp only [hLvl, Nat.ne_of_gt hPos, false_and, false_or, geoTransformAlong_refl, hOrig, hCos]
  exact and_congr_right fun _ => mem_memberInterLocus_preimage_iff (Subtype.val : W → X)
    (W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq a) P.N (origMembers P T) (barMarked P).cosupp

/-- The literal next Step One records and prescribed coefficient contact on
a common subwindow, with their native marks and original canonicality. -/
abbrev LocalizedBornWitness {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (a : X) (u : X → ℂ) : Prop :=
  let I : BlowupTower X X := .refl
  ∃ V : Opens X, a ∈ V ∧ V ≤ maskA J I a ∧ V ≤ maskA R I a ∧
    let A := CMfd.of (n := n) V
    let K := positiveMemberOn J I a V
    let S := positiveMemberOn R I a V
    let Cut := withN (coeffMarkedAlong K) (K.N ∩ {z : V | u z.val = 0})
    IsInvDomain (k - 1) K ∧
    IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : V → X)) ∧
    Cut.N = S.N ∧ Cut.E = S.E ∧ LocWPEquiv (X := A) Cut S ∧
    K.d = (coeffMarkedAlong (barMarked J)).d ∧
    S.d = (coeffMarkedAlong (barMarked R)).d ∧
    Cut.d = (coeffMarkedAlong K).d ∧
    IsInvDomain (l - 1) Cut ∧ IsInvDomain (l - 1) S ∧
    (∀ F ∈ Cut.E, ∀ z ∈ Cut.cosupp, z ∈ F →
      S.d * divExpAlong n Cut.N Cut.ideal F z =
        Cut.d * divExpAlong n S.N S.ideal F z) ∧
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical Cut ((invFamily hn (l - 1)).inv Cut) T ↔
        IsCanonical S ((invFamily hn (l - 1)).inv S) T

set_option maxHeartbeats 1000000 in
/-- The born-positive branch uses only the actual localized companion and
supported reference. Its companion nonspeciality follows from supported
nonspeciality, using the exact prescribed zero trace. -/
theorem localized_born_witness_of_supported_nonspecial {n k l b : ℕ}
    (hn : 0 < n) {X : CMfd.{0} n} (J R : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (a : X) (ha : a ∈ R.N) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {z | u z = 0} = R.N)
    (hl : level J (.refl : BlowupTower X X) a = b + 1)
    (hNS : ¬ IsSpecial R (.refl : BlowupTower X X) a) :
    LocalizedBornWitness (k := k) (l := l) hn J R a u := by
  let I : BlowupTower X X := .refl
  have hRJ : R.N ⊆ J.N := fun z hz => (hTrace ▸ hz).1
  have hPos : 0 < level J I a := by rw [hl]; omega
  have hNSJ : ¬ IsSpecial J I a := fun hS =>
    hNS (positive_special_of_larger_carrier J R hJ hR hClass hRJ a hPos hS)
  have hu' : IsTangentDirectionAlong J.N J.ideal J.d (⊤ : Opens X) u := hu
  have hTrace' : J.N ∩ {z | u z = 0} ∩ (⊤ : Opens X) = R.N ∩ (⊤ : Opens X) := by
    rw [hTrace]
  obtain ⟨V, haV, _, hVJ, hVR, hK, hKu, hN, hE, hCS, hC, hS, hExp, hCan⟩ :=
    exists_born_selected_contact_canonical_of_supported_nonspecial hn J R hJ hR hClass
      hRJ a ha hl hNSJ hNS ⊤ trivial u hu' hTrace'
  exact ⟨V, haV, hVJ, hVR, hK, hKu, hN, hE, hCS, rfl, rfl, rfl, hC, hS, hExp, hCan⟩

open BlowupTowerSplit StepOneRegime StepOneValueMasked GeneralValue NonmonomialOrderTail
  InvDomainMemberRestriction HironakaG1ActualLaterCommonTangent HironakaG8HomStable
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials

set_option maxHeartbeats 1600000 in
/-- Start the next born-positive recursive branch on the actual common
reference window. No global reference domain or local weak equivalence is
required. The level and nonspeciality tests at the order-mask anchor survive
restriction to the actual common window. -/
theorem exists_actual_localized_later_born_canonical {n k s b : ℕ}
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
    let I : BlowupTower B B := .refl
    (¬ IsSpecial Sec H p) →
    (∀ a : C, a.val.val = p → level J I a = b + 1 ∧ ¬ IsSpecial R I a) →
    ∃ (a : C) (W : Opens B) (u : W → ℂ) (haW : a ∈ W), a.val.val = p ∧
      let D := CMfd.of (n := n + 1) W
      let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      LocalizedBornWitness (k := k + 1) (l := k) (Nat.succ_pos n) Jw Rw ⟨a, haW⟩ u := by
  intro X P Sec r H S p O A L C B J R I hNSS hBorn
  obtain ⟨a, W, u, haW, ha, hJw, hRw, hClass, hu, hTrace, haR, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent Q hQ T hCan y hy hl hNS hNSS
  let D := CMfd.of (n := n + 1) W
  let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
  let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
  let aw : W := ⟨a, haW⟩
  obtain ⟨hlJ, hNSR⟩ := hBorn a ha
  have hlJw : level Jw (.refl : BlowupTower D D) aw = b + 1 :=
    (initial_level_pullback_open J W aw).trans hlJ
  have hlR : level R I a = b + 1 :=
    (initial_level_pullback_open R W aw).symm.trans
      ((HironakaG8MemberLoci.level_eq_of_E_eq hClass.wEquiv.1 (.refl : BlowupTower D D) aw).symm.trans hlJw)
  have hR : R.IsWellFormed := by
    have hP := properNormalMarked_isInvDomain Q hQ
    have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
    have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily (Nat.succ_pos n) (k + 1))
      P hP hMax (Nat.succ_pos n) T hCan).2.1
    have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
    let BS := geoTransformAlong (barMarked Sec) H
    have hSec : IsInvDomain (k + 1) Sec := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
    have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hHeadTest
    have hBST := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
    have hBS : BS.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked Sec hSec.isWellFormed) H hBST
    exact IsWellFormed.pullback_val (IsWellFormed.pullback_val
      (isWellFormed_memberRestrict (Nat.succ_pos n) hBS _) O) C
  have hNSRw : ¬ IsSpecial Rw (.refl : BlowupTower D D) aw := fun hSp =>
    hNSR ((initial_positive_special_pullback_open_iff R hR hRw.one_le_d W aw
      (hlR ▸ Nat.succ_pos b)).mp hSp)
  exact ⟨a, W, u, haW, ha, localized_born_witness_of_supported_nonspecial
    (Nat.succ_pos n) Jw Rw hJw hRw hClass aw haR u hu hTrace hlJw hNSRw⟩

end Hironaka.HironakaG1LocalizedLaterBornCanonical
