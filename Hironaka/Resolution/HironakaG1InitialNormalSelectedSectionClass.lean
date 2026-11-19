import Hironaka.Resolution.HironakaG11InvCommonMark
import Hironaka.Resolution.HironakaG1InitialSelectedNormalOrder
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaG8MemberWeakEquiv
import Hironaka.Resolution.HironakaNormalCrossingsActualCentreSupport

/-! The initial prescribed normal contact and the literal supported selected
record on an open of the same physical ambient manifold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialNormalSelectedSectionClass
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  ResolutionInvariantSpec HomogenizedIdealAlong CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterLocusAlong InvDomainMemberRestriction InvDomainRebase
  HironakaG8MemberWeakEquiv HironakaNormalCrossingsActualCentreSupport
  HironakaG8LocalHistory HironakaG8HomStable HironakaCoherentTransformExtension HironakaG8LocalContact
  HironakaG1InitialSelectedNormalOrder HironakaG1ProperNormalOriginalTest
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  BoundaryCount StepOneValue ContactStageKept ContactEquivalenceAlong ContactEquivalenceStage
  TangentDirectionAlong HomogenizedEquivalence RelativePrincipalizationSpan
  HironakaActualPowerBoundaryExponents HironakaG11InvCommonMark

private theorem centresIn_carrier_of_test {n : ℕ} {X : CMfd.{0} n} (A : MarkedIdeal n X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T → CentresIn A.N T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, hT => by
    refine ⟨centresIn_carrier_of_test A T hT.1, ?_⟩
    rw [← N_geoTransformAlong]
    exact fun _ hx => (hT.2.2.1 hx).1

private theorem member_selected_wEquiv_of_nested {n : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) {A B : MarkedIdeal n X} (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d) (hN : B.N ⊆ A.N) (hW : WEquiv A B)
    (p : X) :
    WEquiv (memberRestrict A (membersThrough A.E A.E p))
      (memberRestrict B (membersThrough B.E B.E p)) := by
  let D := {z : X | ∀ F ∈ A.E, p ∈ F → z ∈ F}
  let L := memberRestrict A (membersThrough A.E A.E p)
  let S := memberRestrict B (membersThrough B.E B.E p)
  have hLN : L.N = A.N ∩ D := by
    rw [show L.N = A.N ∩ memberInter A.E (membersThrough A.E A.E p) from rfl,
      memberInter_membersThrough (fun _ h => h)]
  have hSN : S.N = B.N ∩ D := by
    rw [show S.N = B.N ∩ memberInter B.E (membersThrough B.E B.E p) from rfl,
      memberInter_membersThrough (fun _ h => h), ←hW.1]
  have hLE : L.E = S.E := by
    simp only [L, S, memberRestrict_membersThrough_E, hW.1]
  refine ⟨hLE, fun T => ?_⟩
  obtain ⟨hLT, hLCos⟩ := memberRestrict_test_dictionary hn A hA hdA (membersThrough A.E A.E p) T
  obtain ⟨hST, hSCos⟩ := memberRestrict_test_dictionary hn B hB hdB (membersThrough B.E B.E p) T
  have hStrictA (h : IsGeoTestTower A T) :
      strictAlong T L.N = (geoTransformAlong A T).N ∩
        {z | ∀ F ∈ A.E, p ∈ F → z ∈ strictAlong T F} := by
    rw [hLN]
    exact strictAlong_inter_forall_mem A hA (fun _ hF => hF) (p ∈ ·) T h
  have hStrictB (h : IsGeoTestTower B T) :
      strictAlong T S.N = (geoTransformAlong B T).N ∩
        {z | ∀ F ∈ A.E, p ∈ F → z ∈ strictAlong T F} := by
    rw [hSN]
    change strictAlong T (B.N ∩ {z | ∀ F ∈ A.E, p ∈ F → z ∈ F}) = _
    rw [hW.1]
    exact strictAlong_inter_forall_mem B hB (fun _ hF => hF) (p ∈ ·) T h
  have hTests : IsGeoTestTower L T ↔ IsGeoTestTower S T := by
    constructor
    · intro hL
      obtain ⟨hAT, hCentres⟩ := hLT.mp hL
      have hBT := ((hW.2 T).1).mp hAT
      have hBoth : CentresIn S.N T := by
        have hAll : ∀ {Z : CMfd.{0} n} (R : BlowupTower X Z),
            IsGeoTestTower A R → IsGeoTestTower B R → CentresIn L.N R → CentresIn S.N R := by
          intro Z R
          induction R with
          | refl => intro _ _ _; trivial
          | @step Y Z R C π hπ ih =>
            intro hA' hB' hL'
            refine ⟨ih hA'.1 hB'.1 hL'.1, ?_⟩
            intro c hc
            have hL'' := hL'.2 hc
            rw [hLN, strictAlong_inter_forall_mem A hA (fun _ hF => hF) (p ∈ ·) R hA'.1] at hL''
            rw [hSN]
            change c ∈ strictAlong R (B.N ∩ {z | ∀ F ∈ A.E, p ∈ F → z ∈ F})
            rw [hW.1, strictAlong_inter_forall_mem B hB (fun _ hF => hF) (p ∈ ·) R hB'.1]
            exact ⟨(hB'.2.2.1 hc).1, by simpa only [← hW.1] using hL''.2⟩
        exact hAll T hAT hBT hCentres
      exact hST.mpr ⟨hBT, hBoth⟩
    · intro hS
      obtain ⟨hBT, hCentres⟩ := hST.mp hS
      exact hLT.mpr ⟨((hW.2 T).1).mpr hBT,
        centresIn_mono (show S.N ⊆ L.N by rw [hSN, hLN]; exact inter_subset_inter_left _ hN)
          T hCentres⟩
  refine ⟨hTests, fun hL => ?_⟩
  have hS := hTests.mp hL
  have hAT := (hLT.mp hL).1
  have hBT := (hST.mp hS).1
  rw [hLCos hL, hSCos hS, hStrictA hAT, hStrictB hBT, (hW.2 T).2 hAT]
  ext z
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hz, _, hc⟩
    exact ⟨hz, hz.1, hc⟩
  · rintro ⟨hz, _, hc⟩
    exact ⟨hz, ((hW.2 T).2 hAT).symm ▸ hz |>.1, hc⟩

set_option maxHeartbeats 1000000 in
/-- The prescribed normal homogenized coefficient contact of the actual
initial positive padded cut and the actual supported selected record have
the same weak tests and transformed cosupports on a common anchor window.
Their literal coefficient marks are retained. When both records lie in
the invariant domain, their opposite powers have one positive mark. -/
theorem initial_normal_selected_section_wEquiv {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : 0 < boundaryCount (properNormalMarked Q).E p)
    (O : Opens (productOpen U)) (hpO : p ∈ O) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let A := barMarked (X := X) (properNormalMarked Q)
    let B := barMarked (X := X) (supportedNormalMarked Q)
    let L := memberRestrict A (membersThrough A.E A.E p)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let K := contactMarkedKept (X := X) L (relativeNormalCoordinate U) (.refl : BlowupTower X X) O
    let R := MarkedIdeal.pullback (Subtype.val : O → X) S
    WEquiv (X := CMfd.of (n := n+1) O) K R ∧ K.N = R.N ∧ K.E = R.E ∧
      R.d = L.d ∧ K.d = (coeffMarkedAlong (barMarked (X := X) L)).d ∧
      ∀ {l₁ l₂ : ℕ}, IsInvDomain l₁ K → IsInvDomain l₂ R →
        WEquiv (X := CMfd.of (n := n+1) O)
          (powerMarked (X := CMfd.of (n := n+1) O) K R.d) (powerMarked (X := CMfd.of (n := n+1) O) R K.d) ∧
        (powerMarked (X := CMfd.of (n := n+1) O) K R.d).d = (powerMarked (X := CMfd.of (n := n+1) O) R K.d).d := by
  intro X A B L S K R
  let P := properNormalMarked Q
  let M := supportedNormalMarked Q
  have hP := properNormalMarked_isInvDomain Q hQ
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hA := isInvDomain_barMarked (X := X) P hP
  have hB := isInvDomain_barMarked (X := X) M hM
  obtain ⟨hL, _, _, hu, _⟩ := initial_selected_normal_data Q hQ p hp
  have hAB : LocWPEquiv (X := X) A B :=
    (bar_local_any_boundary (X := X) P hP).symm.trans
      (hPM.trans (bar_local_any_boundary (X := X) M hM))
  let AO := MarkedIdeal.pullback (Subtype.val : O → X) A
  let BO := MarkedIdeal.pullback (Subtype.val : O → X) B
  have hAO := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hA.isWellFormed O
  have hBO := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hB.isWellFormed O
  have hN : B.N ⊆ A.N := fun _ h => h.1
  have hComp := member_selected_wEquiv_of_nested (X := CMfd.of (n := n+1) O)
    (Nat.succ_pos n) hAO hBO hA.one_le_d hB.one_le_d (preimage_mono hN)
    (hAB.restrict O).wEquiv (⟨p,hpO⟩ : O)
  have hLO := pullback_val_memberRestrict_membersThrough hA.isWellFormed hA.one_le_d
    (fun _ h => h) O (⟨p,hpO⟩ : O)
  have hSO := pullback_val_memberRestrict_membersThrough hB.isWellFormed hB.one_le_d
    (fun _ h => h) O (⟨p,hpO⟩ : O)
  change WEquiv (X := CMfd.of (n := n+1) O)
    (memberRestrict AO (membersThrough AO.E (A.E.map ((Subtype.val : O → X) ⁻¹' ·)) (⟨p,hpO⟩ : O)))
    (memberRestrict BO (membersThrough BO.E (B.E.map ((Subtype.val : O → X) ⁻¹' ·)) (⟨p,hpO⟩ : O))) at hComp
  have hComp' : WEquiv (X := CMfd.of (n := n+1) O)
      (MarkedIdeal.pullback (Subtype.val : O → X) L) R := by
    change MarkedIdeal.pullback (Subtype.val : O → X) L = _ at hLO
    change R = _ at hSO
    rw [hLO, hSO]
    exact hComp
  have hBar := wEquiv_pullback_val_coeffHomAlong (X := X) L hL.isWellFormed.isClosedSubmanifold_N
    hL.isWellFormed.isCoherent hL.one_le_d O
  let J := barMarked (X := X) L
  have huO : IsTangentDirectionAlong L.N L.ideal L.d O (relativeNormalCoordinate U) :=
    HironakaG8LocalContact.IsTangentDirectionAlong.mono_open hu O.isOpen (subset_univ _)
  have hK' : WEquiv (X := CMfd.of (n := n+1) O)
      (MarkedIdeal.pullback (Subtype.val : O → X) J) K :=
    wEquiv_stage_coeffHomAlong L hL.isWellFormed.isClosedSubmanifold_N
      hL.isWellFormed.isCoherent hL.one_le_d O huO (.refl : BlowupTower X X) trivial
  have hWR : WEquiv (X := CMfd.of (n := n+1) O) K R :=
    hK'.symm.trans (hBar.trans hComp')
  have hE : A.E = B.E := rfl
  have hCarrier : L.N ∩ {z | relativeNormalCoordinate U z = 0} = S.N := by
    rw [show L.N = A.N ∩ memberInter A.E (membersThrough A.E A.E p) from rfl,
      show S.N = B.N ∩ memberInter B.E (membersThrough B.E B.E p) from rfl, ←hE]
    have hBase : A.N ∩ {z | relativeNormalCoordinate U z = 0} = B.N := normal_contact_carrier Q
    rw [←hBase]
    ext z
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩, fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
  refine ⟨hWR, ?_, hWR.1, rfl, rfl, ?_⟩
  · change (Subtype.val : O → X) ⁻¹' (L.N ∩ {z | relativeNormalCoordinate U z = 0}) =
      (Subtype.val : O → X) ⁻¹' S.N
    rw [hCarrier]
  · intro l₁ l₂ hDomK hDomR
    have hPowK := wEquiv_powerMarked (X := CMfd.of (n := n+1) O) K hDomK hDomR.one_le_d
    have hPowR := wEquiv_powerMarked (X := CMfd.of (n := n+1) O) R hDomR hDomK.one_le_d
    exact ⟨hPowK.symm.trans (hWR.trans hPowR), Nat.mul_comm _ _⟩

end
end Hironaka.HironakaG1InitialNormalSelectedSectionClass
