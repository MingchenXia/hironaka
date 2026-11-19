import Hironaka.Resolution.HironakaG1ProperNormalInitialRegime
import Hironaka.Resolution.HironakaG1IndependentContactClassData

/-! Genuine ORIGINAL zero-phase to prescribed normal lower CAN.
Actual run/head/tail and transformed INITIAL bar remain literal.
Blueprint FIRST: hironaka-g1-proper-normal-zero-phase.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalZeroPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  StepOneLowerDomain TangentDirectionAlong ContactStageKept ContactStageInvDomain
  HironakaG1OriginalContactClassAtStage HironakaG1IndependentContactClassData
  HironakaG1CoefficientCarrierClassData HironakaG1CoefficientBarClassData
  HironakaG1OriginalInvariantClassFunctorial HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8HomStable HironakaG8GapNormalizedExponent HironakaG1ChosenCommonContactClassData
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  CoefficientIdealRestriction DivisorExponentAlong InvDomainTowerAlong
open HomogenizedGlueingTower (strictAlong)

/-- Ordinary GLOBAL tangent data, with all lower native metadata derived
on the actual original own mask. No desired lower-output packet. -/
theorem global_prescribed_contact_data {n k : ℕ} (hn : 0<n) {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (u : X→ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y∈(geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y) :
    y∈maskB J T y ∧
      let O:=maskB J T y
      let A:=contactMarkedKept J (tangentChoice J (T.proj y)).2 T O
      let B:=contactMarkedKept J u T O
      IsInvDomain (k-1) A ∧ IsInvDomain (k-1) B ∧
        LocWPEquiv (X := CMfd.of (n := n) O) A B ∧ SameCarrierDim (X := CMfd.of (n := n) O) A B ∧
        A.ideal=B.ideal ∧ A.E=B.E ∧ A.d=B.d ∧ ExpAgree (X := CMfd.of (n := n) O) A B := by
  let O:=maskB J T y
  let A:=contactMarkedKept J (tangentChoice J (T.proj y)).2 T O
  let B:=contactMarkedKept J u T O
  have hTBar : IsGeoTestTower (barMarked J) T := (((bar_local_any_boundary J hJ).wEquiv).2 T).1.mp hT
  have hOut : y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d :=
    fun h=>hReg.2 (Or.inl ⟨hReg.1,h⟩)
  have hyO:=StepOneLowerDomain.mem_maskB J hJ.isWellFormed hJ.one_le_d hMax T hTBar hy hReg.1 hOut
  obtain ⟨_hOwnPoint,huOwn⟩:=tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMax T hTBar hy)
  let UOwn : Opens X:=⟨(tangentChoice J (T.proj y)).1,huOwn.isOpen⟩
  have hOOwn : (O : Set Y)⊆openPreimage T UOwn:=fun _ hz=>(interior_subset hz).1
  have hOGlobal : (O : Set Y)⊆openPreimage T (⊤ : Opens X):=fun _ _=>mem_univ _
  have hA : IsInvDomain (k-1) A :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE UOwn huOwn
      T hTBar O hOOwn (fun _ hz _=>(interior_subset hz).2.2)
      (fun H hH _ hz _=>(interior_subset hz).2.1 H hH)
  have hB : IsInvDomain (k-1) B :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE (⊤ : Opens X) hu
      T hTBar O hOGlobal (fun _ hz _=>(interior_subset hz).2.2)
      (fun H hH _ hz _=>(interior_subset hz).2.1 H hH)
  have hOwn:=original_bar_local_to_reference_contact J J hJ hJ rfl (LocEquiv.refl Kinds.wp J)
    UOwn _ huOwn T hT O hOOwn
  have hOther:=original_bar_local_to_reference_contact J J hJ hJ rfl (LocEquiv.refl Kinds.wp J)
    (⊤ : Opens X) u hu T hT O hOGlobal
  have hL : LocWPEquiv (X := CMfd.of (n := n) O) A B:=hOwn.symm.trans hOther
  have hDim : SameCarrierDim (X := CMfd.of (n := n) O) A B := by
    intro x hx j
    have hxB : x∈B.cosupp:=hL.cosupp_eq_base ▸ hx
    have hxA := A.cosupp_subset_N hx
    have hxB' := B.cosupp_subset_N hxB
    obtain ⟨a,haN,haS⟩:=exists_regularAtDim_strictAlong_stage J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d UOwn huOwn
      T hT (hOOwn x.property) hxA
    obtain ⟨b,hbN,hbS⟩:=exists_regularAtDim_strictAlong_stage J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d (⊤ : Opens X) hu
      T hT (hOGlobal x.property) hxB'
    have hab : a=b:=Nat.add_right_cancel (RegularPointDimension.eq_of_regularAtDim haN hbN)
    have hAx : RegularAtDim (n := n) A.N x a:=AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr haS
    have hBx : RegularAtDim (n := n) B.N x b:=AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hbS
    constructor
    · intro h
      rw [←RegularPointDimension.eq_of_regularAtDim hAx h,hab]
      exact hBx
    · intro h
      rw [←RegularPointDimension.eq_of_regularAtDim hBx h,←hab]
      exact hAx
  have hNorm:=normalized_exponents_of_gap_sameCarrierDim (X := CMfd.of (n := n) O) hn
    A B hA hB hL hDim (contact_hasCosupportGap J hJ T hT _ O) (contact_hasCosupportGap J hJ T hT u O)
  have hExp : ExpAgree (X := CMfd.of (n := n) O) A B := by
    intro H hH x hx hxH
    exact Nat.eq_of_mul_eq_mul_left hA.one_le_d (hNorm H hH x hx hxH)
  exact ⟨hyO,hA,hB,hL,hDim,rfl,rfl,rfl,hExp⟩

set_option maxHeartbeats 1300000 in
/-- The actual zero-level run of an original Step One canonical history
reads any prescribed global tangent on the same masked suffix. -/
theorem prescribed_contact_zero_phase {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain (k + 1) P)
    (hMax : IsMaximalOrderAlong P.N P.ideal P.d)
    (u : X → ℂ) (hu : IsTangentDirectionAlong P.N P.ideal P.d univ u)
    (T : BlowupTower X Y)
    (hCan : IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp)
    (hLevel : level P T y = 0) (hNS : ¬ IsSpecial P T y) :
    let r := regimeRun (stepRegime P 0) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskB P H p
    let A := lowerMarkedB P H p
    let B := contactMarkedKept P u H O
    ∃ hp : p ∈ O,
      IsInvDomain k A ∧ IsInvDomain k B ∧ LocWPEquiv (X := CMfd.of (n := n) O) A B ∧
      SameCarrierDim (X := CMfd.of (n := n) O) A B ∧ A.ideal = B.ideal ∧ A.E = B.E ∧ A.d = B.d ∧
      ExpAgree (X := CMfd.of (n := n) O) A B ∧
      IsCanonical A ((invFamily hn k).inv A) (restrict O S) ∧
      IsCanonical B ((invFamily hn k).inv B) (restrict O S) ∧
      (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong B (restrict O S)).cosupp ∧
      (∀ z ∈ (geoTransformAlong A (restrict O S)).cosupp,
        (invFamily hn k).inv A (restrict O S) z = (invFamily hn k).inv B (restrict O S) z) := by
  let R := invFamily hn k
  obtain ⟨hBarTest, hTest, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R P hP hMax hn T hCan
  have hyBar := hCos.symm ▸ hy
  have hLower := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (k := k + 1) P R
    hP.isWellFormed hP.one_le_d hn hMax hP.dimLE T
    ((Seq.StepOneBridge.isCanonical_iff R P hP hMax hn T).mp hCan) y hyBar hNS
  obtain ⟨hHeadReg, hHeadCos⟩ := stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hLower hHeadReg hHeadCos
  obtain ⟨hp, hA, hCanA, hCosA⟩ := hLower
  let r := regimeRun (stepRegime P 0) T y
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  have hContact := global_prescribed_contact_data hn P hP hMax u hu
    (head T r) hHeadTest ((tail T r).proj y) hHeadCos hHeadReg
  obtain ⟨_, hOwn, hB, hL, hDim, hI, hE, hd, hExp⟩ := hContact
  simp only [Nat.add_sub_cancel] at hA hOwn hB
  let O := maskB P (head T r) ((tail T r).proj y)
  have hCanon := classFunctorialFor_invFamily hn k
  have hCanB := (hCanon.canonical_iff (X := CMfd.of (n := n) O) _ _ hOwn hB hL hd hE hDim hExp _).mp hCanA
  have hLowerTest := R.isInvValue.isGeoTestTower_of_isCanonical (X := CMfd.of (n := n) O) hA _ hCanA
  have hCosLower := (hL.wEquiv.2 _).2 hLowerTest
  refine ⟨hp, hA, hB, hL, hDim, hI, hE, hd, hExp, hCanA, hCanB, ?_, ?_⟩
  · exact hCosLower ▸ hCosA
  · intro z hz
    exact hCanon.inv_eq (X := CMfd.of (n := n) O) _ _ hOwn hB hL hd hE hDim hExp _ hCanA z hz

set_option maxHeartbeats 750000 in
/-- GIVEN genuine ORIGINAL upper StepOne CAN internally gives the actual
normal-contact lower CAN on the ACTUAL zero-regime restricted tail. -/
theorem original_normal_zero_phase {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y∈(geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y=0) (hNS : ¬IsSpecial (properNormalMarked Q) T y) :
    let P:=properNormalMarked Q
    let r:=regimeRun (stepRegime P 0) T y
    let H:=head T r
    let S:=tail T r
    let p:=S.proj y
    let O:=maskB P H p
    let A:=lowerMarkedB P H p
    let B:=contactMarkedKept P (relativeNormalCoordinate U) H O
    ∃hp : p∈O,
      IsInvDomain k A ∧ IsInvDomain k B ∧ LocWPEquiv (X := CMfd.of (n := n+1) O) A B ∧
        SameCarrierDim (X := CMfd.of (n := n+1) O) A B ∧ A.ideal=B.ideal ∧ A.E=B.E ∧ A.d=B.d ∧ ExpAgree (X := CMfd.of (n := n+1) O) A B ∧
        IsCanonical A ((invFamily (Nat.succ_pos n) k).inv A) (restrict O S) ∧
        IsCanonical B ((invFamily (Nat.succ_pos n) k).inv B) (restrict O S) ∧
        (⟨y,hp⟩ : openPreimage S O)∈(geoTransformAlong B (restrict O S)).cosupp ∧
        (∀z∈(geoTransformAlong A (restrict O S)).cosupp,
          (invFamily (Nat.succ_pos n) k).inv A (restrict O S) z=
            (invFamily (Nat.succ_pos n) k).inv B (restrict O S) z) :=
  prescribed_contact_zero_phase (X := CMfd.of (n := n + 1) (productOpen U)) (Y := Y) (k := k)
    (Nat.succ_pos n) (properNormalMarked Q)
    (properNormalMarked_isInvDomain Q hQ)
    (properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent)
    (relativeNormalCoordinate U)
    (properNormalMarked_tangent Q (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d))
    T hCan y hy hLevel hNS

end
end Hironaka.HironakaG1ProperNormalZeroPhase
