import Hironaka.Resolution.HironakaG1IndependentContactClassData
import Hironaka.Resolution.HironakaG8PowerOriginalHistory
import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.Resolution.HironakaG1ScaledCompanionLocal

/-! Actual unequal-mark histories on different original contact carriers.
Blueprint FIRST: hironaka-g1-independent-contact-scaled-history.tex.
No higher recursive cut or weighted normal-padding conclusion is asserted. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1IndependentContactScaledHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen ResolutionInvariantSpec
  DivisorExponentAlong IdealWeightPowers MonomialCaseAlong NonmonomialOrderLocal
  NonmonomialOrderRegime StepOneRegime InvDomainTowerAlong HironakaG8LocalHistory
  HironakaG11InvBMClass HironakaG8LocalPower HironakaG8BornExponents HironakaG8P1Entries
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8DomainExponents HironakaG8PowerOriginalHistory
  HironakaG1IndependentContactClassData HironakaG1ChosenCommonContactClassData
  HironakaG1CoefficientCarrierClassData HironakaG1OriginalContactClassAtStage
  HironakaG8OriginalRecursiveLocal HironakaG1CoeffBarLocal HironakaG8HomStable
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactStageKept ContactIndependenceAlong
  ContactStageInvDomain CoefficientIdealRestriction TangentDirectionAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain HironakaG8SpecialLoci HironakaG8MemberLoci
open HironakaG8MixedBoundaryExponents (divExpAlong_eq_zero_of_notMem)

/-- Whole powers derive the actual same-mark class from the native
normalized exponent law, without identifying the carriers. -/
theorem common_power_class_data {n k l : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x) :
    IsInvDomain k (powerMarked P Q.d) ∧ IsInvDomain l (powerMarked Q P.d) ∧
      LocWPEquiv (powerMarked P Q.d) (powerMarked Q P.d) ∧
      (powerMarked Q P.d).d = (powerMarked P Q.d).d ∧
      SameCarrierDim (powerMarked P Q.d) (powerMarked Q P.d) ∧
      ExpAgree (powerMarked P Q.d) (powerMarked Q P.d) := by
  have hCommon := locEquiv_commonMark (κ := Kinds.wp) rfl hL hP hQ
  have hDimP : SameCarrierDim (powerMarked P Q.d) (powerMarked Q P.d) := by
    intro x hx j
    exact hDim x ((powerMarked_cosupp P hP hQ.one_le_d) ▸ hx) j
  exact ⟨powerMarked_isInvDomain P hP hQ.one_le_d, powerMarked_isInvDomain Q hQ hP.one_le_d,
    hCommon.1, hCommon.2.symm, hDimP,
    HironakaG1ScaledCompanionLocal.commonPower_expAgree_of_scaled P Q hP hQ hInitial⟩

/-- All old and born exponents scale along the SAME original history on
different carriers of equal local dimension. -/
theorem scaled_exponents_sameCarrierDim {n k l : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    ∀ H ∈ (geoTransformAlong P T).E, ∀ x ∈ (geoTransformAlong P T).cosupp, x ∈ H →
      Q.d * divExpAlong n (geoTransformAlong P T).N (geoTransformAlong P T).ideal H x =
      P.d * divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal H x := by
  obtain ⟨hPP, hQP, hCommon, hd, hDimP, hExp⟩ := common_power_class_data P Q hP hQ hL hDim hInitial
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hAP := original_power_transform P hP Q.d hQ.one_le_d T hT
  have hAQ := original_power_transform Q hQ P.d hP.one_le_d T hTQ
  have hXV := locWPEquiv_expAgree_geoTransformAlong hCommon hPP hQP hDimP hd hExp T hAP.1
  intro H hH x hx hxH
  have hHP : H ∈ (geoTransformAlong (powerMarked P Q.d) T).E := by rw [hAP.2.E_eq]; exact hH
  have hxP : x ∈ (geoTransformAlong (powerMarked P Q.d) T).cosupp := by
    rw [hAP.2.cosupp_eq, powerMarked_cosupp _ hPT hQ.one_le_d]
    exact hx
  have h := hXV H hHP x hxP hxH
  rw [divExpAlong_eq_of_restrictEquiv hAP.2, divExpAlong_eq_of_restrictEquiv hAQ.2] at h
  change divExpAlong n (geoTransformAlong P T).N (idealPow (geoTransformAlong P T).ideal Q.d) H x =
    divExpAlong n (geoTransformAlong Q T).N (idealPow (geoTransformAlong Q T).ideal P.d) H x at h
  rw [divExpAlong_idealPow hPT.isWellFormed.isClosedSubmanifold_N hPT.isWellFormed.isCoherent hQ.one_le_d,
    divExpAlong_idealPow hQT.isWellFormed.isClosedSubmanifold_N hQT.isWellFormed.isCoherent hP.one_le_d] at h
  exact h

/-- Actual normalized raw order on the same tested suffix; native marks
and distinct proper carriers remain literal. -/
theorem scaled_raw_sameCarrierDim {n k l : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (x : Y)
    (hx : x ∈ (geoTransformAlong P T).cosupp) :
    Q.d * nmOrd (geoTransformAlong P T) x = P.d * nmOrd (geoTransformAlong Q T) x := by
  obtain ⟨hPP, hQP, hCommon, hd, hDimP, hExp⟩ := common_power_class_data P Q hP hQ hL hDim hInitial
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hAP := original_power_transform P hP Q.d hQ.one_le_d T hT
  have hxP : x ∈ (geoTransformAlong (powerMarked P Q.d) T).cosupp := by
    rw [hAP.2.cosupp_eq, powerMarked_cosupp _ hPT hQ.one_le_d]
    exact hx
  have hxQ : x ∈ (geoTransformAlong Q T).cosupp := (hL.geoTransformAlong T hT).cosupp_eq_base ▸ hx
  have h := locWPEquiv_nmOrd_geoTransformAlong_eq hCommon hPP hQP hDimP hd hExp T hAP.1 hxP
  rw [nmOrd_original_power_history hn P hP hQ.one_le_d T hT ((geoTransformAlong P T).cosupp_subset_N hx),
    nmOrd_original_power_history hn Q hQ hP.one_le_d T hTQ ((geoTransformAlong Q T).cosupp_subset_N hxQ)] at h
  exact h

/-- The complete natural-indexed exponent functions, including all native
default branches, scale without a common-carrier premise. -/
theorem scaled_indexed_exponents_sameCarrierDim {n k l : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (x : Y)
    (hx : x ∈ (geoTransformAlong P T).cosupp) :
    ∀ i, Q.d * expDataAlong n (geoTransformAlong P T).N (geoTransformAlong P T).ideal
      (geoTransformAlong P T).E x i = P.d * expDataAlong n (geoTransformAlong Q T).N
        (geoTransformAlong Q T).ideal (geoTransformAlong Q T).E x i := by
  let PT := geoTransformAlong P T
  let QT := geoTransformAlong Q T
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hET : QT.E = PT.E := E_geoTransformAlong_eq hL.wEquiv.1.symm T
  have hScaled := scaled_exponents_sameCarrierDim P Q hP hQ hL hDim hInitial T hT
  intro i
  change Q.d * expDataAlong n PT.N PT.ideal PT.E x i = P.d * expDataAlong n QT.N QT.ideal QT.E x i
  rw [hET]
  unfold expDataAlong
  split_ifs with hi
  · by_cases hxH : x ∈ PT.E.get ⟨i, hi⟩
    · exact hScaled _ (List.get_mem _ _) x hx hxH
    · have hHP : PT.E.get ⟨i, hi⟩ ∈ PT.E := List.get_mem _ _
      have hHQ : PT.E.get ⟨i, hi⟩ ∈ QT.E := hET.symm ▸ hHP
      have hclP : IsClosed (PT.N ∩ PT.E.get ⟨i, hi⟩) :=
        hPT.isWellFormed.isClosedSubmanifold_N.1.inter (hPT.isWellFormed.isSNCDivisor.1 _ hHP)
      have hclQ : IsClosed (QT.N ∩ PT.E.get ⟨i, hi⟩) :=
        hQT.isWellFormed.isClosedSubmanifold_N.1.inter (hQT.isWellFormed.isSNCDivisor.1 _ hHQ)
      rw [divExpAlong_eq_zero_of_notMem hclP (fun h => hxH h.2),
        divExpAlong_eq_zero_of_notMem hclQ (fun h => hxH h.2)]
      simp only [Nat.mul_zero]
  · simp only [Nat.mul_zero]

/-- Cosupport-local scaling is enough to preserve the literal original
run clock. No all-ambient exponent law is imposed. -/
theorem scaled_regime_run_sameCarrierDim {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (o p : ℕ) (hscale : Q.d * o = P.d * p)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (x : Y) :
    regimeRun (OrdRegime P o) T x = regimeRun (OrdRegime Q p) T x := by
  apply HironakaG8ClassStep.regimeRun_congr_of_test P _ _ ?_ T hT x
  intro Z V hV z
  have hCos := (hL.geoTransformAlong V hV).cosupp_eq_base
  have hRaw := scaled_raw_sameCarrierDim hn P Q hP hQ hL hDim hInitial V hV
  change (z ∈ (geoTransformAlong P V).cosupp ∧ nmOrd (geoTransformAlong P V) z = o) ↔
    (z ∈ (geoTransformAlong Q V).cosupp ∧ nmOrd (geoTransformAlong Q V) z = p)
  constructor
  · rintro ⟨hz, ho⟩
    have hr := hRaw z hz
    refine ⟨hCos ▸ hz, ?_⟩
    rw [ho] at hr
    exact Nat.eq_of_mul_eq_mul_left hP.one_le_d (hr.symm.trans hscale)
  · rintro ⟨hz, hp⟩
    have hzP : z ∈ (geoTransformAlong P V).cosupp := hCos.symm ▸ hz
    have hr := hRaw z hzP
    refine ⟨hzP, ?_⟩
    rw [hp] at hr
    exact Nat.eq_of_mul_eq_mul_left hQ.one_le_d (hr.trans hscale.symm)

abbrev secondOwnContact {n : ℕ} {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) : MarkedIdeal n (CMfd.of (n := n) (contactMask J K T y)) :=
  contactMarkedKept K (tangentChoice K (T.proj y)).2 T (contactMask J K T y)

/-- The actual independent J-own and K-own contacts receive their entire
unequal-mark class internally from ordinary source data. -/
theorem independent_two_source_contact_class {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hDim : SameCarrierDim J K) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y) :
    y ∈ contactMask J K T y ∧
      IsInvDomain (kJ-1) (ownContact J K T y) ∧ IsInvDomain (kK-1) (secondOwnContact J K T y) ∧
      LocWPEquiv (ownContact J K T y) (secondOwnContact J K T y) ∧
      SameCarrierDim (ownContact J K T y) (secondOwnContact J K T y) ∧
      (ownContact J K T y).E = (secondOwnContact J K T y).E ∧
      (∀ H ∈ (ownContact J K T y).E, ∀ x ∈ (ownContact J K T y).cosupp, x ∈ H →
        (secondOwnContact J K T y).d * divExpAlong n (ownContact J K T y).N (ownContact J K T y).ideal H x =
        (ownContact J K T y).d * divExpAlong n (secondOwnContact J K T y).N (secondOwnContact J K T y).ideal H x) := by
  let O := contactMask J K T y
  let P := ownContact J K T y
  let Q := secondOwnContact J K T y
  have hTK : IsGeoTestTower K T := (hL.wEquiv.2 T).1.mp hT
  have hTJBar : IsGeoTestTower (barMarked J) T := (((bar_local_any_boundary J hJ).wEquiv).2 T).1.mp hT
  have hTKBar : IsGeoTestTower (barMarked K) T := (((bar_local_any_boundary K hK).wEquiv).2 T).1.mp hTK
  have hBarT := (bar_local_of_local J K hJ hK hL).geoTransformAlong T hTJBar
  have hyK : y ∈ (geoTransformAlong (barMarked K) T).cosupp := hBarT.cosupp_eq_base ▸ hy
  have hLevel := level_eq_of_E_eq hL.wEquiv.1 T y
  have hSpecial := isSpecial_iff_of_wEquiv hn hJ hK hL.wEquiv hDim T hT y
  have hRegK : stepRegime K 0 T y :=
    ⟨hLevel ▸ hReg.1, fun h => hReg.2 (hSpecial.mpr h)⟩
  have hOutJ : y ∉ CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d :=
    fun h => hReg.2 (Or.inl ⟨hReg.1, h⟩)
  have hOutK : y ∉ CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d :=
    fun h => hRegK.2 (Or.inl ⟨hRegK.1, h⟩)
  have hyJMask := mem_maskB J hJ.isWellFormed hJ.one_le_d hMaxJ T hTJBar hy hReg.1 hOutJ
  have hyKMask := mem_maskB K hK.isWellFormed hK.one_le_d hMaxK T hTKBar hyK hRegK.1 hOutK
  obtain ⟨_hxJ, huJ⟩ := tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMaxJ T hTJBar hy)
  obtain ⟨_hxK, huK⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hK.one_le_d hMaxK T hTKBar hyK)
  let UJ : Opens X := ⟨(tangentChoice J (T.proj y)).1, huJ.isOpen⟩
  let UK : Opens X := ⟨(tangentChoice K (T.proj y)).1, huK.isOpen⟩
  have hOUJ : (O : Set Y) ⊆ openPreimage T UJ := fun _ hz => (interior_subset hz.1).1
  have hOUK : (O : Set Y) ⊆ openPreimage T UK := fun _ hz => (interior_subset hz.2).1
  have hP : IsInvDomain (kJ-1) P :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE UJ huJ T hTJBar O hOUJ
      (fun _ hz _ => (interior_subset hz.1).2.2)
      (fun H hH _ hz _ => (interior_subset hz.1).2.1 H hH)
  have hQ : IsInvDomain (kK-1) Q :=
    isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed hK.one_le_d hK.dimLE UK huK T hTKBar O hOUK
      (fun _ hz _ => (interior_subset hz.2).2.2)
      (fun H hH _ hz _ => (interior_subset hz.2).2.1 H hH)
  have hJP := original_bar_local_to_reference_contact J J hJ hJ rfl (LocEquiv.refl Kinds.wp J)
    UJ (tangentChoice J (T.proj y)).2 huJ T hT O hOUJ
  have hKQ := original_bar_local_to_reference_contact K K hK hK rfl (LocEquiv.refl Kinds.wp K)
    UK (tangentChoice K (T.proj y)).2 huK T hTK O hOUK
  have hPQ : LocWPEquiv (X := CMfd.of (n := n) O) P Q :=
    hJP.symm.trans ((hBarT.restrict O).trans hKQ)
  have hDimT := sameCarrierDim_geoTransformAlong hJ.isWellFormed hK.isWellFormed hL.wEquiv hDim T hT
  have hJBar := (HironakaActualOriginalHistoricalBarWeightedThreshold.original_bar_weighted_history J hJ T hT).2.1
  have hDimPQ : SameCarrierDim P Q := by
    intro x hx j
    have hxQ : x ∈ Q.cosupp := hPQ.cosupp_eq_base ▸ hx
    have hxUpperBar : (x : Y) ∈ (geoTransformAlong (barMarked J) T).cosupp := by
      have h := hJP.cosupp_eq_base.symm ▸ hx
      rw [cosupp_pullback_val (geoTransformAlong (barMarked J) T)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hJBar.isWellFormed.isCoherent hg) O] at h
      exact h
    have hxUpper : (x : Y) ∈ (geoTransformAlong J T).cosupp :=
      ((bar_local_any_boundary J hJ).geoTransformAlong T hT).cosupp_eq_base.symm ▸ hxUpperBar
    obtain ⟨a, haN, haS⟩ := exists_regularAtDim_strictAlong_stage J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d UJ huJ T hT
      (hOUJ x.2) (P.cosupp_subset_N hx)
    obtain ⟨b, hbN, hbS⟩ := exists_regularAtDim_strictAlong_stage K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d UK huK T hTK
      (hOUK x.2) (Q.cosupp_subset_N hxQ)
    have haK := (hDimT (x : Y) hxUpper (a+1)).mp haN
    have hab : a = b := Nat.add_right_cancel (RegularPointDimension.eq_of_regularAtDim haK hbN)
    have hPx : RegularAtDim (n := n) P.N x a := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr haS
    have hQx : RegularAtDim (n := n) Q.N x b := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hbS
    constructor
    · intro h
      rw [← RegularPointDimension.eq_of_regularAtDim hPx h, hab]
      exact hQx
    · intro h
      rw [← RegularPointDimension.eq_of_regularAtDim hQx h, ← hab]
      exact hPx
  have hGapP := contact_hasCosupportGap J hJ T hT (tangentChoice J (T.proj y)).2 O
  have hGapQ := contact_hasCosupportGap K hK T hTK (tangentChoice K (T.proj y)).2 O
  exact ⟨⟨hyJMask, hyKMask⟩, hP, hQ, hPQ, hDimPQ, hPQ.wEquiv.1,
    normalized_exponents_of_gap_sameCarrierDim (X := CMfd.of (n := n) O) hn P Q hP hQ hPQ hDimPQ hGapP hGapQ⟩

/-- Every SAME actual lower suffix receives full labelled geometry and
scaled exponents/raw/clocks. No future comparison is supplied as input. -/
theorem independent_two_source_contact_history {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hDim : SameCarrierDim J K) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y)
    {Z : CMfd.{0} n} (V : BlowupTower (CMfd.of (n := n) (contactMask J K T y)) Z)
    (hV : IsGeoTestTower (ownContact J K T y) V) :
    let P := ownContact J K T y
    let Q := secondOwnContact J K T y
    let PV := geoTransformAlong P V
    let QV := geoTransformAlong Q V
    IsGeoTestTower Q V ∧ IsInvDomain (kJ-1) PV ∧ IsInvDomain (kK-1) QV ∧ PV.E = QV.E ∧
      origMembers P V = origMembers Q V ∧ LocWPEquiv PV QV ∧ SameCarrierDim PV QV ∧
      (∀ x ∈ PV.cosupp, (∀ i, Q.d * expDataAlong n PV.N PV.ideal PV.E x i =
          P.d * expDataAlong n QV.N QV.ideal QV.E x i) ∧ Q.d * nmOrd PV x = P.d * nmOrd QV x) ∧
      (∀ o p, Q.d * o = P.d * p → ∀ x,
        regimeRun (OrdRegime P o) V x = regimeRun (OrdRegime Q p) V x) := by
  let P := ownContact J K T y
  let Q := secondOwnContact J K T y
  obtain ⟨_hyO, hP, hQ, hPQ, hDimPQ, hE, hInitial⟩ :=
    independent_two_source_contact_class hn J K hJ hK hDim hL hMaxJ hMaxK T hT y hy hReg
  have hVQ : IsGeoTestTower Q V := (hPQ.wEquiv.2 V).1.mp hV
  refine ⟨hVQ, isInvDomain_geoTransformAlong hP V hV, isInvDomain_geoTransformAlong hQ V hVQ,
    E_geoTransformAlong_eq hE V, origMembers_eq_of_E_eq hE V, hPQ.geoTransformAlong V hV,
    sameCarrierDim_geoTransformAlong hP.isWellFormed hQ.isWellFormed hPQ.wEquiv hDimPQ V hV, ?_, ?_⟩
  · intro x hx
    exact ⟨scaled_indexed_exponents_sameCarrierDim P Q hP hQ hPQ hDimPQ hInitial V hV x hx,
      scaled_raw_sameCarrierDim hn P Q hP hQ hPQ hDimPQ hInitial V hV x hx⟩
  · intro o p hscale x
    exact scaled_regime_run_sameCarrierDim hn P Q hP hQ hPQ hDimPQ hInitial o p hscale V hV x

end
end Hironaka.HironakaG1IndependentContactScaledHistory
