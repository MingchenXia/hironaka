import Hironaka.Resolution.HironakaG1OriginalContactClassAtStage
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData
import Hironaka.Resolution.HironakaG8P1Entries

/-! Full ordinary-input native class data for the independent ORIGINAL
own/reference contacts, with different carriers and the SAME full suffix.
Blueprint FIRST: hironaka-g1-independent-contact-class-data.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1IndependentContactClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec GermIdealOrder
  HironakaG1OriginalContactClassAtStage HironakaG1ChosenCommonContactClassData
  HironakaG1CoefficientCarrierClassData HironakaG1CoefficientBarClassData
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG8GapNormalizedExponent
  HironakaG1OriginalStepSkeleton HironakaG1CoeffBarLocal HironakaG8HomStable
  HironakaActualOriginalHistoricalBarWeightedThreshold HironakaActualCoefficientDivisorExponentGap
  HironakaG8OriginalRecursiveLocal HironakaG8P1Entries HironakaG8BornExponents
  HironakaG8MemberLoci HironakaG8SpecialLoci InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactEquivalenceAlong ContactEquivalenceStage
  TangentDirectionAlong ContactStageKept ContactStageInvDomain CoefficientIdealRestriction
  DivisorExponentAlong NonmonomialOrderLocal NonmonomialOrderTail
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactIndependenceAlong
  MonomialCaseAlong StepOneRegime NonmonomialOrderRegime
open HomogenizedGlueingTower (strictAlong)

abbrev contactMask {n : ℕ} {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) : Opens Y := maskB J T y ⊓ maskB K T y

abbrev ownContact {n : ℕ} {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) : MarkedIdeal n (CMfd.of (n := n) (contactMask J K T y)) :=
  contactMarkedKept J (tangentChoice J (T.proj y)).2 T (contactMask J K T y)

abbrev referenceContact {n : ℕ} {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (T : BlowupTower X Y) (y : Y) : MarkedIdeal n (CMfd.of (n := n) (contactMask J K T y)) :=
  contactMarkedKept J (tangentChoice K (T.proj y)).2 T (contactMask J K T y)

/-- The WHOLE actual original contact supplies its true marked support gap,
without a lower domain, tangent or finite-order hypothesis. -/
theorem contact_hasCosupportGap {n k : ℕ} {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (u : X → ℂ) (O : Opens Y) :
    HasCosupportGap (X := CMfd.of (n := n) O) (contactMarkedKept J u T O) := by
  let M := geoTransformAlong (barMarked J) T
  let S := strictAlong T (J.N ∩ {x | u x = 0})
  let C := withN (coeffMarkedAlong M) S
  let C₁ : MarkedIdeal n Y := { C with d := 1 }
  have hM := (original_bar_weighted_history J hJ T hT).2.1
  have hCI : C.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N
  have hS : S ⊆ M.N :=
    MaximalContactAlongTower.strictAlong_subset_N (barMarked J) (fun _ hx => hx.1) T
  have hGap : C₁.cosupp = C.cosupp :=
    coefficient_restriction_cosupport_gap M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d S hS
  have hOpen : (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) C₁).cosupp =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) C).cosupp := by
    rw [cosupp_pullback_val C₁
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCI hg) O,
      cosupp_pullback_val C
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCI hg) O, hGap]
  intro x _hx hx
  change x ∈ (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) C).cosupp
  rw [← hOpen]
  exact hx

/-- Ordinary original source data produce both actual independent-contact
domains, the full different-carrier class and genuine initial exponents. -/
theorem independent_contact_initial_class_data {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hN : J.N = K.N) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y) :
    y ∈ contactMask J K T y ∧
      IsInvDomain (kJ-1) (ownContact J K T y) ∧ IsInvDomain (kK-1) (referenceContact J K T y) ∧
      LocWPEquiv (X := CMfd.of (n := n) (contactMask J K T y)) (ownContact J K T y) (referenceContact J K T y) ∧
      SameCarrierDim (ownContact J K T y) (referenceContact J K T y) ∧
      (ownContact J K T y).ideal = (referenceContact J K T y).ideal ∧
      (ownContact J K T y).E = (referenceContact J K T y).E ∧
      (referenceContact J K T y).d = (ownContact J K T y).d ∧
      ExpAgree (ownContact J K T y) (referenceContact J K T y) := by
  let O := contactMask J K T y
  let A := ownContact J K T y
  let B := referenceContact J K T y
  have hTK : IsGeoTestTower K T := (hL.wEquiv.2 T).1.mp hT
  have hTJBar : IsGeoTestTower (barMarked J) T := (((bar_local_any_boundary J hJ).wEquiv).2 T).1.mp hT
  have hTKBar : IsGeoTestTower (barMarked K) T := (((bar_local_any_boundary K hK).wEquiv).2 T).1.mp hTK
  have hyK : y ∈ (geoTransformAlong (barMarked K) T).cosupp :=
    ((bar_local_of_local J K hJ hK hL).geoTransformAlong T hTJBar).cosupp_eq_base ▸ hy
  obtain ⟨hyJMask, hyKMask, hAB⟩ := own_contact_locally_equivalent_on_intersection hn J K hJ hK
    hN hL hMaxJ hMaxK T hT y hy hReg
  have hIB := isCoherent_restrictedCoeff J hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N
    (tangentChoice K (T.proj y)).2 T hTJBar
  obtain ⟨_hxJ, huJ⟩ := tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMaxJ T hTJBar hy)
  obtain ⟨_hxK, huK⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hK.one_le_d hMaxK T hTKBar hyK)
  let UJ : Opens X := ⟨(tangentChoice J (T.proj y)).1, huJ.isOpen⟩
  let UK : Opens X := ⟨(tangentChoice K (T.proj y)).1, huK.isOpen⟩
  have hOUJ : (O : Set Y) ⊆ openPreimage T UJ := fun _ hz => (interior_subset hz.1).1
  have hOUK : (O : Set Y) ⊆ openPreimage T UK := fun _ hz => (interior_subset hz.2).1
  have hA : IsInvDomain (kJ-1) A :=
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE UJ huJ T hTJBar O hOUJ
      (fun _ hz _ => (interior_subset hz.1).2.2)
      (fun H hH _ hz _ => (interior_subset hz.1).2.1 H hH)
  let C := contactMarkedKept K (tangentChoice K (T.proj y)).2 T O
  have hC : IsInvDomain (kK-1) C :=
    isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed hK.one_le_d hK.dimLE UK huK T hTKBar O hOUK
      (fun _ hz _ => (interior_subset hz.2).2.2)
      (fun H hH _ hz _ => (interior_subset hz.2).2.1 H hH)
  have hBNC : B.N = C.N := by
    change (Subtype.val : O → Y) ⁻¹' strictAlong T (J.N ∩ {p | (tangentChoice K (T.proj y)).2 p = 0}) =
      (Subtype.val : O → Y) ⁻¹' strictAlong T (K.N ∩ {p | (tangentChoice K (T.proj y)).2 p = 0})
    rw [hN]
  have hBC : LocWPEquiv (X := CMfd.of (n := n) O) B C :=
    contact_lower_locally_equivalent J K hJ hK hN hL T hT hTK O _
      (hBNC.symm ▸ hC.isWellFormed.isClosedSubmanifold_N)
  have hBI : B.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hIB
  have hBd : 1 ≤ B.d := one_le_coeffMarkedAlong_d (geoTransformAlong (barMarked J) T)
  have hB : IsInvDomain (kK-1) B := isInvDomain_of_sameCarrier_cosupp (X := CMfd.of (n := n) O)
    B C hC hBI hBd hBNC hBC.wEquiv.1 hBC.cosupp_eq_base
  have hNT : (geoTransformAlong J T).N = (geoTransformAlong K T).N :=
    HironakaCoherentTransformExtension.geoTransformAlong_N_eq_of_N_eq hN T
  have hDim : SameCarrierDim A B := by
    intro x hx j
    have hxB : x ∈ B.cosupp := hAB.cosupp_eq_base ▸ hx
    have hxJS : (x : Y) ∈ strictAlong T (J.N ∩ {p | (tangentChoice J (T.proj y)).2 p = 0}) :=
      A.cosupp_subset_N hx
    have hxKS : (x : Y) ∈ strictAlong T (K.N ∩ {p | (tangentChoice K (T.proj y)).2 p = 0}) := by
      rw [← hN]
      exact B.cosupp_subset_N hxB
    obtain ⟨a, haN, haS⟩ := exists_regularAtDim_strictAlong_stage J
      hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d UJ huJ T hT (hOUJ x.2) hxJS
    obtain ⟨b, hbN, hbS⟩ := exists_regularAtDim_strictAlong_stage K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d UK huK T hTK (hOUK x.2) hxKS
    have haK : RegularAtDim (n := n) (geoTransformAlong K T).N (x : Y) (a+1) := hNT ▸ haN
    have hab : a = b := Nat.add_right_cancel (RegularPointDimension.eq_of_regularAtDim haK hbN)
    have hAx : RegularAtDim (n := n) A.N x a := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr haS
    have hBx : RegularAtDim (n := n) B.N x b := by
      change RegularAtDim (n := n) ((Subtype.val : O → Y) ⁻¹'
        strictAlong T (J.N ∩ {p | (tangentChoice K (T.proj y)).2 p = 0})) x b
      rw [hN]
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hbS
    constructor
    · intro h
      rw [← RegularPointDimension.eq_of_regularAtDim hAx h, hab]
      exact hBx
    · intro h
      rw [← RegularPointDimension.eq_of_regularAtDim hBx h, ← hab]
      exact hAx
  have hGapA : HasCosupportGap A := contact_hasCosupportGap J hJ T hT _ O
  have hGapB : HasCosupportGap B := contact_hasCosupportGap J hJ T hT _ O
  have hNorm := normalized_exponents_of_gap_sameCarrierDim (X := CMfd.of (n := n) O) hn A B
    hA hB hAB hDim hGapA hGapB
  have hExp : ExpAgree A B := by
    intro H hH x hx hxH
    exact Nat.eq_of_mul_eq_mul_left hA.one_le_d (hNorm H hH x hx hxH)
  exact ⟨⟨hyJMask, hyKMask⟩, hA, hB, hAB, hDim, rfl, rfl, rfl, hExp⟩

/-- The SAME actual lower suffix carries all whole labelled exponent data,
native raw orders and unreset run clocks. No future comparison is an input. -/
theorem independent_contact_same_suffix_data {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hN : J.N = K.N) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y)
    {Z : CMfd.{0} n} (V : BlowupTower (CMfd.of (n := n) (contactMask J K T y)) Z)
    (hV : IsGeoTestTower (ownContact J K T y) V) :
    let A := ownContact J K T y
    let B := referenceContact J K T y
    let AV := geoTransformAlong A V
    let BV := geoTransformAlong B V
    IsGeoTestTower B V ∧ IsInvDomain (kJ-1) AV ∧ IsInvDomain (kK-1) BV ∧ AV.E = BV.E ∧
      origMembers A V = origMembers B V ∧ LocWPEquiv AV BV ∧ SameCarrierDim AV BV ∧ ExpAgree AV BV ∧
      (∀ x ∈ AV.cosupp, expDataAlong n AV.N AV.ideal AV.E x = expDataAlong n BV.N BV.ideal BV.E x ∧
        nmOrd AV x = nmOrd BV x) ∧
      (∀ o x, regimeRun (OrdRegime A o) V x = regimeRun (OrdRegime B o) V x) := by
  let A := ownContact J K T y
  let B := referenceContact J K T y
  obtain ⟨_hyO, hA, hB, hAB, hDim, _hI, hE, hd, hExp⟩ :=
    independent_contact_initial_class_data hn J K hJ hK hN hL hMaxJ hMaxK T hT y hy hReg
  have hVB : IsGeoTestTower B V := (hAB.wEquiv.2 V).1.mp hV
  have hAV := isInvDomain_geoTransformAlong hA V hV
  have hBV := isInvDomain_geoTransformAlong hB V hVB
  have hEV := MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE V
  have hOld := origMembers_eq_of_E_eq hE V
  have hLV := hAB.geoTransformAlong V hV
  have hDV := sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed hAB.wEquiv hDim V hV
  have hXV := locWPEquiv_expAgree_geoTransformAlong hAB hA hB hDim hd hExp V hV
  refine ⟨hVB, hAV, hBV, hEV, hOld, hLV, hDV, hXV, ?_, ?_⟩
  · intro x hx
    exact ⟨expDataAlong_eq_of_expAgree' hAV.isWellFormed hBV.isWellFormed hEV.symm hXV hx,
      locWPEquiv_nmOrd_geoTransformAlong_eq hAB hA hB hDim hd hExp V hV hx⟩
  · intro o x
    exact locWPEquiv_regimeRun_eq hAB hA hB hDim hd hExp o V hV x

end
end Hironaka.HironakaG1IndependentContactClassData
