import Hironaka.Resolution.HironakaG1IndependentContactScaledHistory
import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut

/-! Full ORIGINAL positive-member class on genuinely different carriers.
Blueprint FIRST: hironaka-g1-different-carrier-member-class-data.tex.
The carrier-specific stage-local mother is consumed without re-proving it. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1DifferentCarrierMemberClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8MemberLoci HironakaG8SpecialLoci HironakaG8GapNormalizedExponent
  HironakaG1CoefficientCarrierClassData HironakaG1IndependentContactScaledHistory
  HironakaG1RecursiveMemberValueTransport HironakaG8HomStable HironakaG1CoeffBarLocal
  HironakaActualCoefficientDivisorExponentGap HironakaActualOriginalHistoricalBarWeightedThreshold
  InvDomainMemberRestriction InvDomainRebase InvDomainTowerAlong HomogenizedIdealAlong MemberInterAlong BoundaryCount
  CoefficientIdealRestriction StepOneValue StepOneValueMasked StepOneLowerDomain
  DivisorExponentAlong MonomialCaseAlong NonmonomialOrderLocal NonmonomialOrderRegime StepOneRegime

/-- Positive original masks agree from the held special-locus theorem on
equal-dimensional carriers; their subsets need not agree. -/
theorem positive_mask_eq_sameCarrierDim {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hW : WEquiv A B) (hDim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) (y : Y) :
    maskA A T y = maskA B T y := by
  have hOrig := origMembers_eq_of_E_eq hW.1 T
  have hl : ∀ z : Y, level A T z = level B T z := level_eq_of_E_eq hW.1 T
  have hs : ∀ z : Y, IsSpecial A T z ↔ IsSpecial B T z :=
    isSpecial_iff_of_wEquiv hn hA hB hW hDim T hT
  unfold maskA
  congr 1
  apply congrArg interior
  ext z
  simp only [mem_ofPred_eq, hOrig, hl, hs]

/-- Whole native coefficient ideals give the actual member support gap,
including open restriction, with no lower-domain premise. -/
theorem member_open_hasCosupportGap {n k : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (I : Finset (Fin P.E.length)) (U : Opens X) :
    HasCosupportGap (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (memberRestrict P I)) := by
  let C := memberRestrict P I
  let C₁ : MarkedIdeal n X := { C with d := 1 }
  have hCI : C.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hGap : C₁.cosupp = C.cosupp :=
    coefficient_restriction_cosupport_gap P hP.isWellFormed.isClosedSubmanifold_N
      hP.isWellFormed.isCoherent hP.one_le_d (P.N ∩ memberInter P.E I) inter_subset_left
  have hOpen : (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) C₁).cosupp =
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) C).cosupp := by
    rw [cosupp_pullback_val C₁
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCI hg) U,
      cosupp_pullback_val C
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCI hg) U, hGap]
  intro x _hx hx
  change x ∈ (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) C).cosupp
  rw [← hOpen]
  exact hx

private theorem member_dimension_on_mask {n k l : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (E₀ : List (Set X)) (hE₀ : ∀ H ∈ E₀, H ∈ P.E) (y : X) (U : Opens X)
    (hInc : ∀ x ∈ (U : Set X), ∀ H ∈ E₀, x ∈ H → y ∈ H) :
    SameCarrierDim (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (memberRestrict P (InvDomainMemberRestriction.membersThrough P.E E₀ y)))
      (MarkedIdeal.pullback (Subtype.val : U → X) (memberRestrict Q (InvDomainMemberRestriction.membersThrough Q.E E₀ y))) := by
  let A := memberRestrict P (InvDomainMemberRestriction.membersThrough P.E E₀ y)
  let B := memberRestrict Q (InvDomainMemberRestriction.membersThrough Q.E E₀ y)
  have hIA : A.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hE : P.E = Q.E := hL.wEquiv.1
  have hTransP := NormalCrossingsComparison.isTransverse_of_forall_mem hP.isWellFormed.isTransverse hE₀
  have hTransQ := NormalCrossingsComparison.isTransverse_of_forall_mem hQ.isWellFormed.isTransverse
    (fun H hH => hE ▸ hE₀ H hH)
  intro x hx j
  have hxA : (x : X) ∈ A.cosupp := by
    have h := cosupp_pullback_val A
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIA hg) U
    rw [h] at hx
    exact hx
  have hxSplit := (cosupp_memberRestrict hP.isWellFormed hP.one_le_d
    (InvDomainMemberRestriction.membersThrough P.E E₀ y)) ▸ hxA
  have hxP : (x : X) ∈ P.cosupp := hxSplit.1
  have hxQ : (x : X) ∈ Q.cosupp := hL.cosupp_eq_base ▸ hxP
  have hxS : ∀ H ∈ P.E, H ∈ E₀ → y ∈ H → (x : X) ∈ H := by
    have h := hxSplit.2
    rw [memberInter_membersThrough_eq] at h
    exact h
  have hSx : memberInter P.E (InvDomainMemberRestriction.membersThrough P.E E₀ y) =
      HironakaG8MemberLoci.membersThrough E₀ (x : X) := by
    rw [memberInter_membersThrough_eq]
    ext w
    constructor
    · intro h H hH hxH
      exact h H (hE₀ H hH) hH (hInc x x.2 H hH hxH)
    · intro h H _hH hH₀ hyH
      exact h H hH₀ (hxS H (hE₀ H hH₀) hH₀ hyH)
  have hSQ : memberInter Q.E (InvDomainMemberRestriction.membersThrough Q.E E₀ y) =
      HironakaG8MemberLoci.membersThrough E₀ (x : X) := by rw [← hE]; exact hSx
  obtain ⟨a, h, haN, haH, _haLe, haInt⟩ := exists_regularAtDim_inter_membersThrough hTransP
    (P.cosupp_subset_N hxP)
  obtain ⟨b, i, hbN, hbH, _hbLe, hbInt⟩ := exists_regularAtDim_inter_membersThrough hTransQ
    (Q.cosupp_subset_N hxQ)
  have hab : a = b := RegularPointDimension.eq_of_regularAtDim ((hDim (x : X) hxP a).mp haN) hbN
  have hhi : h = i := RegularPointDimension.eq_of_regularAtDim haH hbH
  have hNA : A.N = P.N ∩ HironakaG8MemberLoci.membersThrough E₀ (x : X) := by
    change P.N ∩ memberInter P.E (InvDomainMemberRestriction.membersThrough P.E E₀ y) = _
    rw [hSx]
  have hNB : B.N = Q.N ∩ HironakaG8MemberLoci.membersThrough E₀ (x : X) := by
    change Q.N ∩ memberInter Q.E (InvDomainMemberRestriction.membersThrough Q.E E₀ y) = _
    rw [hSQ]
  have hAx : RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' A.N) x (a+h-n) := by
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    rw [hNA]
    exact haInt
  have hBx : RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' B.N) x (b+i-n) := by
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    rw [hNB]
    exact hbInt
  change RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' A.N) x j ↔
    RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' B.N) x j
  constructor
  · intro hReg
    rw [← RegularPointDimension.eq_of_regularAtDim hAx hReg, hab, hhi]
    exact hBx
  · intro hReg
    rw [← RegularPointDimension.eq_of_regularAtDim hBx hReg, ← hab, ← hhi]
    exact hAx

/-- The actual positive-member records inherit their whole native class
from ordinary different-carrier sources, without lower-output inputs. -/
theorem positive_member_class_data_sameCarrierDim {n kA kB : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hL : LocWPEquiv A B) (hDim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (s : ℕ) (hlevel : level A T y = s+1) :
    let O := maskA A T y
    let A' := positiveMemberOn A T y O
    let B' := positiveMemberOn B T y O
    IsInvDomain (kA-1) A' ∧ IsInvDomain (kB-1) B' ∧ A'.E = B'.E ∧
      LocWPEquiv A' B' ∧ SameCarrierDim A' B' ∧
      (∀ H ∈ A'.E, ∀ x ∈ A'.cosupp, x ∈ H →
        B'.d * divExpAlong n A'.N A'.ideal H x = A'.d * divExpAlong n B'.N B'.ideal H x) := by
  let O := maskA A T y
  let P := geoTransformAlong (barMarked A) T
  let Q := geoTransformAlong (barMarked B) T
  let A' := positiveMemberOn A T y O
  let B' := positiveMemberOn B T y O
  have hTB : IsGeoTestTower B T := (hL.wEquiv.2 T).1.mp hT
  have hTP : IsGeoTestTower (barMarked A) T := (((bar_local_any_boundary A hA).wEquiv).2 T).1.mp hT
  have hTQ : IsGeoTestTower (barMarked B) T := (((bar_local_any_boundary B hB).wEquiv).2 T).1.mp hTB
  have hP : IsInvDomain kA P := (original_bar_weighted_history A hA T hT).2.1
  have hQ : IsInvDomain kB Q := (original_bar_weighted_history B hB T hTB).2.1
  have hMask := positive_mask_eq_sameCarrierDim hn A B hA hB hL.wEquiv hDim T hT y
  have hlevelB : level B T y = s+1 := (level_eq_of_E_eq hL.wEquiv.1 T y).symm.trans hlevel
  have hA' : IsInvDomain (kA-1) A' :=
    isInvDomain_lowerMarked_succ A hA.isWellFormed hA.one_le_d hn T hTP hA.dimLE hlevel
  have hB' : IsInvDomain (kB-1) B' := by
    have hB₀ := isInvDomain_lowerMarked_succ B hB.isWellFormed hB.one_le_d hn T hTQ hB.dimLE hlevelB
    have hTransport : ∀ (V : Opens Y), V = maskA B T y →
        IsInvDomain (kB-1) (positiveMemberOn B T y V) := by
      intro V hV
      subst V
      exact hB₀
    exact hTransport O hMask
  have hLocal : LocWPEquiv (X := CMfd.of (n := n) O) A' B' :=
    HironakaG1SeparateCarrierMemberCut.member_stage_local_of_local hn A B hA hB hL T hT O y
  have hUpper : LocWPEquiv P Q := (bar_local_of_local A B hA hB hL).geoTransformAlong T hTP
  have hDimBar : SameCarrierDim (barMarked A) (barMarked B) := by
    intro x hx j
    exact hDim x (StepOneLowerDomain.cosupp_barMarked A hA.isWellFormed hA.one_le_d ▸ hx) j
  have hDimUpper : SameCarrierDim P Q := sameCarrierDim_geoTransformAlong
    (isWellFormed_barMarked A hA.isWellFormed) (isWellFormed_barMarked B hB.isWellFormed)
    (bar_local_of_local A B hA hB hL).wEquiv hDimBar T hTP
  have hOrig : origMembers A T = origMembers B T := origMembers_eq_of_E_eq hL.wEquiv.1 T
  have hE₀ : ∀ H ∈ origMembers A T, H ∈ P.E :=
    fun H hH => List.take_subset A.E.length _ hH
  have hDimLower : SameCarrierDim A' B' := by
    change SameCarrierDim (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y)
        (memberRestrict P (InvDomainMemberRestriction.membersThrough P.E (origMembers A T) y)))
      (MarkedIdeal.pullback (Subtype.val : O → Y)
        (memberRestrict Q (InvDomainMemberRestriction.membersThrough Q.E (origMembers B T) y)))
    rw [← hOrig]
    exact member_dimension_on_mask P Q hP hQ hUpper hDimUpper (origMembers A T) hE₀ y O
      (fun _ hx H hH hxH => (interior_subset hx).1 H hH hxH)
  have hGapA : HasCosupportGap A' :=
    member_open_hasCosupportGap P hP (InvDomainMemberRestriction.membersThrough P.E (origMembers A T) y) O
  have hGapB : HasCosupportGap B' :=
    member_open_hasCosupportGap Q hQ (InvDomainMemberRestriction.membersThrough Q.E (origMembers B T) y) O
  exact ⟨hA', hB', hLocal.wEquiv.1, hLocal, hDimLower,
    normalized_exponents_of_gap_sameCarrierDim (X := CMfd.of (n := n) O) hn A' B' hA' hB' hLocal hDimLower hGapA hGapB⟩

/-- Every SAME actual positive-member suffix inherits the whole labelled
native data, including scaled default exponents, raw orders and clocks. -/
theorem positive_member_suffix_class_data_sameCarrierDim {n kA kB : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hL : LocWPEquiv A B) (hDim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (s : ℕ) (hlevel : level A T y = s+1)
    {Z : CMfd.{0} n} (V : BlowupTower (CMfd.of (n := n) (maskA A T y)) Z)
    (hV : IsGeoTestTower (positiveMemberOn A T y (maskA A T y)) V) :
    let P := positiveMemberOn A T y (maskA A T y)
    let Q := positiveMemberOn B T y (maskA A T y)
    let PV := geoTransformAlong P V
    let QV := geoTransformAlong Q V
    IsGeoTestTower Q V ∧ IsInvDomain (kA-1) PV ∧ IsInvDomain (kB-1) QV ∧ PV.E = QV.E ∧
      origMembers P V = origMembers Q V ∧ LocWPEquiv PV QV ∧ SameCarrierDim PV QV ∧
      (∀ x ∈ PV.cosupp, (∀ i, Q.d * expDataAlong n PV.N PV.ideal PV.E x i =
          P.d * expDataAlong n QV.N QV.ideal QV.E x i) ∧ Q.d * nmOrd PV x = P.d * nmOrd QV x) ∧
      (∀ o p, Q.d * o = P.d * p → ∀ x,
        regimeRun (OrdRegime P o) V x = regimeRun (OrdRegime Q p) V x) := by
  let P := positiveMemberOn A T y (maskA A T y)
  let Q := positiveMemberOn B T y (maskA A T y)
  obtain ⟨hP, hQ, hE, hPQ, hDimPQ, hInitial⟩ :=
    positive_member_class_data_sameCarrierDim hn A B hA hB hL hDim T hT y s hlevel
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
end Hironaka.HironakaG1DifferentCarrierMemberClassData
