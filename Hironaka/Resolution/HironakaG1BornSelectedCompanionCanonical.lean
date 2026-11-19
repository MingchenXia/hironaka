import Hironaka.Resolution.HironakaG1BornSelectedCompanionPhase
import Hironaka.Resolution.HironakaG1LaterSelectedSectionGapCanonical

/-! Recursive domain and original canonicality for the next born-member contact. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
namespace Hironaka.HironakaG1BornSelectedCompanionCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneLowerDomain InvDomainMemberRestriction
  CoefficientIdealRestriction HomogenizedIdealAlong ContactIndependenceAlong TangentDirectionAlong
  ContactStageInvDomain DivisorExponentAlong
  HironakaG8LocalHistory HironakaG8GapNormalizedExponent HironakaG11InvBMClass
  HironakaG1BornSelectedCompanionPhase HironakaG1LaterPositiveMaskContact
  HironakaG1ChosenCommonContactClassData HironakaG1DifferentCarrierMemberClassData
  HironakaG1CoefficientCarrierClassData HironakaActualCoefficientDivisorExponentGap
  HironakaG1OriginalUnequalMarkCanonical HironakaG1RecursiveMemberValueTransport

set_option maxHeartbeats 1100000 in
/-- For a realized next born cut, the known domain of either contact record
supplies the other domain. Both coefficient gaps furnish the normalized
divisor exponents needed for exact original canonicality. -/
theorem born_selected_contact_canonical_of_domain {n k l q : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hR : IsInvDomain l R) (p : X) (W : Opens X) (u : X → ℂ) :
    let A := CMfd.of (n := n) W
    let H : BlowupTower X X := .refl
    let K := positiveMemberOn J H p W
    let S := positiveMemberOn R H p W
    let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
    IsInvDomain k K → C.N = S.N → LocWPEquiv (X := A) C S →
    (IsInvDomain q C ∨ IsInvDomain q S) →
    IsInvDomain q C ∧ IsInvDomain q S ∧
    (∀ F ∈ C.E, ∀ x ∈ C.cosupp, x ∈ F →
      S.d * divExpAlong n C.N C.ideal F x = C.d * divExpAlong n S.N S.ideal F x) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical C ((invFamily hn q).inv C) T ↔ IsCanonical S ((invFamily hn q).inv S) T := by
  intro A H K S C hK hN hClass hDomain
  let B := barMarked R
  let I := membersThrough B.E (origMembers R H) p
  have hB : IsInvDomain l B :=
    HironakaCoherentTransformExtension.isInvDomain_barMarked R hR
  have hS : S.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val
    (isWellFormed_memberRestrict hn hB.isWellFormed I) W
  have hSd : 1 ≤ S.d := one_le_memberRestrict_d B I
  have hCI : C.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N
  have hCd : 1 ≤ C.d := one_le_coeffMarkedAlong_d K
  have hE := hClass.wEquiv.1
  have hCos := hClass.cosupp_eq_base
  obtain ⟨hCd', hSd'⟩ : IsInvDomain q C ∧ IsInvDomain q S := by
    rcases hDomain with hC | hS'
    · exact ⟨hC, isInvDomain_of_sameCarrier_cosupp S C hC hS.isCoherent hSd
        hN.symm hE.symm hCos.symm⟩
    · exact ⟨isInvDomain_of_sameCarrier_cosupp C S hS' hCI hCd hN hE hCos, hS'⟩
  have hGapS : HasCosupportGap (X := A) S := member_open_hasCosupportGap B hB I W
  have hGapC : HasCosupportGap (X := A) C := by
    intro x _ hx
    change x ∈ GermIdealOrder.cosupport n C.N (coeffMarkedAlong K).ideal 1 at hx
    change x ∈ GermIdealOrder.cosupport n C.N (coeffMarkedAlong K).ideal (coeffMarkedAlong K).d
    rw [← coefficient_restriction_cosupport_gap K hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hK.one_le_d C.N (fun _ h => h.1)]
    exact hx
  have hDim := SameCarrierDim.of_N_eq hN
  have hExp := normalized_exponents_of_gap_sameCarrierDim hn C S hCd' hSd' hClass hDim hGapC hGapS
  exact ⟨hCd', hSd', hExp, fun T =>
    invFamily_isCanonical_iff_of_local hn C S hCd' hSd' hClass hDim hExp T⟩

set_option maxHeartbeats 1300000 in
/-- When the supported reference is itself nonspecial at the positive
companion anchor, a common window supplies the recursive domain of the
prescribed contact and original CAN without a domain or exponent input. -/
theorem exists_born_selected_contact_canonical_of_supported_nonspecial {n k l s : ℕ}
    (hn : 0 < n) {X : CMfd.{0} n} (J R : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (hRJ : R.N ⊆ J.N) (p : X) (hpR : p ∈ R.N)
    (hl : level J (.refl : BlowupTower X X) p = s + 1)
    (hNS : ¬ IsSpecial J (.refl : BlowupTower X X) p)
    (hNSR : ¬ IsSpecial R (.refl : BlowupTower X X) p)
    (V : Opens X) (hpV : p ∈ V) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d V u)
    (hTrace : J.N ∩ {x | u x = 0} ∩ V = R.N ∩ V) :
    let H : BlowupTower X X := .refl
    ∃ W : Opens X, p ∈ W ∧ W ≤ V ∧ W ≤ maskA J H p ∧ W ≤ maskA R H p ∧
      let A := CMfd.of (n := n) W
      let K := positiveMemberOn J H p W
      let S := positiveMemberOn R H p W
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      IsInvDomain (k - 1) K ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → X)) ∧
      C.N = S.N ∧ C.E = S.E ∧ LocWPEquiv (X := A) C S ∧
      IsInvDomain (l - 1) C ∧ IsInvDomain (l - 1) S ∧
      (∀ F ∈ C.E, ∀ x ∈ C.cosupp, x ∈ F →
        S.d * divExpAlong n C.N C.ideal F x = C.d * divExpAlong n S.N S.ideal F x) ∧
      ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
        IsCanonical C ((invFamily hn (l - 1)).inv C) T ↔
          IsCanonical S ((invFamily hn (l - 1)).inv S) T := by
  intro H
  have hlR : level R H p = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq hClass.wEquiv.1 H p).symm.trans hl
  have hpRmask : p ∈ maskA R H p :=
    mem_maskA R hR.isWellFormed hR.one_le_d hn H trivial (by rw [hlR]; omega) hNSR
  let V' := V ⊓ maskA R H p
  have hpV' : p ∈ V' := ⟨hpV, hpRmask⟩
  have hu' : IsTangentDirectionAlong J.N J.ideal J.d V' u :=
    isTangentDirectionAlong_mono hu V'.isOpen inf_le_left
  have hTrace' : J.N ∩ {x | u x = 0} ∩ V' = R.N ∩ V' := by
    ext z
    have hz := Set.ext_iff.mp hTrace z
    exact ⟨fun h => ⟨(hz.mp ⟨h.1, h.2.1⟩).1, h.2⟩,
      fun h => ⟨(hz.mpr ⟨h.1, h.2.1⟩).1, h.2⟩⟩
  obtain ⟨W, hpW, hWV, hWJ, hK, hKu, hN, _, hE, _, hCR⟩ :=
    exists_born_selected_companion_contact hn J R hJ hR hClass hRJ p hpR hl hNS V' hpV' u hu' hTrace'
  have hWR : W ≤ maskA R H p := le_trans hWV inf_le_right
  have hS := positive_member_domain_on_subwindow hn R hR H trivial p hlR W hWR
  obtain ⟨hC, hS', hExp, hCan⟩ :=
    born_selected_contact_canonical_of_domain (q := l - 1) hn J R hR p W u hK hN hCR (Or.inr hS)
  exact ⟨W, hpW, le_trans hWV inf_le_left, hWJ, hWR, hK, hKu, hN, hE, hCR, hC, hS', hExp, hCan⟩

end Hironaka.HironakaG1BornSelectedCompanionCanonical
