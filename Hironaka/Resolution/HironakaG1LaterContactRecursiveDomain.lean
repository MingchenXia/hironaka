import Hironaka.Resolution.HironakaG1LaterSelectedSectionClass
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary
import Hironaka.Invariant.GeneralCompare
import Hironaka.Resolution.HironakaActualOpenTangentDescent

/-! The prescribed later contact on the support-aligned positive branch. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterContactRecursiveDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec StepOneLowerDomain InvDomainMemberRestriction
  HironakaActualOpenTangentDescent StepOneValue TangentDirectionAlong CoefficientIdealRestriction
  DerivativeIdealAlong ContactEquivalenceAlong GeneralValue GeneralCompare CompanionReductionAlong NonmonomialOrderTail NonmonomialOrderLocal
  HomogenizedGlueingLiftAlong CompanionRebase
  RestrictedIdealExtension MonomialPartAlong RelativePrincipalizationSpan
  HironakaSharpActualChronologicalResidualDictionary
  HomogenizedIdealAlong ContactIndependenceAlong
  HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1LaterSelectedSectionClass HironakaG1LaterPositiveMaskContact
  HironakaG1ChosenCommonContactClassData HironakaG1RecursiveMemberValueTransport
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalContact HironakaG1PositiveNormalPhase
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1500000 in
/-- On a window in the actual section mask the prescribed later contact has
the exact smaller recursive domain, even when the retained boundary has
born slots. The lower-domain proof uses the section's own nonspecial mask. -/
theorem later_contact_domain_on_section_mask {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hl : level (properNormalMarked Q) H p = s + 1) (W : Opens Y)
    (hW : W ≤ maskA (sectionMarked Q) H p) (u : Y → ℂ) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let L := positiveMemberOn P H p W
    let S := positiveMemberOn Sec H p W
    let C := withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0})
    IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) →
    L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D →
    IsInvDomain (k - 1) C ∧ IsInvDomain (k - 1) S := by
  intro P Sec D L S C hu hTrace
  let X := CMfd.of (n := n + 1) (productOpen U)
  let A := CMfd.of (n := n + 1) W
  have hP := properNormalMarked_isInvDomain Q hQ
  have hPT := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hWp : W ≤ maskA P H p := fun _ hx => positive_normal_section_mask_subset Q hQ H hH p
    (by rw [hl]; exact Nat.succ_pos s) (hW hx)
  have hL : IsInvDomain k L := by
    simpa using positive_member_domain_on_subwindow (Nat.succ_pos n) P hP H hPT p hl W hWp
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBT := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
  have hlSec : level Sec H p = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (A := P) (B := Sec) rfl H p).symm.trans hl
  have hS : IsInvDomain (k - 1) S :=
    positive_member_domain_on_subwindow (Nat.succ_pos n) Sec hSec H hBT p hlSec W hW
  obtain ⟨hN, _, hE, hClass⟩ :=
    selected_normal_contact_section_class_on_window Q hQ H hH p W u hL hu hTrace
  have hC : IsInvDomain (k - 1) C :=
    isInvDomain_of_sameCarrier_cosupp (X := A) C S hS
      (isCoherent_coeffMarkedAlong hL.isWellFormed.isCoherent hL.isWellFormed.isClosedSubmanifold_N)
      (one_le_coeffMarkedAlong_d L) hN hE hClass.cosupp_eq_base
  exact ⟨hC, hS⟩

/-- At the true mark on the literal order mask, absence of a divisor
factor on each touching retained member identifies the actual maximal-order
companion with the carrier restriction and preserves the prescribed tangent. -/
theorem same_mark_companion_tangent_on_order_mask {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain k L) (u : X → ℂ)
    (hu : IsTangentDirectionAlong L.N L.ideal L.d univ u) :
    let O := ordMask L L.d
    let A := CMfd.of (n := n) O
    let M := MarkedIdeal.pullback (M' := A) (Subtype.val : O → X) L
    let J := compAt L L.d (.refl : BlowupTower X X)
    (∀ x ∈ M.N, ∀ i : Fin M.E.length, x ∈ M.E.get i →
      ∃ a, M.ideal.mem x a ∧
        ¬ IsInSpanOnAt (n := n) M.N
          ((vanishingIdeal (n := n) (M.E.get i)).mem x) x a) →
    J = (⟨M.N, M.E, restrictOn n M.N M.ideal, L.d⟩ : MarkedIdeal n A) ∧
    IsInvDomain k J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
    IsTangentDirectionAlong J.N J.ideal J.d univ (u ∘ (Subtype.val : O → X)) := by
  intro O A M J hFactors
  have hM : IsInvDomain k M := InvDomainTowerAlong.isInvDomain_pullback_val O hL
  have hPart := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isSNCDivisor
    hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hFactors
  have hEq : J = (⟨M.N, M.E, restrictOn n M.N M.ideal, L.d⟩ : MarkedIdeal n A) := by
    change companionOf n M L.d = _
    have hd : M.d = L.d := rfl
    simp only [companionOf, companionAlong, hd, lt_self_iff_false, if_false, hPart]
  have hMT : IsTangentDirectionAlong M.N M.ideal M.d univ (u ∘ (Subtype.val : O → X)) :=
    isTangentDirectionAlong_pullback_val O
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL.isWellFormed.isCoherent hg)
      ⟨O.isOpen, fun x _ => hu.mem x (mem_univ x), fun x _ => hu.multiplicity_one x (mem_univ x)⟩
  refine ⟨hEq, isInvDomain_compAt hn hL.one_le_d (.refl : BlowupTower X X) hL,
    isMaximalOrderAlong_compAt hn L.d (.refl : BlowupTower X X) hL, ?_⟩
  rw [hEq]
  exact ⟨hMT.isOpen, fun z hz =>
    iterDerivIdealAlong_mono (N := M.N) (le_restrictOn hM.isWellFormed.isCoherent)
      (L.d - 1) z _ (hMT.mem z hz), hMT.multiplicity_one⟩

set_option maxHeartbeats 1500000 in
/-- At an actual positive anchor that is also nonspecial on the supported
section, choose a common tangent window and construct the prescribed
contact's smaller recursive domain. -/
theorem exists_later_contact_recursive_domain_of_section_nonspecial {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (properNormalMarked Q) H).cosupp)
    (hl : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    ∃ (W : Opens Y) (u : Y → ℂ),
      let L := positiveMemberOn P H p W
      let S := positiveMemberOn Sec H p W
      let C := withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0})
      p ∈ W ∧ p ∈ D ∧ W ≤ maskA Sec H p ∧ W ≤ maskA P H p ∧
      IsInvDomain k L ∧ IsInvDomain (k - 1) C ∧ IsInvDomain (k - 1) S ∧
      IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) ∧
      L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D := by
  intro P Sec D
  let X := CMfd.of (n := n + 1) (productOpen U)
  let B := geoTransformAlong (barMarked P) H
  let K := memberRestrict B (membersThrough B.E (origMembers P H) p)
  let M := maskA Sec H p
  have hPos : 0 < level P H p := hl ▸ Nat.succ_pos s
  have hNSp : ¬ IsSpecial P H p := fun hS =>
    hNS (positive_normal_special_of_padded Q hQ H hH p hPos hS)
  obtain ⟨V, hVM, u, hpV, hpD, _, _, _, hu, hTrace⟩ :=
    later_positive_mask_contact Q hQ H hH p hp hl hNSp
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBT := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
  have hpM : p ∈ M := mem_maskA (X := X) Sec hSec.isWellFormed hSec.one_le_d
    (Nat.succ_pos n) H hBT ((HironakaG8MemberLoci.level_eq_of_E_eq
      (A := P) (B := Sec) rfl H p) ▸ hPos) hNS
  let W := V ⊓ M
  have hWV : W ≤ V := inf_le_left
  have hWM : W ≤ M := inf_le_right
  have hWP : W ≤ maskA P H p := le_trans hWV hVM
  have hP := properNormalMarked_isInvDomain Q hQ
  have hPBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hPT := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hBI : IsInvDomain (k + 1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hPBar H hPT
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hBI.isWellFormed _
  have hDown := isTangentDirectionAlong_of_open_pullback K.N hK.isClosedSubmanifold_N
    K.ideal hK.isCoherent K.d V univ u hu
  have hVeq : (Subtype.val : V → Y) '' (univ : Set V) = (V : Set Y) := by
    ext x
    exact ⟨fun ⟨z, _, hz⟩ => hz ▸ z.property, fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩⟩
  rw [hVeq] at hDown
  let L := positiveMemberOn P H p W
  have hOnW : IsTangentDirectionAlong K.N K.ideal K.d W u :=
    ⟨W.isOpen, fun y hy => hDown.mem y (hWV hy),
      fun y hy => hDown.multiplicity_one y (hWV hy)⟩
  have hT : IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) :=
    isTangentDirectionAlong_pullback_val W
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) hOnW
  have hD : L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D := by
    ext z
    exact Set.ext_iff.mp hTrace (Opens.inclusion hWV z)
  have hL : IsInvDomain k L := by
    simpa using positive_member_domain_on_subwindow (Nat.succ_pos n) P hP H hPT p hl W hWP
  obtain ⟨hC, hS⟩ := later_contact_domain_on_section_mask Q hQ H hH p hl W hWM u hT hD
  exact ⟨W, u, ⟨hpV, hpM⟩, hpD, hWM, hWP, hL, hC, hS, hT, hD⟩

end Hironaka.HironakaG1LaterContactRecursiveDomain
