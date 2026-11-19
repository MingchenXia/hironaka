import Hironaka.Resolution.HironakaG1ActualLaterBornCut
import Hironaka.Resolution.HironakaG8LocalRestrictEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterOrderMaskSupportedLocal
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue
  NonmonomialOrderTail InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1PositiveNormalPhase HironakaG1LaterPositiveMaskContact
  HironakaG1PositiveNormalRepairCentres HironakaActualSectionBoundaryGeometry
  HironakaG1RecursiveMemberValueTransport HironakaG1SeparateCarrierMemberCut
  HironakaG8HomStable HironakaG8LocalHistory HironakaG8LocalRestrictEquiv
  RelativePrincipalizationSpan MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  HironakaActualOpenZeroSectionDifferentials GeneralCompare MarkedIdealOperationsAlong.MarkedIdeal

set_option maxHeartbeats 800000 in
/-- The part of an order mask lying over a domain window inherits the domain
of the literal supported record, even when its larger representative does not. -/
theorem supported_domain_on_nested_order_window {n k : ℕ} {Y : CMfd.{0} n}
    (K : MarkedIdeal n Y) (hK : K.ideal.IsCoherent) {M O : Opens Y} (hMO : M ≤ O)
    (hM : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : M → Y) K))
    (C : Opens (CMfd.of (n := n) O)) :
    let A := CMfd.of (n := n) O
    let B := CMfd.of (n := n) C
    let V₀ := MaxLocusLocal.nestedOpens O M
    let V := MaxLocusLocal.nestedOpens C V₀
    let R₀ : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : O → Y) K
    let R : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : C → A) R₀
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → B) R) := by
  intro A B V₀ V R₀ R
  let Rm : MarkedIdeal n (CMfd.of (n := n) M) := MarkedIdeal.pullback (Subtype.val : M → Y) K
  have h₀ : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V₀ → A) R₀) := by
    rw [MaxLocusLocal.pullback_val_pullback_val hK hMO]
    exact isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hMO)
      (show IsInvDomain k Rm from hM)
  let N := C ⊓ V₀
  have hNV : N ≤ V₀ := inf_le_right
  have hNC : N ≤ C := inf_le_left
  have hR₀ := GermIdealPullbackCalculus.isCoherent_pullback
    (f := (Subtype.val : O → Y)) contMDiff_subtype_val hK
  have hAlias : V = MaxLocusLocal.nestedOpens C N := by
    ext z
    exact ⟨fun hz => ⟨z.property, hz⟩, fun hz => hz.2⟩
  have hN : IsInvDomain k (MarkedIdeal.pullback (M' := CMfd.of (n := n) N)
      (Subtype.val : N → A) R₀) := by
    have h := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens V₀ N) h₀
    have h' := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hNV).symm h
    rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hR₀ hNV] at h'
  rw [hAlias, MaxLocusLocal.pullback_val_pullback_val hR₀ hNC]
  exact isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hNC) hN

set_option maxHeartbeats 1400000 in
/-- At a supported nonspecial anchor the literal supported member has its
ordinary domain on the part of the exact order mask over the section mask.
A local restricted-ideal comparison with the companion then gives its
local weak class on the same window. -/
theorem later_supported_reference_on_exact_order_window {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hl : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let O := maskA P H p
    let M := maskA Sec H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let V := MaxLocusLocal.nestedOpens C (MaxLocusLocal.nestedOpens O M)
    let J := compAt L L.d (.refl : BlowupTower A A)
    let D := CMfd.of (n := n + 1) V
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    let Rv := MarkedIdeal.pullback (M' := D) (Subtype.val : V → B) R
    let Jv := MarkedIdeal.pullback (M' := D) (Subtype.val : V → B) J
    let Lv := MarkedIdeal.pullback (M' := D) (Subtype.val : V → B)
      (MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) L)
    (∀ a : C, a.val.val = p → a ∈ V) ∧ IsInvDomain k Rv ∧
      (RestrictEquiv Lv Jv → LocWPEquiv (X := D) Jv Rv) := by
  intro X P Sec O M A L C B V J D R Rv Jv Lv
  have hSec : IsInvDomain (k + 1) Sec := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBT := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
  have hlSec : level Sec H p = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (A := P) (B := Sec) rfl H p).symm.trans hl
  have hPos : 0 < level P H p := hl ▸ Nat.succ_pos s
  have hMO : M ≤ O := positive_normal_section_mask_subset Q hQ H hH p hPos
  have hpM : p ∈ M := mem_maskA Sec hSec.isWellFormed hSec.one_le_d (Nat.succ_pos n)
    H hBT (hlSec ▸ Nat.succ_pos s) hNS
  let B' := geoTransformAlong (barMarked Sec) H
  let K := memberRestrict B' (membersThrough B'.E (origMembers Sec H) p)
  have hB' := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) Sec hSec) H hBT
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB'.isWellFormed _
  have hM : IsInvDomain k (positiveMemberOn Sec H p M) := by
    simpa using positive_member_domain_on_subwindow (Nat.succ_pos n) Sec hSec H hBT p hlSec M le_rfl
  have hRv : IsInvDomain k Rv := supported_domain_on_nested_order_window K hK.isCoherent hMO hM C
  refine ⟨fun a ha => ?_, hRv, fun hCmp => ?_⟩
  · change a.val.val ∈ M
    exact ha ▸ hpM
  have hL : IsInvDomain (k + 1) L := padded_lower_isInvDomain Q hQ H hH p hl
  have hJ : IsInvDomain (k + 1) J :=
    isInvDomain_compAt (Nat.succ_pos n) hL.one_le_d (.refl : BlowupTower A A) hL
  have hLv : IsInvDomain (k + 1) Lv := isInvDomain_pullback_val V (isInvDomain_pullback_val C hL)
  have hJv : IsInvDomain (k + 1) Jv := isInvDomain_pullback_val V hJ
  have hLr : LocWPEquiv (X := A) L (positiveMemberOn Sec H p O) :=
    (positive_lower_section_class Q hQ H hH p).1
  exact (locWPEquiv_of_restrictEquiv hLv hJv hCmp).symm.trans ((hLr.restrict C).restrict V)

end
end Hironaka.HironakaG1LaterOrderMaskSupportedLocal
