import Hironaka.Resolution.HironakaG1RecursiveMemberValueTransport
import Hironaka.Resolution.HironakaG8LocalCompanion
import Hironaka.Resolution.HironakaG8PowerCompanionLocal

/-! Unequal-mark original companions: derive their full local relation
from actual whole powers and E4c, on the intersection of the original masks.
Blueprint FIRST: hironaka-g1-scaled-companion-local.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ScaledCompanionLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  RelativePrincipalizationSpan IdealWeightPowers DivisorExponentAlong
  HironakaActualPowerBoundaryExponents HironakaG8LocalHistory HironakaG8LocalPower
  HironakaG8MixedBoundaryExponents HironakaG8LocalCompanion HironakaG8E4cCompanion
  HironakaG8PowerCompanionLocal HironakaG8PowerNonmonomialOrder
  HironakaG8ScaledNonmonomialHistory HironakaG8ScaledExponentHistory
  HironakaG11PresClassTransport InvDomainTowerAlong HironakaCoherentTransformExtension
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase
  HironakaG1GenericPositiveClassData HironakaG1RecursiveMemberValueTransport StepOneValue

/-- The actual common WHOLE powers have ordinary exponent agreement;
the input equality is only on the true original cosupport. -/
theorem commonPower_expAgree_of_scaled {n k l : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x) :
    ExpAgree (powerMarked P Q.d) (powerMarked Q P.d) := by
  intro H hH x hx hxH
  have hxP : x ∈ P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hx
  change divExpAlong n P.N (idealPow P.ideal Q.d) H x = divExpAlong n Q.N (idealPow Q.ideal P.d) H x
  rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hQ.one_le_d,
    divExpAlong_idealPow hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hP.one_le_d]
  exact hInitial H hH x hxP hxH

/-- Normalized exponents on the actual cosupport restrict to a genuine
open through full powers, with no all-ambient exponent premise. -/
theorem scaled_initial_exponents_restrict {n k l : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (W : Opens X) :
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) P
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) Q
    ∀ H ∈ P'.E, ∀ x ∈ P'.cosupp, x ∈ H →
      Q'.d * divExpAlong n P'.N P'.ideal H x = P'.d * divExpAlong n Q'.N Q'.ideal H x := by
  let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) P
  let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) Q
  have hP' := isInvDomain_pullback_val W hP
  have hQ' := isInvDomain_pullback_val W hQ
  have hPP := powerMarked_isInvDomain P hP hQ.one_le_d
  have hQQ := powerMarked_isInvDomain Q hQ hP.one_le_d
  have hExp := commonPower_expAgree_of_scaled P Q hP hQ hInitial
  have hExpW := expAgree_pullback_val
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hPP.isWellFormed.isCoherent hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQQ.isWellFormed.isCoherent hg) hExp W
  rw [pullback_powerMarked (M := X) (M' := CMfd.of (n := n) W)
      (f := (Subtype.val : W → X)) contMDiff_subtype_val P hP.isWellFormed.isCoherent Q.d,
    pullback_powerMarked (M := X) (M' := CMfd.of (n := n) W)
      (f := (Subtype.val : W → X)) contMDiff_subtype_val Q hQ.isWellFormed.isCoherent P.d] at hExpW
  dsimp only
  intro H hH x hx hxH
  have hxPow : x ∈ (powerMarked P' Q.d).cosupp := by
    rw [powerMarked_cosupp P' hP' hQ.one_le_d]
    exact hx
  have h := hExpW H hH x hxPow hxH
  change divExpAlong n P'.N (idealPow P'.ideal Q.d) H x = divExpAlong n Q'.N (idealPow Q'.ideal P.d) H x at h
  rw [divExpAlong_idealPow hP'.isWellFormed.isClosedSubmanifold_N hP'.isWellFormed.isCoherent hQ.one_le_d,
    divExpAlong_idealPow hQ'.isWellFormed.isClosedSubmanifold_N hQ'.isWellFormed.isCoherent hP.one_le_d] at h
  exact h

/-- The full local relation of two ORIGINAL unequal-mark companions is
derived via common whole powers. The second raw-order bound is internal. -/
theorem companion_local_of_scaled_exponents {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p) (hscale : Q.d * o = P.d * p)
    (hbound : ∀ x ∈ P.cosupp, x ∉ ordGe P (o+1)) :
    LocWPEquiv (companionOf n P o) (companionOf n Q p) := by
  have hboundQ : ∀ x ∈ Q.cosupp, x ∉ ordGe Q (p+1) := by
    intro x hx hHigh
    have hxP : x ∈ P.cosupp := hL.wEquiv.cosupp_eq.symm ▸ hx
    have hr := scaled_nmOrd_of_initial_exponents hn P Q hP hQ hN.symm hL.wEquiv.1.symm hL
      hInitial (.refl : BlowupTower X X) trivial x hxP
    change Q.d * nmOrd P x = P.d * nmOrd Q x at hr
    have hq := (mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt (Q.cosupp_subset_N hx) (p+1)).mp hHigh
    have hd := hP.one_le_d
    have he := hQ.one_le_d
    have hgt : o < nmOrd P x := by nlinarith
    exact hbound x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt (P.cosupp_subset_N hxP) (o+1)).mpr (by omega))
  have hPP := powerMarked_isInvDomain P hP hQ.one_le_d
  have hQQ := powerMarked_isInvDomain Q hQ hP.one_le_d
  have hCommon := locEquiv_commonMark (κ := Kinds.wp) rfl hL hP hQ
  have hExp := commonPower_expAgree_of_scaled P Q hP hQ hInitial
  have hboundPP : ∀ x ∈ (powerMarked P Q.d).cosupp, x ∉ ordGe (powerMarked P Q.d) (Q.d*o+1) := by
    intro x hx hHigh
    have hxP : x ∈ P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hx
    have hxN := P.cosupp_subset_N hxP
    have hq := (mem_ordGe_iff hPP.isWellFormed hPP.isNonzeroAlongAt hxN (Q.d*o+1)).mp hHigh
    rw [nmOrd_powerMarked hn P hP hQ.one_le_d hxN] at hq
    have hgt : o < nmOrd P x := Nat.lt_of_mul_lt_mul_left (by omega : Q.d*o < Q.d*nmOrd P x)
    exact hbound x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxN (o+1)).mpr (by omega))
  have hNP : (powerMarked Q P.d).N = (powerMarked P Q.d).N := hN.symm
  have hMiddle := locWPEquiv_companionOf hCommon.1 hPP hQQ hNP hCommon.2.symm hExp hn
    (Nat.mul_pos hQ.one_le_d ho) hboundPP
  have hMiddle' : LocWPEquiv (companionOf n (powerMarked P Q.d) (Q.d*o))
      (companionOf n (powerMarked Q P.d) (P.d*p)) := by simpa only [hscale] using hMiddle
  have hLeft := locWPEquiv_companionOf_powerMarked hn P hP hQ.one_le_d ho hbound
  have hRight := locWPEquiv_companionOf_powerMarked hn Q hQ hP.one_le_d hp hboundQ
  exact hLeft.trans (hMiddle'.trans hRight.symm)

/-- The genuine intersection of the two original raw-order masks supplies
the bounded open. Its two factors are never asserted equal. -/
theorem scaled_mask_intersection_companions_local {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p) (hscale : Q.d * o = P.d * p) :
    let W := ordMask P o ⊓ ordMask Q p
    LocWPEquiv
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) P) o)
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) Q) p) := by
  let W := ordMask P o ⊓ ordMask Q p
  let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) P
  let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) Q
  have hP' := isInvDomain_pullback_val W hP
  have hQ' := isInvDomain_pullback_val W hQ
  have hN' : P'.N = Q'.N := by change (Subtype.val : W → X) ⁻¹' P.N = (Subtype.val : W → X) ⁻¹' Q.N; rw [hN]
  have hL' := hL.restrict W
  have hInitial' := scaled_initial_exponents_restrict P Q hP hQ hInitial W
  have hbound : ∀ x ∈ P'.cosupp, x ∉ ordGe P' (o+1) := by
    intro x _hx hHigh
    have hHigh' := (mem_ordGe_pullback_val_iff hn hP.isWellFormed hP.isNonzeroAlongAt W (o+1) x).mp hHigh
    exact (mem_ordMask_iff hn hP.isWellFormed hP.isNonzeroAlongAt o x.val).mp x.property.1 hHigh'
  exact companion_local_of_scaled_exponents hn P' Q' hP' hQ' hN' hL' hInitial' o p ho hp hscale hbound

/-- For actual original positive-member records and every true suffix
prefix, the companion local relation on the actual intersected masks is
produced internally. No caller companion/normalized-record packet is used. -/
theorem positive_member_prefix_scaled_companions_local {n kA kB : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) (y : Y) (s : ℕ) (hl : level A T y = s+1) :
    let O := maskA A T y
    let P := positiveMemberOn A T y O
    let Q := positiveMemberOn B T y O
    ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) O) Z), IsGeoTestTower P S →
      ∀ (o p : ℕ), 1 ≤ o → 1 ≤ p → (geoTransformAlong Q S).d * o = (geoTransformAlong P S).d * p →
        let W := ordMask (geoTransformAlong P S) o ⊓ ordMask (geoTransformAlong Q S) p
        LocWPEquiv
          (companionOf n (M := CMfd.of (n := n) W)
            (MarkedIdeal.pullback (Subtype.val : W → Z) (geoTransformAlong P S)) o)
          (companionOf n (M := CMfd.of (n := n) W)
            (MarkedIdeal.pullback (Subtype.val : W → Z) (geoTransformAlong Q S)) p) := by
  let O := maskA A T y
  let P := positiveMemberOn A T y O
  let Q := positiveMemberOn B T y O
  obtain ⟨hP,hQ,hNP,hEP,hLocal,hInitial⟩ := positive_member_class_data hn A B hA hB hN hL T hT y s hl
  change IsInvDomain (kA-1) P at hP
  change IsInvDomain (kB-1) Q at hQ
  change P.N = Q.N at hNP
  change P.E = Q.E at hEP
  change LocWPEquiv P Q at hLocal
  dsimp only
  intro Z S hS o p ho hp hscale
  have hSQ := (hLocal.wEquiv.2 S).1.mp hS
  have hPS := isInvDomain_geoTransformAlong hP S hS
  have hQS := isInvDomain_geoTransformAlong hQ S hSQ
  have hNS := geoTransformAlong_N_eq_of_N_eq hNP S
  have hLS := hLocal.geoTransformAlong S hS
  have hIS := scaled_exponents_of_initial_agreement P Q hP hQ hNP.symm hEP.symm hLocal hInitial S hS
  have hIS' : ∀ H ∈ (geoTransformAlong P S).E, ∀ x ∈ (geoTransformAlong P S).cosupp, x ∈ H →
      (geoTransformAlong Q S).d * divExpAlong n (geoTransformAlong P S).N (geoTransformAlong P S).ideal H x =
        (geoTransformAlong P S).d * divExpAlong n (geoTransformAlong Q S).N (geoTransformAlong Q S).ideal H x := by
    simpa only [d_geoTransformAlong] using hIS
  exact scaled_mask_intersection_companions_local hn (geoTransformAlong P S) (geoTransformAlong Q S)
    hPS hQS hNS hLS hIS' o p ho hp hscale

end
end Hironaka.HironakaG1ScaledCompanionLocal
