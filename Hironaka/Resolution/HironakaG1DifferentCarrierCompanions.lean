import Hironaka.Resolution.HironakaG1IndependentContactScaledHistory
import Hironaka.Resolution.HironakaG8E4cCarrier

/-! Actual unequal-mark companions on different native carriers.
Blueprint FIRST: hironaka-g1-different-carrier-companions.tex.
Full original recursive cuts and weighted normal padding remain separate. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1DifferentCarrierCompanions
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec DivisorExponentAlong
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaG8LocalHistory HironakaG11InvBMClass InvDomainTowerAlong InvDomainCompanion
  HironakaActualPowerBoundaryExponents HironakaG8PowerNonmonomialOrder HironakaG8PowerCompanionLocal
  HironakaG1ScaledCompanionLocal HironakaG1IndependentContactClassData
  HironakaG1IndependentContactScaledHistory HironakaG8SpecialLoci HironakaG8E4cCompanion
  HironakaG8CompanionEquiv HironakaG8E4cCarrier StepOneValue HomogenizedIdealAlong

/-- The actual bounded companions are locally equivalent at unequal native
marks on genuinely different carriers. The second bound is derived. -/
theorem companion_local_sameCarrierDim {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p) (hscale : Q.d * o = P.d * p)
    (hbound : ∀ x ∈ P.cosupp, x ∉ ordGe P (o+1)) :
    LocWPEquiv (companionOf n P o) (companionOf n Q p) := by
  have hboundQ : ∀ x ∈ Q.cosupp, x ∉ ordGe Q (p+1) := by
    intro x hx hHigh
    have hxP : x ∈ P.cosupp := hL.cosupp_eq_base.symm ▸ hx
    have hr := scaled_raw_sameCarrierDim hn P Q hP hQ hL hDim hInitial
      (.refl : BlowupTower X X) trivial x hxP
    change Q.d * nmOrd P x = P.d * nmOrd Q x at hr
    have hq := (mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt (Q.cosupp_subset_N hx) (p+1)).mp hHigh
    have hd := hP.one_le_d
    have he := hQ.one_le_d
    have hgt : o < nmOrd P x := by nlinarith
    exact hbound x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt (P.cosupp_subset_N hxP) (o+1)).mpr (by omega))
  obtain ⟨hPP, hQQ, hCommon, hd, hDimP, hExp⟩ := common_power_class_data P Q hP hQ hL hDim hInitial
  have hboundPP : ∀ x ∈ (powerMarked P Q.d).cosupp, x ∉ ordGe (powerMarked P Q.d) (Q.d*o+1) := by
    intro x hx hHigh
    have hxP : x ∈ P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hx
    have hxN := P.cosupp_subset_N hxP
    have hq := (mem_ordGe_iff hPP.isWellFormed hPP.isNonzeroAlongAt hxN (Q.d*o+1)).mp hHigh
    rw [nmOrd_powerMarked hn P hP hQ.one_le_d hxN] at hq
    have hgt : o < nmOrd P x := Nat.lt_of_mul_lt_mul_left (by omega : Q.d*o < Q.d*nmOrd P x)
    exact hbound x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxN (o+1)).mpr (by omega))
  have hMiddle := locWPEquiv_companionOf_carrier hCommon hPP hQQ hDimP hd hExp hn
    (Nat.mul_pos hQ.one_le_d ho) hboundPP
  have hMiddle' : LocWPEquiv (companionOf n (powerMarked P Q.d) (Q.d*o))
      (companionOf n (powerMarked Q P.d) (P.d*p)) := by simpa only [hscale] using hMiddle
  have hLeft := locWPEquiv_companionOf_powerMarked hn P hP hQ.one_le_d ho hbound
  have hRight := locWPEquiv_companionOf_powerMarked hn Q hQ hP.one_le_d hp hboundQ
  exact hLeft.trans (hMiddle'.trans hRight.symm)

/-- Both genuine mask factors are retained; the whole native companion
class, dimensions and normalized exponents are all conclusions. -/
theorem masked_companion_class_sameCarrierDim {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p) (hscale : Q.d * o = P.d * p) :
    let W := ordMask P o ⊓ ordMask Q p
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) P
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) Q
    let C := companionOf n P' o
    let D := companionOf n Q' p
    IsInvDomain k C ∧ IsInvDomain l D ∧ LocWPEquiv C D ∧ SameCarrierDim C D ∧ C.E = D.E ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  let W := ordMask P o ⊓ ordMask Q p
  let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) P
  let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → X) Q
  let C := companionOf n P' o
  let D := companionOf n Q' p
  have hP' := isInvDomain_pullback_val W hP
  have hQ' := isInvDomain_pullback_val W hQ
  have hL' := hL.restrict W
  have hDim' := sameCarrierDim_pullback_val
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg) hDim W
  have hInitial' := scaled_initial_exponents_restrict P Q hP hQ hInitial W
  have hbound : ∀ x ∈ P'.cosupp, x ∉ ordGe P' (o+1) := by
    intro x _hx hHigh
    have hHigh' := (mem_ordGe_pullback_val_iff hn hP.isWellFormed hP.isNonzeroAlongAt W (o+1) x).mp hHigh
    exact (mem_ordMask_iff hn hP.isWellFormed hP.isNonzeroAlongAt o x.val).mp x.property.1 hHigh'
  have hCD : LocWPEquiv (X := CMfd.of (n := n) W) C D :=
    companion_local_sameCarrierDim hn P' Q' hP' hQ' hL' hDim' hInitial' o p ho hp hscale hbound
  have hC : IsInvDomain k C := isInvDomain_companionAlong (X := CMfd.of (n := n) W) hn hP' ho
  have hD : IsInvDomain l D := isInvDomain_companionAlong (X := CMfd.of (n := n) W) hn hQ' hp
  have hCN : C.N = P'.N := by simp [C, companionOf]
  have hDN : D.N = Q'.N := by simp [D, companionOf]
  have hCE : C.E = P'.E := by simp [C, companionOf]
  have hDE : D.E = Q'.E := by simp [D, companionOf]
  have hSub : C.cosupp ⊆ P'.cosupp := by
    have h := (cosupp_companionOf_geoTransformAlong hP' hn ho hbound
      (.refl : BlowupTower (CMfd.of (n := n) W) (CMfd.of (n := n) W)) trivial).2
    change C.cosupp = ordGe P' o ∩ P'.cosupp at h
    rw [h]
    exact inter_subset_right
  have hDimCD : SameCarrierDim C D := by
    intro x hx j
    rw [hCN, hDN]
    exact hDim' x (hSub hx) j
  refine ⟨hC, hD, hCD, hDimCD, hCD.wEquiv.1, ?_⟩
  intro H hH x hx hxH
  have hxD : x ∈ D.cosupp := hCD.cosupp_eq_base ▸ hx
  have hzeroC : divExpAlong n C.N C.ideal H x = 0 := by
    rw [hCN]
    exact divExpAlong_companionOf_eq_zero (𝔪 := P') hn hP'.isWellFormed hP'.isNonzeroAlongAt o
      (hCN ▸ C.cosupp_subset_N hx) (hCE ▸ hH) hxH
  have hzeroD : divExpAlong n D.N D.ideal H x = 0 := by
    rw [hDN]
    exact divExpAlong_companionOf_eq_zero (𝔪 := Q') hn hQ'.isWellFormed hQ'.isNonzeroAlongAt p
      (hDN ▸ D.cosupp_subset_N hxD) (hDE ▸ (hCD.wEquiv.1 ▸ hH)) hxH
  change D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x
  simp only [hzeroC, hzeroD, Nat.mul_zero]

/-- Ordinary original source data and the SAME given lower suffix derive
the actual different-carrier companions, without a lower-output packet. -/
theorem independent_contact_companion_class {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hDim : SameCarrierDim J K) (hL : LocWPEquiv J K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked J) T).cosupp) (hReg : stepRegime J 0 T y)
    {Z : CMfd.{0} n} (V : BlowupTower (CMfd.of (n := n) (contactMask J K T y)) Z)
    (hV : IsGeoTestTower (ownContact J K T y) V)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p)
    (hscale : (secondOwnContact J K T y).d * o = (ownContact J K T y).d * p) :
    let P := geoTransformAlong (ownContact J K T y) V
    let Q := geoTransformAlong (secondOwnContact J K T y) V
    let W := ordMask P o ⊓ ordMask Q p
    let C := companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Z) P) o
    let D := companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Z) Q) p
    IsInvDomain (kJ-1) C ∧ IsInvDomain (kK-1) D ∧ LocWPEquiv C D ∧ SameCarrierDim C D ∧ C.E = D.E ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  let A := ownContact J K T y
  let B := secondOwnContact J K T y
  obtain ⟨_hyO, hA, hB, hAB, hDimAB, _hE, hInitial⟩ :=
    independent_two_source_contact_class hn J K hJ hK hDim hL hMaxJ hMaxK T hT y hy hReg
  have hVB : IsGeoTestTower B V := (hAB.wEquiv.2 V).1.mp hV
  have hAV := isInvDomain_geoTransformAlong hA V hV
  have hBV := isInvDomain_geoTransformAlong hB V hVB
  have hLV := hAB.geoTransformAlong V hV
  have hDV := sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed hAB.wEquiv hDimAB V hV
  have hXV := scaled_exponents_sameCarrierDim A B hA hB hAB hDimAB hInitial V hV
  have hScaleV : (geoTransformAlong B V).d * o = (geoTransformAlong A V).d * p := by
    simpa only [d_geoTransformAlong] using hscale
  have hXV' : ∀ H ∈ (geoTransformAlong A V).E, ∀ x ∈ (geoTransformAlong A V).cosupp, x ∈ H →
      (geoTransformAlong B V).d * divExpAlong n (geoTransformAlong A V).N (geoTransformAlong A V).ideal H x =
      (geoTransformAlong A V).d * divExpAlong n (geoTransformAlong B V).N (geoTransformAlong B V).ideal H x := by
    simpa only [d_geoTransformAlong] using hXV
  exact masked_companion_class_sameCarrierDim hn (geoTransformAlong A V) (geoTransformAlong B V)
    hAV hBV hLV hDV hXV' o p ho hp hScaleV

end
end Hironaka.HironakaG1DifferentCarrierCompanions
