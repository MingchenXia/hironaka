import Hironaka.Resolution.HironakaG8E4cCompanion
import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Resolution.HironakaG8BornExponents
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG8DomainExponents

/-! Common-mark companion boundary exponents through actual controlled tests.
Blueprint: `hironaka-g8-companion-scaled-history.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CompanionScaledHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers ResolutionInvariantSpec
  DivisorExponentAlong CompanionRebase CompanionReductionAlong InvDomainCompanion IdealWeightPowers
  HironakaG8E4cCompanion HironakaG8LocalHistory HironakaG8LocalPower
  HironakaG8BornExponents HironakaG8MixedBoundaryExponents
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8DomainExponents HironakaG11InvBMClass InvDomainTowerAlong
variable {n : ℕ} {X : CMfd.{0} n}

/-- The two companions have zero initial boundary exponents, even with unequal
marks. Their common-mark powers retain exponent agreement along every actual
controlled test of the first companion. -/
theorem companion_common_mark_exponents {k l : ℕ} (hn : 0 < n)
    (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : B.N = A.N) (hE : B.E = A.E) {o p : ℕ} (ho : 1 ≤ o) (hp : 1 ≤ p)
    (hL : LocWPEquiv (companionOf n A o) (companionOf n B p))
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (companionOf n A o) T) :
    let C := companionOf n A o
    let D := companionOf n B p
    HironakaG8MixedBoundaryExponents.ExpAgree (geoTransformAlong (powerMarked C D.d) T)
      (geoTransformAlong (powerMarked D C.d) T) := by
  let C := companionOf n A o
  let D := companionOf n B p
  have hC : IsInvDomain k C := isInvDomain_companionAlong hn hA ho
  have hD : IsInvDomain l D := isInvDomain_companionAlong hn hB hp
  have hCN : C.N = A.N := by simp [C,companionOf]
  have hDN : D.N = B.N := by simp [D,companionOf]
  have hCE : C.E = A.E := by simp [C,companionOf]
  have hDE : D.E = B.E := by simp [D,companionOf]
  have hCommon := locEquiv_commonMark (κ := Kinds.wp) rfl hL hC hD
  have hCP := powerMarked_isInvDomain C hC hD.one_le_d
  have hDP := powerMarked_isInvDomain D hD hC.one_le_d
  have hDim : SameCarrierDim (powerMarked C D.d) (powerMarked D C.d) := by
    apply SameCarrierDim.of_N_eq
    change C.N = D.N
    rw [hCN,hDN,hN]
  have hExp : HironakaG8MixedBoundaryExponents.ExpAgree (powerMarked C D.d) (powerMarked D C.d) := by
    intro H hH y hy hyH
    have hyC : y ∈ C.cosupp := (powerMarked_cosupp C hC hD.one_le_d) ▸ hy
    have hyA : y ∈ A.N := by rw [←hCN]; exact C.cosupp_subset_N hyC
    have hHA : H ∈ A.E := by simpa [powerMarked,hCE] using hH
    change divExpAlong n C.N (idealPow C.ideal D.d) H y = divExpAlong n D.N (idealPow D.ideal C.d) H y
    rw [divExpAlong_idealPow hC.isWellFormed.isClosedSubmanifold_N hC.isWellFormed.isCoherent hD.one_le_d,
      divExpAlong_idealPow hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hC.one_le_d]
    have hzeroC := divExpAlong_companionOf_eq_zero hn hA.isWellFormed hA.isNonzeroAlongAt o hyA hHA hyH
    have hzeroD := divExpAlong_companionOf_eq_zero hn hB.isWellFormed hB.isNonzeroAlongAt p (hN ▸ hyA) (hE ▸ hHA) hyH
    have hzeroC' : divExpAlong n C.N C.ideal H y = 0 := by rw [hCN]; exact hzeroC
    have hzeroD' : divExpAlong n D.N D.ideal H y = 0 := by rw [hDN]; exact hzeroD
    simp [hzeroC',hzeroD']
  have hTest : IsGeoTestTower (powerMarked C D.d) T :=
    ((locEquiv_powerMarked (κ := Kinds.wp) rfl C hC hD.one_le_d).wEquiv.2 T).1.mp hT
  exact locWPEquiv_expAgree_geoTransformAlong hCommon.1 hCP hDP hDim hCommon.2.symm hExp T hTest

/-- The actual, unpowered companion transforms have cross-scaled boundary
exponents at every point of the common cosupport along each controlled test. -/
theorem companion_scaled_exponents {k l : ℕ} (hn : 0 < n)
    (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain l B)
    (hN : B.N = A.N) (hE : B.E = A.E) {o p : ℕ} (ho : 1 ≤ o) (hp : 1 ≤ p)
    (hL : LocWPEquiv (companionOf n A o) (companionOf n B p))
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (companionOf n A o) T) :
    let C := companionOf n A o
    let D := companionOf n B p
    ∀ H ∈ (geoTransformAlong C T).E, ∀ y ∈ (geoTransformAlong C T).cosupp, y ∈ H →
      D.d * divExpAlong n (geoTransformAlong C T).N (geoTransformAlong C T).ideal H y =
      C.d * divExpAlong n (geoTransformAlong D T).N (geoTransformAlong D T).ideal H y := by
  let C := companionOf n A o
  let D := companionOf n B p
  have hC : IsInvDomain k C := isInvDomain_companionAlong hn hA ho
  have hD : IsInvDomain l D := isInvDomain_companionAlong hn hB hp
  have hTD : IsGeoTestTower D T := (hL.wEquiv.2 T).1.mp hT
  have hCT := isInvDomain_geoTransformAlong hC T hT
  have hDT := isInvDomain_geoTransformAlong hD T hTD
  have hPC := original_power_transform C hC D.d hD.one_le_d T hT
  have hPD := original_power_transform D hD C.d hC.one_le_d T hTD
  have hag := companion_common_mark_exponents hn A B hA hB hN hE ho hp hL T hT
  dsimp only
  intro H hH y hy hyH
  have hHE : H ∈ (geoTransformAlong (powerMarked C D.d) T).E := by
    rw [hPC.2.E_eq]
    exact hH
  have hyC : y ∈ (geoTransformAlong (powerMarked C D.d) T).cosupp := by
    rw [hPC.2.cosupp_eq, powerMarked_cosupp _ hCT hD.one_le_d]
    exact hy
  have heq := hag H hHE y hyC hyH
  rw [divExpAlong_eq_of_restrictEquiv hPC.2, divExpAlong_eq_of_restrictEquiv hPD.2] at heq
  change divExpAlong n (geoTransformAlong C T).N (idealPow (geoTransformAlong C T).ideal D.d) H y =
    divExpAlong n (geoTransformAlong D T).N (idealPow (geoTransformAlong D T).ideal C.d) H y at heq
  rw [divExpAlong_idealPow hCT.isWellFormed.isClosedSubmanifold_N hCT.isWellFormed.isCoherent hD.one_le_d,
    divExpAlong_idealPow hDT.isWellFormed.isClosedSubmanifold_N hDT.isWellFormed.isCoherent hC.one_le_d] at heq
  exact heq
end
end Hironaka.HironakaG8CompanionScaledHistory
