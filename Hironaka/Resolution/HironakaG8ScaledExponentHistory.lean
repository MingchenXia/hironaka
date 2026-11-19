import Hironaka.Resolution.HironakaG8CompanionScaledHistory

/-! Initial scaled exponents persist through actual controlled histories.
Blueprint: `hironaka-g8-scaled-exponent-history.tex`. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ScaledExponentHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers ResolutionInvariantSpec
  DivisorExponentAlong IdealWeightPowers HironakaG8LocalHistory HironakaG8LocalPower
  HironakaG8BornExponents HironakaG8MixedBoundaryExponents HironakaActualPowerBoundaryExponents
  HironakaActualOriginalPowerTransform HironakaG8DomainExponents HironakaG11InvBMClass InvDomainTowerAlong
variable {n : ℕ} {X : CMfd.{0} n}

/-- Cross-scaled boundary exponents at the common cosupport persist through
every actual controlled test tower of the common-carrier pair. -/
theorem scaled_exponents_of_initial_agreement {k l : ℕ}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N = P.N) (_hE : Q.E = P.E) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    ∀ H ∈ (geoTransformAlong P T).E, ∀ y ∈ (geoTransformAlong P T).cosupp, y ∈ H →
      Q.d * divExpAlong n (geoTransformAlong P T).N (geoTransformAlong P T).ideal H y =
      P.d * divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal H y := by
  have hCommon := locEquiv_commonMark (κ := Kinds.wp) rfl hL hP hQ
  have hPP := powerMarked_isInvDomain P hP hQ.one_le_d
  have hQP := powerMarked_isInvDomain Q hQ hP.one_le_d
  have hDim : SameCarrierDim (powerMarked P Q.d) (powerMarked Q P.d) := by
    apply SameCarrierDim.of_N_eq
    change P.N = Q.N
    exact hN.symm
  have hExp : HironakaG8MixedBoundaryExponents.ExpAgree (powerMarked P Q.d) (powerMarked Q P.d) := by
    intro H hH y hy hyH
    have hyP : y ∈ P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hy
    change divExpAlong n P.N (idealPow P.ideal Q.d) H y = divExpAlong n Q.N (idealPow Q.ideal P.d) H y
    rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hQ.one_le_d,
      divExpAlong_idealPow hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hP.one_le_d]
    have hHP : H ∈ P.E := hH
    exact hInitial H hHP y hyP hyH
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hAP := original_power_transform P hP Q.d hQ.one_le_d T hT
  have hAQ := original_power_transform Q hQ P.d hP.one_le_d T hTQ
  have hag := locWPEquiv_expAgree_geoTransformAlong hCommon.1 hPP hQP hDim hCommon.2.symm hExp T hAP.1
  intro H hH y hy hyH
  have hHE : H ∈ (geoTransformAlong (powerMarked P Q.d) T).E := by rw [hAP.2.E_eq]; exact hH
  have hyC : y ∈ (geoTransformAlong (powerMarked P Q.d) T).cosupp := by
    rw [hAP.2.cosupp_eq, powerMarked_cosupp _ hPT hQ.one_le_d]
    exact hy
  have heq := hag H hHE y hyC hyH
  rw [divExpAlong_eq_of_restrictEquiv hAP.2, divExpAlong_eq_of_restrictEquiv hAQ.2] at heq
  change divExpAlong n (geoTransformAlong P T).N (idealPow (geoTransformAlong P T).ideal Q.d) H y =
    divExpAlong n (geoTransformAlong Q T).N (idealPow (geoTransformAlong Q T).ideal P.d) H y at heq
  rw [divExpAlong_idealPow hPT.isWellFormed.isClosedSubmanifold_N hPT.isWellFormed.isCoherent hQ.one_le_d,
    divExpAlong_idealPow hQT.isWellFormed.isClosedSubmanifold_N hQT.isWellFormed.isCoherent hP.one_le_d] at heq
  exact heq
end
end Hironaka.HironakaG8ScaledExponentHistory
