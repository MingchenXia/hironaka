import Hironaka.Resolution.HironakaG1ProperCarrierNormalLocalClass
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial
import Hironaka.Resolution.HironakaG1CoefficientRecodingCanonical

/-! Actual original canonical data for the kept proper-normal lower.
Every tight domain/gap/exponent premise is derived from ordinary Q.
The actual original family uses the SAME chronological tower throughout.
Blueprint FIRST: hironaka-g1-proper-normal-lower-canonical.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalLowerCanonical
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver HomogenizedIdealAlong
  CoefficientIdealRestriction StepOneValue DivisorExponentAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ChosenCommonContactClassData
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG8GapNormalizedExponent
  HironakaG8HomStable HironakaActualInitialNonmonomialCoefficientBoundary
  HironakaActualCoefficientDivisorExponentGap HironakaG1CoefficientBarClassData
  HironakaG1CoefficientCarrierClassData HironakaG1OriginalInvariantClassFunctorial
  HironakaG1CoefficientRecodingCanonical

private theorem section_domain {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) : IsInvDomain k (sectionMarked Q) :=
  section_projected_domain k Q.N Q.E Q.ideal Q.d hQ

/-- Ordinary Q gives the ACTUAL tight domains, full labels/true marks,
both coefficient gaps and INITIAL normalized/exact exponent agreement. -/
theorem kept_normal_lower_data {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    let R := keptNormalLower Q
    let V := sectionBarCoefficient Q
    IsInvDomain k R ∧ IsInvDomain k V ∧ R.N = V.N ∧ R.E = V.E ∧ R.d = V.d ∧
      LocWPEquiv (X := CMfd.of (n := n+1) (productOpen U)) R V ∧
      SameCarrierDim (X := CMfd.of (n := n+1) (productOpen U)) R V ∧
      HasCosupportGap (X := CMfd.of (n := n+1) (productOpen U)) R ∧
      HasCosupportGap (X := CMfd.of (n := n+1) (productOpen U)) V ∧
      (∀ H ∈ R.E, ∀ x ∈ R.cosupp, x ∈ H →
        V.d * divExpAlong (n+1) R.N R.ideal H x = R.d * divExpAlong (n+1) V.N V.ideal H x) ∧
      HironakaG11InvBMClass.ExpAgree (X := CMfd.of (n := n+1) (productOpen U)) R V := by
  let P := properNormalMarked Q
  let S := sectionMarked Q
  let R := keptNormalLower Q
  let V := sectionBarCoefficient Q
  have hP := properNormalMarked_isInvDomain Q hQ
  have hS := section_domain Q hQ
  have hBP : IsInvDomain (k+1) (barMarked (X := CMfd.of (n := n+1) (productOpen U)) P) :=
    HironakaCoherentTransformExtension.isInvDomain_barMarked
      (X := CMfd.of (n := n+1) (productOpen U)) P hP
  have hBS : IsInvDomain k (barMarked (X := CMfd.of (n := n+1) (productOpen U)) S) :=
    HironakaCoherentTransformExtension.isInvDomain_barMarked
      (X := CMfd.of (n := n+1) (productOpen U)) S hS
  have hV : IsInvDomain k V := coefficient_isInvDomain _ hBS
  obtain ⟨hN,hE,hd⟩ := keptNormalLower_fields Q
  have hL := keptNormalLower_locWPEquiv_sectionBarCoefficient Q hQ
  have hRI : R.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hBP.isWellFormed.isCoherent hBP.isWellFormed.isClosedSubmanifold_N
  have hdR : 1 ≤ R.d := hd.symm ▸ hV.one_le_d
  have hR : IsInvDomain k R := isInvDomain_of_sameCarrier_cosupp
    (X := CMfd.of (n := n+1) (productOpen U)) R V hV hRI hdR hN hE hL.cosupp_eq_base
  have hDim : SameCarrierDim (X := CMfd.of (n := n+1) (productOpen U)) R V :=
    SameCarrierDim.of_N_eq hN
  have hGapR : HasCosupportGap (X := CMfd.of (n := n+1) (productOpen U)) R := by
    intro x _hx hx
    have hGap := coefficient_restriction_cosupport_gap
      (barMarked (X := CMfd.of (n := n+1) (productOpen U)) P)
      hBP.isWellFormed.isClosedSubmanifold_N hBP.isWellFormed.isCoherent hBP.one_le_d
      (liftedCarrier Q.N) (fun _ hz => hz.1)
    change x∈GermIdealOrder.cosupport (n+1) (liftedCarrier Q.N)
      (coeffMarkedAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) P)).ideal
      (coeffMarkedAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) P)).d
    rw [←hGap]
    exact hx
  have hGapV : HasCosupportGap (X := CMfd.of (n := n+1) (productOpen U)) V :=
    coefficient_hasCosupportGap _ hBS
  have hNorm := normalized_exponents_of_gap_sameCarrierDim (X := CMfd.of (n := n+1) (productOpen U))
    (Nat.succ_pos n) R V hR hV hL hDim hGapR hGapV
  refine ⟨hR,hV,hN,hE,hd,hL,hDim,hGapR,hGapV,hNorm,?_⟩
  intro H hH x hx hxH
  have h := hNorm H hH x hx hxH
  rw [hd] at h
  exact Nat.eq_of_mul_eq_mul_left hV.one_le_d h

/-- The LITERAL original family derives the second-side CAN on the SAME T. -/
theorem invFamily_isCanonical_kept_section_iff {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) :
    IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T ↔
      IsCanonical (sectionBarCoefficient Q)
        ((invFamily (Nat.succ_pos n) k).inv (sectionBarCoefficient Q)) T := by
  obtain ⟨hR,hV,_hN,hE,hd,hL,hDim,_hGapR,_hGapV,_hNorm,hExp⟩ := kept_normal_lower_data Q hQ
  exact (classFunctorialFor_invFamily (Nat.succ_pos n) k).canonical_iff
    (X := CMfd.of (n := n+1) (productOpen U))
    (keptNormalLower Q) (sectionBarCoefficient Q) hR hV hL hd hE hDim hExp T

/-- FULL actual original values of the two SAME-mark literal lower records,
with no reflexive restart or supplied future comparison. -/
theorem invFamily_values_kept_section {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T)
    (y : Y) (hy : y∈(geoTransformAlong (keptNormalLower Q) T).cosupp) :
    (invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T y=
      (invFamily (Nat.succ_pos n) k).inv (sectionBarCoefficient Q) T y := by
  obtain ⟨hR,hV,_hN,hE,hd,hL,hDim,_hGapR,_hGapV,_hNorm,hExp⟩ := kept_normal_lower_data Q hQ
  exact (classFunctorialFor_invFamily (Nat.succ_pos n) k).inv_eq
    (X := CMfd.of (n := n+1) (productOpen U))
    (keptNormalLower Q) (sectionBarCoefficient Q) hR hV hL hd hE hDim hExp T hCan y hy

/-- ENTIRE original maximum centre of the actual kept normal lower. -/
theorem invFamily_maxLocus_kept_section {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T) :
    maxLocus ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T)
        (geoTransformAlong (keptNormalLower Q) T).cosupp=
      maxLocus ((invFamily (Nat.succ_pos n) k).inv (sectionBarCoefficient Q) T)
        (geoTransformAlong (sectionBarCoefficient Q) T).cosupp := by
  obtain ⟨hR,_hV,_hN,_hE,_hd,hL,_hDim,_hGapR,_hGapV,_hNorm,_hExp⟩ := kept_normal_lower_data Q hQ
  have hT := (invFamily (Nat.succ_pos n) k).isInvValue.isGeoTestTower_of_isCanonical hR T hCan
  have hCos := (hL.wEquiv.2 T).2 hT
  rw [←hCos]
  exact ResolutionInvariantExt.maxLocus_congr (invFamily_values_kept_section Q hQ T hCan)

/-- Actual kept normal lower versus the GIVEN original SECTION bar;
the differing true marks are retained and both CAN are conclusions. -/
theorem invFamily_isCanonical_kept_barSection_iff {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) :
    IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T ↔
      IsCanonical (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (sectionMarked Q))
        ((invFamily (Nat.succ_pos n) k).inv
          (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (sectionMarked Q))) T :=
  (invFamily_isCanonical_kept_section_iff Q hQ T).trans
    (invFamily_isCanonical_bar_coefficient_iff (n := n+1) (k := k)
      (X := CMfd.of (n := n+1) (productOpen U))
      (Nat.succ_pos n) (sectionMarked Q) (section_domain Q hQ) T).symm

/-- Whole SAME-prefix maximum-centre identity with the original section bar,
without asserting equality of the unequal-mark full raw values. -/
theorem invFamily_maxLocus_kept_barSection {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T) :
    maxLocus ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T)
        (geoTransformAlong (keptNormalLower Q) T).cosupp=
      maxLocus ((invFamily (Nat.succ_pos n) k).inv
          (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (sectionMarked Q)) T)
        (geoTransformAlong (barMarked (X := CMfd.of (n := n+1) (productOpen U)) (sectionMarked Q)) T).cosupp := by
  have hBarCan := (invFamily_isCanonical_kept_barSection_iff Q hQ T).mp hCan
  exact (invFamily_maxLocus_kept_section Q hQ T hCan).trans
    (invFamily_maxLocus_bar_coefficient (n := n+1) (k := k)
      (X := CMfd.of (n := n+1) (productOpen U))
      (Nat.succ_pos n) (sectionMarked Q) (section_domain Q hQ) T hBarCan).symm

end
end Hironaka.HironakaG1ProperNormalLowerCanonical
