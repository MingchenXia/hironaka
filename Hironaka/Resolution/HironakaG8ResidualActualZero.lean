import Hironaka.Resolution.HironakaG8ResidualZeroCoeff
import Hironaka.Resolution.HironakaG8CaseTActualAmbient
import Hironaka.Resolution.HironakaG8ClassStepResidual

/-! # Actual successor residual with a zero coefficient exponent -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualActualZero
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  HomogenizedGlueingTower HomogenizedIdealAlongTower TangentDirectionAlong GermIdealOrder DivisorExponentAlong
  StepOneValue HironakaG11InvBMMask HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMLowerTailSucc
  HironakaG8LocalHistory HironakaG8CaseTActualAmbient HironakaG8ClassStepResidual
  HironakaG8ResidualZeroCoeff
open RestrictedIdealExtension (sumIdeal)

/-- At an actual successor stage, truncated coefficient exponent agreement
gives the residual exponent equality when the coefficients are nonzero and
one coefficient exponent is zero. -/
theorem actual_successor_exp_eq_of_zero_coeff
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hd : A.d = B.d) (hE : A.E = B.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) (hTB : IsGeoTestTower B T)
    (a y : Y) (s : ℕ) (H : Set Y) (hyH : y ∈ H)
    (U : Opens X)
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U (tangentChoice A (T.proj a)).2)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U (tangentChoice B (T.proj a)).2)
    (hyU : y ∈ openPreimage T U)
    (hyA : y ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N)
    (hyB : y ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal y)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
      (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal y)
    (hcoeff : min (divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y) (coeffEmptyBM A).d =
      min (divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y) (coeffEmptyBM A).d)
    (hzero : divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
        (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal H y = 0 ∨
      divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N
        (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal H y = 0) :
    divExpAlong n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal H y =
      divExpAlong n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal H y := by
  have hTA := isGeoTestTower_of_barMarked hA hdA T hT
  have hca := actual_contact_ambient A hA hdA U hf T hTA
  have hcb := actual_contact_ambient B hB hdB U hg T hTB
  obtain ⟨m, -, hm⟩ := hca.2.2.2 ⟨y,hyU⟩ hyA
  obtain ⟨m', -, hm'⟩ := hcb.2.2.2 ⟨y,hyU⟩ hyB
  have hmA := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hm
  have hmB := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hm'
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hmA
  obtain ⟨r', hr'⟩ := exists_isLocalRetraction hmB
  have hcA : (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal.IsCoherent := by
    have hw := isWellFormed_coeffEmptyBM hA
    have ht := isGeoTestTower_coeffEmptyBM hA hdA T (isGeoTestTower_emptyBoundary A T hTA)
    exact (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hw.isClosedSubmanifold_N hw.isCoherent T ht).2
  have hcB : (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).ideal.IsCoherent := by
    have hw := isWellFormed_coeffEmptyBM hB
    have ht := isGeoTestTower_coeffEmptyBM hB hdB T (isGeoTestTower_emptyBoundary B T hTB)
    exact (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hw.isClosedSubmanifold_N hw.isCoherent T ht).2
  have hSm := isClosedSubmanifold_of_mem_throughMembers A hA hn T hT a
  have hEc := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSm (coeffEmptyBM A).d
  have hpos : 1 ≤ (coeffEmptyBM A).d := HironakaG8ClassStepCut.one_le_coeffEmptyBM_d A
  have hEq : exceptionalTermBM (throughMembers B T a) (coeffEmptyBM B).d =
      exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d := by
    rw [throughMembers_eq_of_E_eq hE T a, coeffEmptyBM_d B, coeffEmptyBM_d A, hd]
  have hsum := HironakaG8ResidualZeroCoeff.sum_exponents_equal_of_coeff_zero
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcA)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcB)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hEc)
    hr hr' hyH hnzA hnzB hpos hcoeff hzero
  rw [lowerIdealBM_succ_ideal, lowerIdealBM_succ_ideal, hEq]
  change divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N _ H y =
    divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N _ H y
  simpa only [contactCoeffBM_ideal] using hsum

end
end Hironaka.HironakaG8ResidualActualZero
