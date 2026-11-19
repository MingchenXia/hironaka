import Hironaka.Resolution.HironakaG8ExceptionalSumCoeff
import Hironaka.Resolution.HironakaG8CaseTActualAmbient
import Hironaka.Resolution.HironakaG8ClassStepResidual

/-! # Actual successor residual from coefficient and trace comparisons -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualActualSum
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen
  HomogenizedGlueingTower HomogenizedIdealAlongTower TangentDirectionAlong GermIdealOrder DivisorExponentAlong
  StepOneValue HironakaG11InvBMMask HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMLowerTailSucc
  HironakaG8LocalHistory HironakaG8CaseTActualAmbient HironakaG8ClassStepResidual
  HironakaG8ExceptionalSumCoeff
open RestrictedIdealExtension (sumIdeal)

/-- At an actual successor stage, coefficient exponent agreement below the
mark and the common old-member trace condition give the residual exponent
equality, when both coefficients are nonzero. -/
theorem actual_successor_exp_eq_of_coeff_and_trace
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
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D))
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y) :
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
  have hS : ∀ D ∈ throughMembers A T a, IsClosed D := fun D hD => (hSm D hD).1
  have hEc := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSm (coeffEmptyBM A).d
  have hmin := sum_exp_below_eq_of_coeff_exp_and_trace hS hcA hcB hEc hr hr' hyH hnzA hnzB hcoeff htrace
  have hbelow' : ¬ IsDivNearAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (sumIdeal (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d)) H (coeffEmptyBM A).d y := by
    simpa only [lowerIdealBM_N, lowerIdealBM_succ_ideal, lowerIdealBM_d, contactCoeffBM_N, contactCoeffBM_ideal] using hbelow
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent
    (RestrictedIdealExtension.isCoherent_sumIdeal hcA hEc)
  have hlt : divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (sumIdeal (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal
        (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d)) H y < (coeffEmptyBM A).d := by
    by_contra hge
    exact hbelow' ((isDivNearAlong_divExpAlong hhol y).mono (by omega))
  have hEq : exceptionalTermBM (throughMembers B T a) (coeffEmptyBM B).d =
      exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d := by
    rw [throughMembers_eq_of_E_eq hE T a, coeffEmptyBM_d B, coeffEmptyBM_d A, hd]
  rw [lowerIdealBM_succ_ideal, lowerIdealBM_succ_ideal, hEq]
  change divExpAlong n (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N _ H y =
    divExpAlong n (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N _ H y
  simp only [contactCoeffBM_ideal] at hmin hlt
  omega

end
end Hironaka.HironakaG8ResidualActualSum
