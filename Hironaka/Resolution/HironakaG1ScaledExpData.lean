import Hironaka.Resolution.HironakaG8ScaledExponentHistory
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ScaledExpData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong MonomialCaseAlong HironakaG8LocalHistory HironakaG8ScaledExponentHistory
  HironakaG8MixedBoundaryExponents HironakaCoherentTransformExtension InvDomainTowerAlong
  MarkedIdealEquivalence.MarkedIdeal

/-- Initial normalized exponent agreement gives cross-scaled indexed
exponent data at every tested suffix cosupport point. -/
theorem scaled_expData_of_initial {n k l : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N = P.N) (hE : Q.E = P.E) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    ∀ i, (geoTransformAlong Q T).d * expDataAlong n (geoTransformAlong P T).N
      (geoTransformAlong P T).ideal (geoTransformAlong P T).E y i =
    (geoTransformAlong P T).d * expDataAlong n (geoTransformAlong Q T).N
      (geoTransformAlong Q T).ideal (geoTransformAlong Q T).E y i := by
  let PT := geoTransformAlong P T
  let QT := geoTransformAlong Q T
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hNT : QT.N = PT.N := geoTransformAlong_N_eq_of_N_eq hN T
  have hET : QT.E = PT.E := E_geoTransformAlong_eq hE T
  have hScaled := scaled_exponents_of_initial_agreement P Q hP hQ hN hE hL hInitial T hT
  intro i
  change QT.d * expDataAlong n PT.N PT.ideal PT.E y i = PT.d * expDataAlong n QT.N QT.ideal QT.E y i
  rw [hET]
  unfold expDataAlong
  split_ifs with hi
  · by_cases hyH : y ∈ PT.E.get ⟨i,hi⟩
    · simpa only [PT,QT,d_geoTransformAlong] using hScaled _ (List.get_mem _ _) y hy hyH
    · have hcl : IsClosed (PT.N ∩ PT.E.get ⟨i,hi⟩) :=
        hPT.isWellFormed.isClosedSubmanifold_N.1.inter (hPT.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _))
      rw [divExpAlong_eq_zero_of_notMem hcl (fun h => hyH h.2),hNT,
        divExpAlong_eq_zero_of_notMem hcl (fun h => hyH h.2)]
      simp only [Nat.mul_zero]
  · simp only [Nat.mul_zero]
end
end Hironaka.HironakaG1ScaledExpData
