import Hironaka.Resolution.HironakaG8ExceptionalSumCoeff
import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.Resolution.HironakaG8ExceptionalDivisibility
import Hironaka.Resolution.HironakaG11ActualPrefixedSum

set_option autoImplicit false

/-! Below-mark residual sums with a divisible exceptional term have a
nonzero coefficient summand along their carrier. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ResidualCoefficientNonzero
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealOrder GiraudAlong IdealWeightPowers BlowupTowers DivisorExponentAlong HironakaG8SumExponents
  MarkedIdealOperationsAlong.MarkedIdeal RestrictedIdealExtension
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower StepOneValue
  HironakaG11InvBMLower HironakaG11InvBMLowerTailSucc HironakaG8ExceptionalDivisibility

/-- If the second summand is divisible at the mark while the sum is not,
the coherent first summand is nonzero along the carrier at the point. -/
theorem coefficient_nonzero_of_sum_below
    {n : ℕ} {X : CMfd.{0} n} {N H : Set X} {C E : GermIdeal n X}
    (hC : C.IsCoherent) (hE : ∀ x g, E.mem x g → HolomorphicAt n g x)
    {d : ℕ} {y : X} (hdivE : IsDivNearAlong n N E H d y)
    (hbelow : ¬ IsDivNearAlong n N (sumIdeal C E) H d y) :
    IsNonzeroAlongAt N C y := by
  by_contra hnz
  have hzero := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hC hnz
  have hdivC : IsDivNearAlong n N C H d y := by
    filter_upwards [hzero] with z hz hzN hzH
    exact ⟨hzN,fun g hg => ⟨fun _ => 0,zero_mem_idealPow _ z d,hz g hg⟩⟩
  exact hbelow ((isDivNearAlong_sumIdeal_iff (hol_of_isCoherent hC) hE d y).mpr ⟨hdivC,hdivE⟩)


/-- At the actual successor residual, order-one exceptional divisibility and
below-mark divisibility failure force the literal contact coefficient ideal
to be nonzero along its carrier at the evaluated endpoint. -/
theorem actual_residual_coefficient_nonzero
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (hA : A.IsWellFormed) (hd : 1 ≤ A.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked A) T) (a z : Y) (s : ℕ) (H : Set Y)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z)
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d z) :
    IsNonzeroAlongAt (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N
      (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).ideal z := by
  have hS : ∀ K ∈ throughMembers A T a, IsClosed K := fun K hK =>
    (isClosedSubmanifold_of_mem_throughMembers A hA hn T hT a K hK).1
  have hpos : 1 ≤ (coeffEmptyBM A).d := HironakaG8ClassStepCut.one_le_coeffEmptyBM_d A
  have hdiv' := (exceptionalTerm_divisible_one_iff_mark hS hpos z).mp hdiv
  have hTA := HironakaG11InvBMStage.isGeoTestTower_of_barMarked hA hd T hT
  have hw := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA
  have ht := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA hd T
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T hTA)
  have hc := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hw.isClosedSubmanifold_N hw.isCoherent T ht).2
  have he := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM
    (isClosedSubmanifold_of_mem_throughMembers A hA hn T hT a) (coeffEmptyBM A).d
  rw [lowerIdealBM_d,lowerIdealBM_succ_ideal] at hbelow
  have hnz := coefficient_nonzero_of_sum_below hc (hol_of_isCoherent he) hdiv' hbelow
  exact hnz

end Hironaka.HironakaG11ResidualCoefficientNonzero
