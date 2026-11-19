import Hironaka.Resolution.HironakaG11ResidualBirthPoint

set_option autoImplicit false

/-! The actual residual endpoint retains both the full and coefficient test
structures at the same selected birth, with a separate defining anchor. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG11ResidualBirthFullTrace
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11InvBMLower StepOneValue
  DivisorExponentAlong HironakaG8SuccExponents HironakaG11BirthFullTest
  HironakaG11ResidualBirthPoint MemberInterLocusAlong

/-- The residual's evaluated point may differ from the anchor; an actual
exceptional-divisibility alternative puts it in every retained member and
selects one shared birth with both full and coefficient tests. -/
theorem lower_residual_birth_with_full_tests
    {n : ℕ} {X : CMfd.{0} n}
    (J L : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (s t : ℕ)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (a z : Y) {H K : Set Y} (hH : H ∈ (lowerIdealBM J s T a).E)
    (hK : K ∈ throughMembers J T a) (hS : ∀ H ∈ throughMembers J T a, IsClosed H)
    (hzJ : z ∈ (lowerIdealBM J s T a).N) (hzL : z ∈ (lowerIdealBM L t T a).N) (hzH : z ∈ H)
    (hdiv : IsDivNearAlong n (lowerIdealBM J s T a).N
      (exceptionalTermBM (n := n) (throughMembers J T a) (coeffEmptyBM J).d) H 1 z ∨
      IsDivNearAlong n (lowerIdealBM L t T a).N
      (exceptionalTermBM (n := n) (throughMembers J T a) (coeffEmptyBM J).d) H 1 z) :
    ∃ (A B : CMfd.{0} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y) (K₀ : Set X),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      K₀ ∈ J.E ∧ K = strictAlong Q (geoStrictTransform π C (strictAlong P K₀)) ∧
      IsGeoTestTower (coeffEmptyBM J) P ∧
      (geoTransformAlong (coeffEmptyBM J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (coeffEmptyBM J) (.step P C π hπ)) Q ∧
      IsGeoTestTower (barMarked J) P ∧
      (geoTransformAlong (barMarked J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (barMarked J) (.step P C π hπ)) Q ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (J.N ∩ {x | (tangentChoice J (T.proj a)).2 x = 0})) ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (L.N ∩ {x | (tangentChoice L (T.proj a)).2 x = 0})) ∧
      π (Q.proj z) ∈ C ∧ Q.proj z ∈ geoStrictTransform π C (strictAlong P K₀) := by
  have hzK : z ∈ K := by
    rcases hdiv with hdiv | hdiv
    · exact residual_endpoint_mem_throughMember hS hzJ hzH hdiv K hK
    · exact residual_endpoint_mem_throughMember hS hzL hzH hdiv K hK
  obtain ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hN, hPc, hCc, hQc, hP, hC, hQ⟩ :=
    lower_birth_full_test_with_carrier_and_old_member J hJ hd s T hT a hH hK
  refine ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hPc, hCc, hQc, hP, hC, hQ, ?_, ?_, ?_, ?_⟩
  · apply MemberInterTowerAlong.strictAlong_subset_preimage Q isClosed_closure
    exact hN ▸ hzJ
  · have hL : (lowerIdealBM L t T a).N = strictAlong Q
        (geoStrictTransform π C (strictAlong P (L.N ∩ {x | (tangentChoice L (T.proj a)).2 x = 0}))) := by
      rw [lowerIdealBM_N, hEq, strictAlong_append]
      rfl
    apply MemberInterTowerAlong.strictAlong_subset_preimage Q isClosed_closure
    exact hL ▸ hzL
  · apply MemberInterTowerAlong.strictAlong_subset_preimage Q (hC.1.1.preimage hπ.contMDiff.continuous)
    rwa [← hH']
  · apply MemberInterTowerAlong.strictAlong_subset_preimage Q isClosed_closure
    exact hK' ▸ hzK

end Hironaka.HironakaG11ResidualBirthFullTrace
