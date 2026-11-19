import Hironaka.Resolution.HironakaG11BirthFullTest
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Resolution.HironakaG8SuccExponents

set_option autoImplicit false

/-!
# A lower residual endpoint and its actual boundary birth

The anchor defining the lower ideals and the point at which the residual is
being tested are independent. Membership in a retained old member at the
endpoint follows from exceptional-term near divisibility, not from the
anchor's membership in that member.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG11ResidualBirthPoint

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11InvBMLower StepOneValue
  DivisorExponentAlong HironakaG8SuccExponents HironakaG11BirthFullTest MemberInterLocusAlong

/-- Given a retained old member containing the evaluated endpoint, identify
one actual boundary birth and project that endpoint to all corresponding
birth-stage sets. The anchor may differ from the endpoint. -/
theorem lower_residual_endpoint_has_birth_trace
    {n : ℕ} {X : CMfd.{u} n}
    (J L : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (s t : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    (a z : Y) {H K : Set Y} (hH : H ∈ (lowerIdealBM J s T a).E)
    (hK : K ∈ throughMembers J T a) (hzK : z ∈ K)
    (hzJ : z ∈ (lowerIdealBM J s T a).N) (hzL : z ∈ (lowerIdealBM L t T a).N) (hzH : z ∈ H) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y) (K₀ : Set X),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      K₀ ∈ J.E ∧ K = strictAlong Q (geoStrictTransform π C (strictAlong P K₀)) ∧
      IsGeoTestTower (barMarked J) P ∧
      (geoTransformAlong (barMarked J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (barMarked J) (.step P C π hπ)) Q ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (J.N ∩ {x | (tangentChoice J (T.proj a)).2 x = 0})) ∧
      Q.proj z ∈ geoStrictTransform π C (strictAlong P (L.N ∩ {x | (tangentChoice L (T.proj a)).2 x = 0})) ∧
      π (Q.proj z) ∈ C ∧ Q.proj z ∈ geoStrictTransform π C (strictAlong P K₀) := by
  obtain ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hN, _, _, _, hP, hC, hQ⟩ :=
    lower_birth_full_test_with_carrier_and_old_member J hJ hd s T hT a hH hK
  refine ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hP, hC, hQ, ?_, ?_, ?_, ?_⟩
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

/-- The exceptional-term divisibility alternative in the residual puts the
actual evaluated endpoint in every retained original member. -/
theorem residual_endpoint_mem_throughMember
    {n : ℕ} {Y : CMfd.{0} n} {N D : Set Y} {S : List (Set Y)}
    (hS : ∀ K ∈ S, IsClosed K) {e : ℕ} {z : Y}
    (hzN : z ∈ N) (hzD : z ∈ D)
    (hdiv : IsDivNearAlong n N (exceptionalTermBM (n := n) S e) D 1 z) :
    ∀ K ∈ S, z ∈ K := by
  exact mem_of_mem_cosupport_one_exceptionalTermBM hS (hdiv.self_of_nhds hzN hzD)

end Hironaka.HironakaG11ResidualBirthPoint
