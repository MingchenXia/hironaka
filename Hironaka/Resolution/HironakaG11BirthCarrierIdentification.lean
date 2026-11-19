import Hironaka.Resolution.HironakaG11BornMemberOrigin
import Hironaka.Invariant.MemberInterLocusAlong

set_option autoImplicit false

/-! Identify the actual lower carrier and old member at the selected birth. -/

open Set
namespace Hironaka.HironakaG11BirthCarrierIdentification
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11InvBMLower StepOneValue
  HironakaG11BornMemberOrigin MemberInterLocusAlong

universe u
variable {n : ℕ} {X : CMfd.{u} n}

/-- At the literal birth of a lower boundary member, the final lower carrier
and every retained original member are the strict transforms along the same
suffix of their respective strict transforms at that birth. -/
theorem lower_birth_with_carrier_and_old_member
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (s : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T) (y : Y)
    {H K : Set Y} (hH : H ∈ (lowerIdealBM J s T y).E) (hK : K ∈ throughMembers J T y) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y) (K₀ : Set X),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      K₀ ∈ J.E ∧
      K = strictAlong Q (geoStrictTransform π C (strictAlong P K₀)) ∧
      (lowerIdealBM J s T y).N = strictAlong Q
        (geoStrictTransform π C (strictAlong P (J.N ∩ {x | (tangentChoice J (T.proj y)).2 x = 0}))) ∧
      IsGeoTestTower (coeffEmptyBM J) P ∧
      (geoTransformAlong (coeffEmptyBM J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (coeffEmptyBM J) (.step P C π hπ)) Q := by
  obtain ⟨A, B, P, C, π, hπ, Q, hT', hH', hP, hC, hQ⟩ :=
    exists_lowerIdeal_test_birth J hJ hd s T hT y hH
  have hK' := (mem_throughMembers.mp hK).1
  rw [origMembers_eq] at hK'
  obtain ⟨K₀, hK₀, hK⟩ := List.mem_map.mp hK'
  refine ⟨A, B, P, C, π, hπ, Q, K₀, hT', hH', hK₀, ?_, ?_, hP, hC, hQ⟩
  · rw [← hK, hT', strictAlong_append]
    rfl
  · rw [lowerIdealBM_N, hT', strictAlong_append]
    rfl

end Hironaka.HironakaG11BirthCarrierIdentification
