import Hironaka.Resolution.HironakaG11BirthCarrierIdentification

set_option autoImplicit false

/-! The selected birth and suffix are also tests for the actual full boundary. -/

open Set
namespace Hironaka.HironakaG11BirthFullTest
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11InvBMLower StepOneValue
  HironakaG11BirthCarrierIdentification

universe u
variable {n : ℕ} {X : CMfd.{u} n}

/-- The same identified lower-boundary birth carries both the coefficient
and full original marked-ideal test structures. -/
theorem lower_birth_full_test_with_carrier_and_old_member
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (s : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T) (y : Y)
    {H K : Set Y} (hH : H ∈ (lowerIdealBM J s T y).E) (hK : K ∈ throughMembers J T y) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y) (K₀ : Set X),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      K₀ ∈ J.E ∧ K = strictAlong Q (geoStrictTransform π C (strictAlong P K₀)) ∧
      (lowerIdealBM J s T y).N = strictAlong Q
        (geoStrictTransform π C (strictAlong P (J.N ∩ {x | (tangentChoice J (T.proj y)).2 x = 0}))) ∧
      IsGeoTestTower (coeffEmptyBM J) P ∧
      (geoTransformAlong (coeffEmptyBM J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (coeffEmptyBM J) (.step P C π hπ)) Q ∧
      IsGeoTestTower (barMarked J) P ∧
      (geoTransformAlong (barMarked J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (barMarked J) (.step P C π hπ)) Q := by
  obtain ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hN, hPc, hCc, hQc⟩ :=
    lower_birth_with_carrier_and_old_member J hJ hd s T hT y hH hK
  have hFull := (isGeoTestTower_append_iff (barMarked J) (.step P C π hπ) Q).mp (hEq ▸ hT)
  have hBirth := (isGeoTestTower_step_iff (barMarked J) P C π hπ).mp hFull.1
  exact ⟨A, B, P, C, π, hπ, Q, K₀, hEq, hH', hK₀, hK', hN, hPc, hCc, hQc,
    hBirth.1, hBirth.2, hFull.2⟩

end Hironaka.HironakaG11BirthFullTest
