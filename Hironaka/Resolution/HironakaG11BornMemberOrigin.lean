import Hironaka.Resolution.HironakaG11InvBMNaturality
import Hironaka.Blowup.BlowupTowerSplit

set_option autoImplicit false

/-! Every boundary member of an empty-boundary history has an actual birth. -/

open Set
namespace Hironaka.HironakaG11BornMemberOrigin
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11InvBMLower StepOneValue
  HironakaG11InvBMNaturality

universe u
variable {n : ℕ} {X : CMfd.{u} n}

/-- Every member appearing in a tower from an empty boundary is the strict
transform of the literal exceptional set of a specific blowup in that tower. -/
theorem exists_birth_of_empty_boundary (M : MarkedIdeal n X) (hE : M.E = []) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) {H : Set Y},
      H ∈ (geoTransformAlong M T).E →
      ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
        (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y),
        T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) := by
  intro Y T
  induction T with
  | refl =>
      intro H hH
      simp [hE] at hH
  | @step Y Z T C π hπ ih =>
      intro H hH
      change H ∈ (geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
      rcases List.mem_append.mp hH with hOld | hNew
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hOld
        obtain ⟨A, B, P, D, ρ, hρ, Q, hT, hBirth⟩ := ih hH₀
        refine ⟨A, B, P, D, ρ, hρ, .step Q C π hπ, ?_, ?_⟩
        · simp [hT]
        · change geoStrictTransform π C H₀ = geoStrictTransform π C (strictAlong Q (ρ ⁻¹' D))
          rw [hBirth]
      · have hH : H = π ⁻¹' C := by simpa using hNew
        refine ⟨Y, Z, T, C, π, hπ, .refl, rfl, ?_⟩
        simpa using hH

/-- In a test history, the selected birth has an admissible centre and the
remaining tower is a test history of the actual born-stage marked ideal. -/
theorem exists_test_birth_of_empty_boundary (M : MarkedIdeal n X) (hE : M.E = [])
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {H : Set Y} (hH : H ∈ (geoTransformAlong M T).E) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      IsGeoTestTower M P ∧ (geoTransformAlong M P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong M (.step P C π hπ)) Q := by
  obtain ⟨A, B, P, C, π, hπ, Q, hEq, hH⟩ := exists_birth_of_empty_boundary M hE T hH
  have hParts := (isGeoTestTower_append_iff M (.step P C π hπ) Q).mp (hEq ▸ hT)
  have hBirth := (isGeoTestTower_step_iff M P C π hπ).mp hParts.1
  exact ⟨A, B, P, C, π, hπ, Q, hEq, hH, hBirth.1, hBirth.2, hParts.2⟩

/-- Every literal lower ideal boundary member comes from a particular
coefficient-history birth, followed by its actual strict transform. -/
theorem exists_lowerIdeal_birth (J : MarkedIdeal n X) (s : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y)
    {H : Set Y} (hH : H ∈ (lowerIdealBM J s T y).E) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) := by
  apply exists_birth_of_empty_boundary (coeffEmptyBM J) (coeffEmptyBM_E J) T
  simpa only [lowerIdealBM_E] using hH

/-- An actual Step I.B coefficient history locates every lower boundary
member at a specific admissible birth with its test tail. -/
theorem exists_lowerIdeal_test_birth (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d) (s : ℕ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T) (y : Y)
    {H : Set Y} (hH : H ∈ (lowerIdealBM J s T y).E) :
    ∃ (A B : CMfd.{u} n) (P : BlowupTower X A) (C : Set A)
      (π : B → A) (hπ : IsBlowupAlong n C π) (Q : BlowupTower B Y),
      T = (BlowupTower.step P C π hπ).append Q ∧ H = strictAlong Q (π ⁻¹' C) ∧
      IsGeoTestTower (coeffEmptyBM J) P ∧
      (geoTransformAlong (coeffEmptyBM J) P).IsAdmissibleCentre C ∧
      IsGeoTestTower (geoTransformAlong (coeffEmptyBM J) (.step P C π hπ)) Q := by
  apply exists_test_birth_of_empty_boundary (coeffEmptyBM J) (coeffEmptyBM_E J) T
    (isGeoTestTower_coeffEmptyBM_of_barMarked J hJ hd T hT)
  simpa only [lowerIdealBM_E] using hH

end Hironaka.HironakaG11BornMemberOrigin
