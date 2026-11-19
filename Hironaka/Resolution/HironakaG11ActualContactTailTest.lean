import Hironaka.Resolution.HironakaG11ResidualActualContact
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc

set_option autoImplicit false

/-! An actual original test tail restricts to a test of the literal contact
coefficient ideal at the preceding stage. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualContactTailTest
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism MarkedIdealOpenBiholomorphism
  StepOneValue
  TangentDirectionAlong HironakaG11InvBMLower HironakaG11InvBMStage
  HironakaG11InvBMLowerDomainSucc ResolutionInvariantSpec

noncomputable section

/-- The literal restriction of the actual suffix is a test of the stage
contact coefficient record. That record is well formed on the tangent open. -/
theorem actual_contact_tail_test
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q)) :
    let V := openPreimage P U
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u P)
    L.IsWellFormed ∧ IsGeoTestTower L (restrict V Q) := by
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hTA : IsGeoTestTower A (P.append Q) := (hWA.2 _).1.mp hT
  have hPA : IsGeoTestTower A P := (isGeoTestTower_append_iff A P Q).mp hTA |>.1
  have hTP : IsGeoTestTower (barMarked A) P := (isGeoTestTower_append_iff (barMarked A) P Q).mp hT |>.1
  have hTE : IsGeoTestTower (emptyBoundary A) (P.append Q) := isGeoTestTower_emptyBoundary A _ hTA
  have ⟨hPE,hQE⟩ := (isGeoTestTower_append_iff (emptyBoundary A) P Q).mp hTE
  obtain ⟨hN,hI⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪 := emptyBoundary A)
    hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent P hPE
  let V := openPreimage P U
  have hR := isGeoTestTower_restrict V hN hI Q hQE
  have hW := wEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d U hu P hPA
  have hL := (hW.2 (restrict V Q)).1.mp hR
  have hwf := (isWellFormed_dimLE_contactCoeffBM_of_le hA.isWellFormed hA.one_le_d U hu
    P hA.dimLE hTP V (fun _ h => h)).1
  exact ⟨hwf,hL⟩


/-- The actual test suffix remains a test after a further local restriction
inside the tangent stage open, as needed for local birth neighbourhoods. -/
theorem actual_contact_tail_test_restrict
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q))
    (W : Opens (openPreimage P U)) :
    let V := openPreimage P U
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u P)
    let LW := MarkedIdeal.pullback (Subtype.val : W → V) L
    LW.IsWellFormed ∧ IsGeoTestTower LW (restrict W (restrict V Q)) := by
  let V := openPreimage P U
  let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u P)
  obtain ⟨hL,hQ⟩ := actual_contact_tail_test A hA U hu P Q hT
  exact ⟨IsWellFormed.pullback_val hL W, isGeoTestTower_restrict W hL.isClosedSubmanifold_N hL.isCoherent _ hQ⟩


/-- The new exceptional fibre is literally in the stage contact divisor. -/
theorem birth_mem_contact_boundary
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) (u : X → ℂ)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    π ⁻¹' C ∈ (contactCoeffBM A u (.step P C π hπ)).E := by
  rw [contactCoeffBM_E]
  change π ⁻¹' C ∈ (geoTransformAlong (coeffEmptyBM A) P).E.map
    (geoStrictTransform π C) ++ [π ⁻¹' C]
  simp


/-- Its literal trace is a member of every open restriction of that record. -/
theorem birth_mem_restricted_contact_boundary
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) (u : X → ℂ)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (V : Opens Z) :
    (Subtype.val : V → Z) ⁻¹' (π ⁻¹' C) ∈
      (MarkedIdeal.pullback (Subtype.val : V → Z) (contactCoeffBM A u (.step P C π hπ))).E := by
  change (Subtype.val : V → Z) ⁻¹' (π ⁻¹' C) ∈
    (contactCoeffBM A u (.step P C π hπ)).E.map (fun H => (Subtype.val : V → Z) ⁻¹' H)
  exact List.mem_map.mpr ⟨π ⁻¹' C,birth_mem_contact_boundary A u P C π hπ,rfl⟩

end
end Hironaka.HironakaG11ActualContactTailTest
