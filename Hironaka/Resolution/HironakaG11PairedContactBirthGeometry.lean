import Hironaka.Resolution.HironakaG11ContactBirthGeometry
import Hironaka.Invariant.StepOneBridge
import Hironaka.Resolution.HironakaG8LocalHistory

set_option autoImplicit false

/-!
# Paired maximal-contact geometry at an actual test birth

A common test of the original locally equivalent pair supplies the two
coefficient tests and their centre admissibility. Thus the actual birth
centre is contained in both literal contact carriers on a common source open.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG11PairedContactBirthGeometry
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  HomogenizedGlueingTower TangentDirectionAlong HironakaG11InvBMLower HironakaG11InvBMStage
  ResolutionInvariantSpec HironakaG8LocalHistory HironakaG11ContactBirthGeometry
  StepOneValue

noncomputable section

/-- The actual common test birth yields both ambient/contact hypersurface
configurations on one source open, including centre containment in each
literal restricted contact carrier. -/
theorem paired_contact_birth_geometry
    {n : ℕ} {X : CMfd.{u} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (h : LocWPEquiv A B)
    (U : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    (hv : IsTangentDirectionAlong B.N B.ideal B.d U v)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hStep : IsGeoTestTower (barMarked A) (.step T C π hπ))
    (p : openPreimage T U) (hpC : p.val ∈ C) :
    let V := openPreimage T U
    let LA := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u T)
    let LB := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B v T)
    let RA := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    let RB := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong B T)
    RA.IsWellFormed ∧ LA.N ⊆ RA.N ∧ IsClosedSubmanifold n LA.N ∧
      (Subtype.val : V → Y) ⁻¹' C ⊆ LA.N ∧
      (∃ m, RegularAtDim (n := n) RA.N p (m + 1) ∧ RegularAtDim (n := n) LA.N p m) ∧
    RB.IsWellFormed ∧ LB.N ⊆ RB.N ∧ IsClosedSubmanifold n LB.N ∧
      (Subtype.val : V → Y) ⁻¹' C ⊆ LB.N ∧
      ∃ m, RegularAtDim (n := n) RB.N p (m + 1) ∧ RegularAtDim (n := n) LB.N p m := by
  have hSA : IsGeoTestTower A (.step T C π hπ) :=
    isGeoTestTower_of_barMarked hA.isWellFormed hA.one_le_d _ hStep
  have hSB : IsGeoTestTower B (.step T C π hπ) := (h.wEquiv.2 _).1.mp hSA
  have hSCA : IsGeoTestTower (coeffEmptyBM A) (.step T C π hπ) :=
    isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d _
      (isGeoTestTower_emptyBoundary A _ hSA)
  have hSCB : IsGeoTestTower (coeffEmptyBM B) (.step T C π hπ) :=
    isGeoTestTower_coeffEmptyBM hB.isWellFormed hB.one_le_d _
      (isGeoTestTower_emptyBoundary B _ hSB)
  obtain ⟨hTA, -⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hSA
  obtain ⟨hTB, -⟩ := (isGeoTestTower_step_iff B T C π hπ).mp hSB
  obtain ⟨hTCA, hCA⟩ := (isGeoTestTower_step_iff (coeffEmptyBM A) T C π hπ).mp hSCA
  obtain ⟨hTCB, hCB⟩ := (isGeoTestTower_step_iff (coeffEmptyBM B) T C π hπ).mp hSCB
  obtain ⟨hRA, hLARA, hLA, hCLA, hdimA⟩ :=
    contact_birth_geometry A hA.isWellFormed hA.one_le_d U hu T hTA hTCA hCA p hpC
  obtain ⟨hRB, hLBRB, hLB, hCLB, hdimB⟩ :=
    contact_birth_geometry B hB.isWellFormed hB.one_le_d U hv T hTB hTCB hCB p hpC
  exact ⟨hRA, hLARA, hLA, hCLA, hdimA, hRB, hLBRB, hLB, hCLB, hdimB⟩

end
end Hironaka.HironakaG11PairedContactBirthGeometry
