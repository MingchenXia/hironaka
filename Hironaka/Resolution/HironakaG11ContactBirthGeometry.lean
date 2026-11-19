import Hironaka.Resolution.HironakaG8ContactStageAmbient
import Hironaka.Resolution.HironakaG11InvBMLowerTail

set_option autoImplicit false

/-!
# Local maximal-contact geometry at an actual coefficient-test birth

The admissible centre of the coefficient test lies in the actual strict
contact over its source open. The previous ambient carrier and its transverse
boundary are the ones produced by the original marked ideal's test history.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaG11ContactBirthGeometry

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal CoefficientIdealAlongRestrictionTower
  CoefficientIdealRestriction GiraudAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower TangentDirectionAlong MaximalContactAlongTower
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMLowerTail HironakaG8ContactStageAmbient

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- At a coefficient-test birth over the original contact open, the actual
centre lies in the literal strict-contact carrier on that open. At any of its
points, that carrier is a regular hypersurface of the actual previous carrier,
whose complete boundary is well formed and transverse. -/
theorem contact_birth_geometry
    (A : MarkedIdeal n X) (hA : A.IsWellFormed) (hd : 1 ≤ A.d)
    (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) (hTC : IsGeoTestTower (coeffEmptyBM A) T)
    {C : Set Y} (hC : (geoTransformAlong (coeffEmptyBM A) T).IsAdmissibleCentre C)
    (p : openPreimage T U) (hpC : p.val ∈ C) :
    let V := openPreimage T U
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A u T)
    let R := MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A T)
    R.IsWellFormed ∧ L.N ⊆ R.N ∧ IsClosedSubmanifold n L.N ∧
      (Subtype.val : V → Y) ⁻¹' C ⊆ L.N ∧
      ∃ m, RegularAtDim (n := n) R.N p (m + 1) ∧ RegularAtDim (n := n) L.N p m := by
  have hTe : IsGeoTestTower (emptyBoundary A) T :=
    (coeffAlong_tower (emptyBoundary A) hA.isClosedSubmanifold_N hA.isCoherent hd T).1.mp hTC
  have hsub : C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T (A.N ∩ {x | u x = 0}) := by
    intro z hz
    have hzco : z ∈ (geoTransformAlong (emptyBoundary A) T).cosupp := by
      rw [cosupp_geoTransformAlong_emptyBoundary, ← cosupp_geoTransformAlong_coeffEmptyBM hA hd T hTe]
      exact hC.2.1 hz.1
    have hzcontact := cosupp_subset_strictAlong_along (emptyBoundary A)
      hA.isClosedSubmanifold_N hA.isCoherent hd hu T hTe ⟨hzco, hz.2⟩
    exact MemberInterTowerAlong.strictAlong_mono T (fun x hx => hx.1) hzcontact
  have hp : p.val ∈ (contactCoeffBM A u T).N := hsub ⟨hpC, p.property⟩
  obtain ⟨hR, hLR, hL, m, hmR, hmL⟩ := contact_stage_ambient_hypersurface A hA hd U hu T hT p hp
  refine ⟨hR, hLR, hL, ?_, m, hmR, hmL⟩
  intro z hz
  exact hsub ⟨hz, z.property⟩

end
end Hironaka.HironakaG11ContactBirthGeometry
