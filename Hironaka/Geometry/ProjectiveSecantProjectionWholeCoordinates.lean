import Hironaka.Geometry.ProjectiveProjectionCenterFinite

/-!
# Exact entire original polynomial basic-open and point-ideal readback of the SAME actual finite projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter
open Algebra.ProjectiveProjectionFinite Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- EVERY original whole polynomial basic-open pullback retains the SAME actual original closed source and exact remaining-variable substitution. -/
theorem closedProjection_preimage_basicOpen
    (hout : centrePoint k n ∉ Set.range i) (F : MvPolynomial (Fin (n + 1)) k) :
    closedProjection k n i hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) F =
      i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.rename Fin.succ F) := by
  conv_rhs => rw [← representativeIso_hom_inclusion k n i]
  simp only [closedProjection, Scheme.Hom.comp_preimage, projection_preimage_basicOpen,
    originalInclusion, GradedQuotient.quotientSchemeMap, Proj.map_preimage_basicOpen,
    partialGradedMap, GradedRingHom.comp_apply, GradedQuotient.gradedMk_apply]
  rfl

/-- EVERY original whole basic-open pullback of the SAME actual finite arbitrary-centre projection is the SAME original full normalization after remaining-variable inclusion. -/
theorem projectionFromVector_preimage_basicOpen
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (hout : vectorPoint k n v hv ∉ Set.range i)
    (F : MvPolynomial (Fin (n + 1)) k) :
    projectionFromVector k n i v hv hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) F =
      i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1))
        (coordinatePolynomialEquiv k n v hv (MvPolynomial.rename Fin.succ F)) := by
  rw [projectionFromVector, closedProjection_preimage_basicOpen,
    transformedInclusion, Scheme.Hom.comp_preimage, coordinateAutomorphism_preimage_basicOpen]

/-- At EVERY same actual original source point, the entire original projected point ideal is exactly the full original normalized-coordinate ideal contraction. -/
theorem projectionFromVector_pointIdeal_mem
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (hout : vectorPoint k n v hv ∉ Set.range i)
    (x : X) (F : MvPolynomial (Fin (n + 1)) k) :
    F ∈ (projectionFromVector k n i v hv hout x).asHomogeneousIdeal ↔
      coordinatePolynomialEquiv k n v hv (MvPolynomial.rename Fin.succ F) ∈ (i x).asHomogeneousIdeal := by
  have h := congrArg (fun U : X.Opens => x ∈ U)
    (projectionFromVector_preimage_basicOpen k n i v hv hout F)
  replace h := Iff.of_eq h
  change (F ∉ (projectionFromVector k n i v hv hout x).asHomogeneousIdeal) ↔
    (coordinatePolynomialEquiv k n v hv (MvPolynomial.rename Fin.succ F) ∉ (i x).asHomogeneousIdeal) at h
  simpa only [not_not] using not_congr h

end Hironaka.Geometry.ProjectiveSecant
