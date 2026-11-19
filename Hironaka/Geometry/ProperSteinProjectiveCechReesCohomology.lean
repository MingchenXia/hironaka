import Hironaka.Geometry.ProperSteinProjectiveCechReesProjective
import Hironaka.Geometry.ProperSteinProjectiveCechReesChartSections
import Hironaka.Geometry.ProperSteinProjectiveCechClosedCohomology

/-! # Genuine finite Rees cohomology on the SAME ORIGINAL pulled-back coordinate cover -/
universe u
open CategoryTheory AlgebraicGeometry
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesCohomology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} {n : ℕ}
  (i : X ⟶ projectiveSpace R n) [hi : IsClosedImmersion i]

/-- The SAME original coordinate opens pulled back to the ACTUAL internally constructed schematic Rees family. -/
def coordinateOpens (j : ULift.{u} (Fin (n+1))) :
    (ReesFamily.family I (i ≫ projectiveSpaceStructure R n)).Opens :=
  ReesChartSections.projection I (i ≫ projectiveSpaceStructure R n) ⁻¹ᵁ originalClosedCoordinateOpens i j

/-- The actual constructed family embedding has EXACTLY the SAME original pulled-back coordinate opens. -/
theorem familyEmbedding_coordinateOpens (j : ULift.{u} (Fin (n+1))) :
    originalClosedCoordinateOpens (ReesProjective.familyEmbedding I i) j = coordinateOpens I i j := by
  rw [originalClosedCoordinateOpens_eq, coordinateOpens, originalClosedCoordinateOpens_eq]
  have h := ReesProjective.familyEmbedding_original I i
  change ReesProjective.familyEmbedding I i ≫
    ProjectiveSpaceBaseChange.nativeCoefficientMap (algebraMap R (reesAlgebra I)) =
      ReesChartSections.projection I (i ≫ projectiveSpaceStructure R n) ≫ i at h
  have h' := congrArg (fun g => g ⁻¹ᵁ
    Hironaka.Geometry.ProjectiveIdeal.nativeCoordinateOpen (R := R) j.down) h
  rw [Scheme.Hom.comp_preimage, ProjectiveSpaceBaseChange.nativeCoefficientMap_preimage_coordinateOpen,
    Scheme.Hom.comp_preimage] at h'
  exact h'

/-- The actual family cover is produced from the SAME ORIGINAL coordinate cover. -/
theorem coordinateOpens_covers : iSup (coordinateOpens I i) = ⊤ := by
  change (⨆ j, ReesChartSections.projection I (i ≫ projectiveSpaceStructure R n) ⁻¹ᵁ
    originalClosedCoordinateOpens i j) = ⊤
  rw [← Scheme.Hom.preimage_iSup, originalClosedCoordinateOpens_covers, Scheme.Hom.preimage_top]

/-- GENUINE original-source affine family projection gives affinity of EVERY same original family coordinate open. -/
theorem coordinateOpens_isAffine (j : ULift.{u} (Fin (n+1))) : IsAffineOpen (coordinateOpens I i j) :=
  (originalClosedCoordinateOpens_isAffine i j).preimage
    (ReesChartSections.projection I (i ≫ projectiveSpaceStructure R n))

include hi in
/-- The ACTUAL original projective geometry internally proves finite ENTIRE Rees Cech cohomology in EVERY degree; no hfinite premise. -/
theorem nativeCech_finite [IsNoetherianRing R] (p : ℕ) :
    Module.Finite (reesAlgebra I)
      ((subsetCechComplex
        (actualSchemeModuleBaseSubsetDiagram
          (SheafOfModules.unit (ReesFamily.family I (i ≫ projectiveSpaceStructure R n)).ringCatSheaf)
          (coordinateOpens I i)
          (ProperGeometricGlobalFunctions.coefficientMap
            (ReesFamily.familyProjection I (i ≫ projectiveSpaceStructure R n))))).homology p) := by
  have h := originalClosedCoordinateCech_finite_original (ReesProjective.familyEmbedding I i) p
  have hU : originalClosedCoordinateOpens (ReesProjective.familyEmbedding I i) = coordinateOpens I i :=
    funext (familyEmbedding_coordinateOpens I i)
  rw [hU, ReesProjective.familyEmbedding_projection] at h
  exact h

end
end Hironaka.Geometry.ProperSteinProjectiveCech.ReesCohomology
