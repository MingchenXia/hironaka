/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Algebra.ReesPresentation
import DeJongAlterations.Geometry.ProjClosedImmersion
import DeJongAlterations.Geometry.ProjStructureMap

/-!
# Projectivity of the native affine blowup

A finitely generated ideal has a surjective graded polynomial presentation of its actual
Rees algebra. The resulting native Proj closed immersion factors the actual blowup structure
morphism through projective space over the original coefficient ring.
-/

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace DeJongAlterations

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero restriction of a graded coefficient-algebra map commutes with the actual
coefficient-ring identifications of projective space and the Rees algebra. -/
theorem reesPolynomial_degreeZero_constants {n : ℕ}
    (φ : GradedAlgHom R (projectiveSpaceGrading R n) (reesGrading I)) :
    φ.toGradedRingHom.gradedZeroRingHom.comp (projectiveSpaceDegreeZeroEquiv R n).toRingHom =
      (reesDegreeZeroEquiv I).toRingHom := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change φ (MvPolynomial.C r) = algebraMap R (reesAlgebra I) r
  exact φ.commutes r

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The native Proj morphism of a graded coefficient-algebra presentation is over the
original affine coefficient scheme, using the genuine degree-zero identifications. -/
theorem reesPolynomialMap_projStructure {n : ℕ}
    (φ : GradedAlgHom R (projectiveSpaceGrading R n) (reesGrading I))
    (hf : HomogeneousIdeal.irrelevant (reesGrading I) ≤
      (HomogeneousIdeal.irrelevant (projectiveSpaceGrading R n)).map φ.toGradedRingHom) :
    Proj.map φ.toGradedRingHom hf ≫ projectiveSpaceStructure R n = affineBlowupStructure I := by
  exact Geometry.ProjStructureMap.map_toSpec_base φ.toGradedRingHom hf
    (projectiveSpaceDegreeZeroEquiv R n).toRingHom (reesDegreeZeroEquiv I).toRingHom
    (reesPolynomial_degreeZero_constants I φ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine blowup of any finitely generated ideal is projective over its original
affine base. The graded polynomial presentation, closed immersion and structure equality
are all constructed internally from finite generation. -/
theorem affineBlowupStructure_isProjective (hI : I.FG) :
    IsProjectiveOver (affineBlowupStructure I) := by
  obtain ⟨n, φ, hφ⟩ := Algebra.ReesPresentation.exists_surjective_gradedPolynomialMap I hI
  let hf := Geometry.ProjClosedImmersion.irrelevant_le_map_of_surjective φ.toGradedRingHom hφ
  refine ⟨n, Proj.map φ.toGradedRingHom hf, ?_, ?_⟩
  · exact Geometry.ProjClosedImmersion.isClosedImmersion_map φ.toGradedRingHom hφ hf
  · exact reesPolynomialMap_projStructure I φ hf

end

end DeJongAlterations
