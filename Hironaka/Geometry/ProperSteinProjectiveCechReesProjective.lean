/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesRestriction
import Hironaka.Geometry.ProjectiveSpaceBaseChange
import Hironaka.Geometry.ProperSteinProjectiveCechClosedSource

/-!
# Actual projective embedding of the SAME original schematic Rees family

Closed native embedding pattern adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsProjectiveFamily.lean`,
SHA256 85c178a03bcd319e2d66abccd5e88771241de3ba34e8bf479ed402968ee90eec.
Only accepted own projective coefficient/closed-source producers and the actual
original Rees-family cone are used; no constructed-family projectivity is assumed.
-/
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} {d : ℕ} (i : X ⟶ projectiveSpace R d)

/-- The actual original projective embedding after genuine Rees coefficient
base change and the actual polynomial-projective scalar isomorphism. -/
def ambientEmbedding :
    ReesFamily.ambient I (i ≫ projectiveSpaceStructure R d) ⟶
      projectiveSpace (reesAlgebra I) d :=
  ReesRestriction.ambientMap I (projectiveSpaceStructure R d) i ≫
    (ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap
      (algebraMap R (reesAlgebra I)) d).isoPullback.inv

/-- The constructed ambient map is a genuine closed immersion whenever
the same original projective embedding is a closed immersion. -/
instance ambientEmbedding_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (ambientEmbedding I i) := by
  have : IsClosedImmersion
      (ReesRestriction.ambientMap I (projectiveSpaceStructure R d) i) :=
    MorphismProperty.of_isPullback
      (ReesRestriction.ambientMap_isPullback I
        (projectiveSpaceStructure R d) i) inferInstance
  unfold ambientEmbedding
  infer_instance

/-- The entire coefficient projection is the SAME original Rees-base projection. -/
theorem ambientEmbedding_projection :
    ambientEmbedding I i ≫ projectiveSpaceStructure (reesAlgebra I) d =
      ReesFamily.ambientProjection I
        (i ≫ projectiveSpaceStructure R d) := by
  let hP := ProjectiveSpaceBaseChange.isPullback_projectiveCoefficientMap
    (algebraMap R (reesAlgebra I)) d
  let E := hP.isoPullback
  have hE : E.inv ≫ projectiveSpaceStructure (reesAlgebra I) d =
      pullback.snd (projectiveSpaceStructure R d)
        (ReesFamily.reesBase I) := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact hP.isoPullback_hom_snd.symm
  change (ReesRestriction.ambientMap I
      (projectiveSpaceStructure R d) i ≫ E.inv) ≫ _ = _
  rw [Category.assoc, hE]
  exact ReesRestriction.ambientMap_projection I
    (projectiveSpaceStructure R d) i

/-- The SAME original closed schematic Rees family has its actual internally derived projective embedding. -/
def familyEmbedding : ReesFamily.family I (i ≫ projectiveSpaceStructure R d) ⟶
    projectiveSpace (reesAlgebra I) d :=
  ReesFamily.familyImmersion I (i ≫ projectiveSpaceStructure R d) ≫ ambientEmbedding I i

/-- Actual original closed immersion base change and SAME closed image derive the family embedding's closedness. -/
instance familyEmbedding_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (familyEmbedding I i) := by
  unfold familyEmbedding
  infer_instance

/-- The ENTIRE original Rees coefficient projection is retained by the SAME family embedding. -/
@[reassoc] theorem familyEmbedding_projection :
    familyEmbedding I i ≫ projectiveSpaceStructure (reesAlgebra I) d =
      ReesFamily.familyProjection I (i ≫ projectiveSpaceStructure R d) := by
  rw [familyEmbedding, Category.assoc, ambientEmbedding_projection]
  rfl

/-- The SAME actual original source embedding triangle is retained over EVERY original scheme point and section. -/
@[reassoc] theorem familyEmbedding_original :
    familyEmbedding I i ≫ BlowupProjectiveEmbedding.projectiveCoefficientMap
        (algebraMap R (reesAlgebra I)) d =
      (ReesFamily.familyImmersion I (i ≫ projectiveSpaceStructure R d) ≫
        pullback.fst (i ≫ projectiveSpaceStructure R d) (ReesFamily.reesBase I)) ≫ i := by
  let E := ProjectiveSpaceBaseChange.projectiveSpaceBaseChangeIso
    (algebraMap R (reesAlgebra I)) d
  have hE : E.inv ≫ BlowupProjectiveEmbedding.projectiveCoefficientMap
      (algebraMap R (reesAlgebra I)) d =
      pullback.fst (projectiveSpaceStructure R d) (ReesFamily.reesBase I) := by
    apply (cancel_epi E.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (ProjectiveSpaceBaseChange.projectiveSpaceBaseChangeIso_hom_fst
      (algebraMap R (reesAlgebra I)) d).symm
  change (ReesFamily.familyImmersion I (i ≫ projectiveSpaceStructure R d) ≫
    (ReesRestriction.ambientMap I (projectiveSpaceStructure R d) i ≫ E.inv)) ≫ _ = _
  rw [Category.assoc, Category.assoc, hE, ReesRestriction.ambientMap_fst]
  simp only [Category.assoc]

/-- Genuine internally constructed projectivity gives finite ENTIRE original family functions with its canonical Rees coefficients. -/
theorem familyGlobalSections_finite [IsNoetherianRing R] [IsClosedImmersion i] :
    letI := ProperGeometricGlobalFunctions.sectionsAlgebra
      (ReesFamily.familyProjection I (i ≫ projectiveSpaceStructure R d))
    Module.Finite (reesAlgebra I) Γ(ReesFamily.family I (i ≫ projectiveSpaceStructure R d), ⊤) := by
  change @Module.Finite (reesAlgebra I) Γ(ReesFamily.family I (i ≫ projectiveSpaceStructure R d), ⊤) _ _
    (ProperGeometricGlobalFunctions.coefficientMap
      (ReesFamily.familyProjection I (i ≫ projectiveSpaceStructure R d))).toAlgebra.toModule
  rw [← familyEmbedding_projection I i]
  exact originalClosedGlobalSections_finite_original (familyEmbedding I i)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesProjective
