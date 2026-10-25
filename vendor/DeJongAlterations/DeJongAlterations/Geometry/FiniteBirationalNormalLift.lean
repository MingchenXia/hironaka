import DeJongAlterations.Geometry.FiniteBirationalNormalLiftAffine

/-!
# Genuine normalization lifts and pullback sections

The actual common-field closure charts and their actual transition maps
construct a scheme morphism to the finite component.  The native pullback
then gives an actual section, with its projection identities.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]
  (L : Type u) [Field L] [Algebra S.functionField L]
  (e : letI := functionFieldAlgebra f; T.functionField →ₐ[S.functionField] L)

/-- A finite component embeds into the actual common-field normalization
contravariantly, by gluing the genuine integral-closure coordinate maps. -/
def normalizationLift : NormalizationInExtension.normalization S L ⟶ T :=
  (NormalizationInExtension.normalizationCover S L).glueMorphismsOfLocallyDirected
    (affineLift f L e) (fun h => affineLift_naturality f L e h)

/-- The global lift restricts to its originally constructed affine morphisms. -/
@[reassoc]
theorem normalizationLift_restrict (U : NormalizationInExtension.NonemptyAffineOpen S) :
    NormalizationInExtension.chartInclusion S L U ≫ normalizationLift f L e =
      affineLift f L e U :=
  (NormalizationInExtension.normalizationCover S L).map_glueMorphismsOfLocallyDirected
    (affineLift f L e) (fun h => affineLift_naturality f L e h) U

/-- The genuine global lift retains the original normalization structure map. -/
@[reassoc]
theorem normalizationLift_structure :
    normalizationLift f L e ≫ f = NormalizationInExtension.normalizationStructure S L := by
  apply (NormalizationInExtension.normalizationCover S L).hom_ext
  intro U
  change NormalizationInExtension.chartInclusion S L U ≫ _ =
    NormalizationInExtension.chartInclusion S L U ≫ _
  rw [← Category.assoc, normalizationLift_restrict, affineLift_structure,
    NormalizationInExtension.chartInclusion_structure]

/-- The actual section of the actual base change produced by the field embedding. -/
def normalizationSection : NormalizationInExtension.normalization S L ⟶
    pullback f (NormalizationInExtension.normalizationStructure S L) :=
  pullback.lift (normalizationLift f L e) (𝟙 _)
    ((normalizationLift_structure f L e).trans (Category.id_comp _).symm)

/-- The original finite-component projection is exactly the constructed lift. -/
@[reassoc (attr := simp)]
theorem normalizationSection_fst :
    normalizationSection f L e ≫
      pullback.fst f (NormalizationInExtension.normalizationStructure S L) =
        normalizationLift f L e := by
  exact pullback.lift_fst _ _ _

/-- The actual base projection makes the constructed morphism a real section. -/
@[reassoc (attr := simp)]
theorem normalizationSection_snd :
    normalizationSection f L e ≫
      pullback.snd f (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ := by
  exact pullback.lift_snd _ _ _

/-- Each actual section is a closed immersion, since the original finite map is separated. -/
instance normalizationSection_isClosedImmersion : IsClosedImmersion (normalizationSection f L e) := by
  let : IsClosedImmersion (normalizationSection f L e ≫
      pullback.snd f (NormalizationInExtension.normalizationStructure S L)) := by
    rw [normalizationSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (normalizationSection f L e)
    (pullback.snd f (NormalizationInExtension.normalizationStructure S L))

end DeJongAlterations.Geometry.FiniteBirationalNormal
