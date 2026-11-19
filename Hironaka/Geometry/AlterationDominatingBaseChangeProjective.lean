import Hironaka.Geometry.AlterationDominatingBaseChange
import Hironaka.Geometry.RelativeChowProjectiveSpace

/-!
# Actual projective presentations of dominating alteration base changes

An actual closed presentation of the base alteration induces its actual
native closed base-change embedding. Native pullback pasting identifies
the target with projective space over the original source scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

noncomputable section

namespace Hironaka.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y S T : Scheme.{u}}

/-- Native pullback pasting identifies the actual base change of relative
projective space with actual relative projective space over the new base. -/
def projectiveBaseChangeIso (f : X ⟶ S) (d : ℕ) :
    pullback f (relativeStructure S d) ≅ relativeSpace X d :=
  pullbackRightPullbackFstIso (integerStructure S) (projectiveSpaceStructure IntegerRing d) f ≪≫
    pullback.congrHom (integerStructure_naturality f) rfl

@[reassoc (attr := simp)]
theorem projectiveBaseChangeIso_hom_structure (f : X ⟶ S) (d : ℕ) :
    (projectiveBaseChangeIso f d).hom ≫ relativeStructure X d =
      pullback.fst f (relativeStructure S d) := by
  simp [projectiveBaseChangeIso, relativeStructure]

/-- The actual base-change closed projective embedding supplied by an actual
closed projective embedding of the original base morphism. -/
def baseChangeEmbedding (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) (he : e ≫ relativeStructure S d = g) :
    pullback f g ⟶ relativeSpace X d :=
  pullback.map f g f (relativeStructure S d) (𝟙 X) e (𝟙 S)
    (by simp) (by simpa using he.symm) ≫ (projectiveBaseChangeIso f d).hom

instance baseChangeEmbedding_isClosedImmersion
    (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S d = g) :
    IsClosedImmersion (baseChangeEmbedding f g e he) := by
  let : IsClosedImmersion
      (pullback.map f g f (relativeStructure S d) (𝟙 X) e (𝟙 S)
        (by simp) (by simpa using he.symm)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      inferInstance inferInstance (by simp) (by simpa using he.symm)
  unfold baseChangeEmbedding
  infer_instance

@[reassoc (attr := simp)]
theorem baseChangeEmbedding_structure
    (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) (he : e ≫ relativeStructure S d = g) :
    baseChangeEmbedding f g e he ≫ relativeStructure X d = pullback.fst f g := by
  simp [baseChangeEmbedding, pullback.map, Category.assoc]

/-- The actual dominating reduced component has a genuine closed projective
presentation whenever the base alteration has an actual closed presentation. -/
theorem exists_projective_alteration_component
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [IsDominant f] [IsAlteration g]
    {d : ℕ} (e : Y ⟶ relativeSpace S d) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S d = g) :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g) (a : T ⟶ relativeSpace X d),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) ∧
      IsClosedImmersion a ∧ a ≫ relativeStructure X d = j ≫ pullback.fst f g := by
  obtain ⟨T, j, hT, hj, hc, hq, hb⟩ := exists_alteration_component f g
  let := hj
  exact ⟨T, j, j ≫ baseChangeEmbedding f g e he,
    hT, hj, hc, hq, hb, inferInstance, by simp⟩

end Hironaka.Geometry.AlterationDominatingBaseChange
