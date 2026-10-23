import DeJongAlterations.Core
import DeJongAlterations.Divisor
import DeJongAlterations.Projective

/-!
# The full alteration theorem as an explicit proof target

`AlterationWithBoundary` is the output to be constructed, not a hypothesis of an
existence theorem. The arbitrary-field target below is proved by
`StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem`.
The perfect-field generically étale refinement remains a separate target.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace DeJongAlterations

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The complete geometric output of de Jong 1996, Theorem 4.1.
No morphism from the compactification to `X` is required. -/
structure AlterationWithBoundary (p : X ⟶ Spec (.of k)) (Z : Set X) where
  source : Scheme.{u}
  compactification : Scheme.{u}
  sourceStructure : source ⟶ Spec (.of k)
  compactificationStructure : compactification ⟶ Spec (.of k)
  alteration : source ⟶ X
  inclusion : source ⟶ compactification
  boundary : compactification.IdealSheafData
  sourceVariety : IsVariety sourceStructure
  compactificationVariety : IsVariety compactificationStructure
  alterationOver : alteration ≫ p = sourceStructure
  inclusionOver : inclusion ≫ compactificationStructure = sourceStructure
  isAlteration : IsAlteration alteration
  isOpenImmersion : IsOpenImmersion inclusion
  projective : IsProjectiveOver compactificationStructure
  regular : IsRegularScheme compactification
  normalCrossings : IsStrictNormalCrossings boundary
  boundarySupport : (boundary.support : Set compactification) =
    inclusion '' (alteration ⁻¹' Z) ∪ (Set.range inclusion)ᶜ

/-- The full output really implies the regular-alteration core, since regularity
is inherited by the open source inside the compactification. -/
theorem AlterationWithBoundary.toRegularCore {p : X ⟶ Spec (.of k)} {Z : Set X}
    (d : AlterationWithBoundary p Z) : HasRegularAlteration p := by
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  exact ⟨d.source, d.sourceStructure, d.alteration, d.sourceVariety,
    d.alterationOver, d.isAlteration, d.regular.of_isOpenImmersion d.inclusion⟩

/-- The identity solves the empty-boundary problem on an already regular
projective variety. This does not assert existence for arbitrary varieties. -/
def identityAlterationWithBoundary (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (hreg : IsRegularScheme X) :
    AlterationWithBoundary p ∅ where
  source := X
  compactification := X
  sourceStructure := p
  compactificationStructure := p
  alteration := 𝟙 X
  inclusion := 𝟙 X
  boundary := ⊤
  sourceVariety := inferInstance
  compactificationVariety := inferInstance
  alterationOver := Category.id_comp p
  inclusionOver := Category.id_comp p
  isAlteration := inferInstance
  isOpenImmersion := inferInstance
  projective := hp
  regular := hreg
  normalCrossings := isStrictNormalCrossings_top X
  boundarySupport := by ext x; simp

/-- Full Theorem 4.1 as a proposition, proved for every field by
`StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem`. -/
def DeJongAlterationTheorem (k : Type u) [Field k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p →
    ∀ Z : TopologicalSpace.Closeds X, Z ≠ ⊤ →
      Nonempty (AlterationWithBoundary p (Z : Set X))

/-- The perfect-field refinement of 4.1 and smoothness in Remark 4.2.
This is also an unproved proposition, with no existence axiom. -/
def DeJongPerfectAlterationTheorem (k : Type u) [Field k] [PerfectField k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)), IsVariety p →
    ∀ Z : TopologicalSpace.Closeds X, Z ≠ ⊤ →
      ∃ d : AlterationWithBoundary p (Z : Set X),
        IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure

end DeJongAlterations
