/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Actual original whole sections as the original restriction equalizer

Adapted from the same workspace source `EnvelopeProperty/SchemeSectionsEqualizer.lean`,
SHA256 6faad379321974bc597e47038a627bd94e27128367019823245b3c21dcbb4e91.
All imports and actual gluing APIs are native Mathlib.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProperSteinSectionsEqualizer
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- The actual left section restriction on EVERY original pairwise intersection. -/
def left : (∀ i, Γ(X, U i)) →+* (∀ p : ι × ι, Γ(X, U p.1 ⊓ U p.2)) where
  toFun s p := X.presheaf.map (homOfLE (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).op (s p.1)
  map_one' := by funext p; exact map_one _
  map_mul' s t := by funext p; exact map_mul _ _ _
  map_zero' := by funext p; exact map_zero _
  map_add' s t := by funext p; exact map_add _ _ _

/-- The actual right section restriction, retaining EVERY original section. -/
def right : (∀ i, Γ(X, U i)) →+* (∀ p : ι × ι, Γ(X, U p.1 ⊓ U p.2)) where
  toFun s p := X.presheaf.map (homOfLE (inf_le_right : U p.1 ⊓ U p.2 ≤ U p.2)).op (s p.2)
  map_one' := by funext p; exact map_one _
  map_mul' s t := by funext p; exact map_mul _ _ _
  map_zero' := by funext p; exact map_zero _
  map_add' s t := by funext p; exact map_add _ _ _

/-- The TRUE equalizer of the original whole restriction RingHoms. -/
def compatible : Subring (∀ i, Γ(X, U i)) := (left X U).eqLocus (right X U)

/-- Actual whole section restriction to EVERY original member of the family. -/
def restriction : Γ(X, iSup U) →+* (∀ i, Γ(X, U i)) where
  toFun s i := X.presheaf.map (homOfLE (le_iSup U i)).op s
  map_one' := by funext i; exact map_one _
  map_mul' s t := by funext i; exact map_mul _ _ _
  map_zero' := by funext i; exact map_zero _
  map_add' s t := by funext i; exact map_add _ _ _

/-- Genuine functorial section restriction gives actual whole pairwise compatibility. -/
theorem restriction_mem (s : Γ(X, iSup U)) : restriction X U s ∈ compatible X U := by
  apply funext
  intro p
  change X.presheaf.map _ (X.presheaf.map _ s) = X.presheaf.map _ (X.presheaf.map _ s)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The ORIGINAL whole restriction map is injective by actual sheaf separation. -/
theorem restriction_injective : Function.Injective (restriction X U) := by
  intro s t h
  exact X.sheaf.eq_of_locally_eq U s t (congrFun h)

/-- Actual sheaf gluing constructs BOTH whole inverses of the ORIGINAL section equalizer. -/
def sectionsEquiv : Γ(X, iSup U) ≃+* compatible X U :=
  RingEquiv.ofBijective ((restriction X U).codRestrict (compatible X U) (restriction_mem X U)) (by
    constructor
    · intro s t h
      exact restriction_injective X U (congrArg Subtype.val h)
    · intro s
      have hs : TopCat.Presheaf.IsCompatible X.presheaf U s.1 := by
        intro i j
        exact congrFun s.2 (i,j)
      obtain ⟨g,hg,_⟩ := X.sheaf.existsUnique_gluing U s.1 hs
      exact ⟨g, Subtype.ext (funext hg)⟩)

/-- Every original component retains its ENTIRE original section under the genuine equivalence. -/
theorem sectionsEquiv_apply (s : Γ(X, iSup U)) (i : ι) :
    (sectionsEquiv X U s).1 i = X.presheaf.map (homOfLE (le_iSup U i)).op s := rfl

end DeJongAlterations.Geometry.ProperSteinSectionsEqualizer
