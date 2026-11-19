import Hironaka.Geometry.ProjectiveProjectionPointFinite
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Actual original rational source points produce native projection residue-field isomorphisms

The generic stalk-surjectivity argument is adapted from the repo's native
Hironaka/Scheme/Smooth/GraphPoint.lean residue-field lemmas.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual native surjective stalk maps internally give surjective actual residue-field maps. -/
theorem residueFieldMap_surjective_of_stalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro b
  obtain ⟨a, rfl⟩ := X.residue_surjective x b
  obtain ⟨a', rfl⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) a', ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- An actual composite surjective on native stalks makes the latter actual native residue-field map an isomorphism. -/
theorem residueFieldMap_isIso_of_comp {T X Y : Scheme.{u}} (s : T ⟶ X) (f : X ⟶ Y)
    [SurjectiveOnStalks (s ≫ f)] (t : T) : IsIso (f.residueFieldMap (s t)) := by
  have hcomp := residueFieldMap_surjective_of_stalks (s ≫ f) t
  rw [Scheme.residueFieldMap_comp] at hcomp
  have hs : Function.Surjective (s.residueFieldMap t) := Function.Surjective.of_comp hcomp
  let : IsIso (s.residueFieldMap t) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(s.residueFieldMap t).hom.injective, hs⟩
  let : IsIso (f.residueFieldMap (s t) ≫ s.residueFieldMap t) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(f.residueFieldMap (s t) ≫ s.residueFieldMap t).hom.injective, hcomp⟩
  exact IsIso.of_isIso_comp_right _ (s.residueFieldMap t)

/-- An actual original rational section triangle internally produces the actual original residue-field isomorphism, without any residue-field certificate. -/
theorem residueFieldMap_isIso_at_rational_point {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : (s ≫ f) ≫ g = 𝟙 _) :
    IsIso (f.residueFieldMap (s (⊥ : PrimeSpectrum k))) := by
  let : IsClosedImmersion (s ≫ f) := isClosedImmersion_of_comp_eq_id g (s ≫ f) hs
  exact residueFieldMap_isIso_of_comp s f (⊥ : PrimeSpectrum k)

/-- The SAME original finite projection's original actual residue-field map is an isomorphism at the SAME original rational source point, from its literal original coefficient triangles alone. -/
theorem projectionFromPoint_residueFieldMap_isIso
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hout : pointImage k n p ∉ Set.range i) :
    IsIso ((projectionFromPoint k n p hp i hout).residueFieldMap (s (⊥ : PrimeSpectrum k))) := by
  apply residueFieldMap_isIso_at_rational_point (projectionFromPoint k n p hp i hout)
    (projectiveSpaceStructure k n) s
  rw [Category.assoc, projectionFromPoint_structure, ← Category.assoc, hs]

end Hironaka.Geometry.ProjectiveSecant
