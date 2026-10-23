import DeJongAlterations.Theorem
import DeJongAlterations.Composition
import DeJongAlterations.Geometry.GenericallyEtaleComposition

/-!
# The full alteration-with-boundary reduction of de Jong 4.4

This transports a constructed output on an altered input. It does not prove
existence of that output, and preserves its actual boundary ideal unchanged.
-/

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations

universe u

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- Compose the alteration in a full output, preserving its actual compactification
and exact original boundary ideal. This is de Jong's reduction 4.4. -/
def AlterationWithBoundary.comp {p : X ⟶ Spec (.of k)} {Z : Set X}
    (f : X' ⟶ X) [IsAlteration f]
    (d : AlterationWithBoundary (f ≫ p) (f ⁻¹' Z)) : AlterationWithBoundary p Z where
  source := d.source
  compactification := d.compactification
  sourceStructure := d.sourceStructure
  compactificationStructure := d.compactificationStructure
  alteration := d.alteration ≫ f
  inclusion := d.inclusion
  boundary := d.boundary
  sourceVariety := d.sourceVariety
  compactificationVariety := d.compactificationVariety
  alterationOver := by rw [Category.assoc]; exact d.alterationOver
  inclusionOver := d.inclusionOver
  isAlteration := by
    let := d.isAlteration
    exact IsAlteration.comp d.alteration f
  isOpenImmersion := d.isOpenImmersion
  projective := d.projective
  regular := d.regular
  normalCrossings := d.normalCrossings
  boundarySupport := d.boundarySupport

/-- Generic etaleness of the actual composed output is preserved; the unchanged
compactification retains any smoothness property already proved. -/
theorem AlterationWithBoundary.comp_genericallyEtale
    {p : X ⟶ Spec (.of k)} {Z : Set X} (f : X' ⟶ X) [IsAlteration f]
    (d : AlterationWithBoundary (f ≫ p) (f ⁻¹' Z))
    (hf : IsGenericallyEtale f) (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (d.comp f).alteration := hd.comp hf

end DeJongAlterations
