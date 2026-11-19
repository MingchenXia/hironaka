import Hironaka.Geometry.ProjectiveSecantProjectionImageFactorIso
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# The SAME actual native image and native birationality under an actual whole target isomorphism
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual target isomorphism transports native birationality of the SAME actual map, without reducedness or integrality assumptions. -/
theorem birationalOver_of_targetIso {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y') (g : X ⟶ Y) (e : Y' ≅ Y) (H : f ≫ e.hom = g)
    (hbr : Scheme.BirationalOver g (𝟙 Y)) : Scheme.BirationalOver f (𝟙 Y') := by
  have hi : Scheme.BirationalOver (𝟙 Y) e.hom := by
    refine ⟨Scheme.PartialIso.ofIso e.symm, ?_⟩
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, Category.assoc]
  obtain ⟨p, hp⟩ := hbr.trans hi
  refine ⟨p, ?_⟩
  change p.iso.hom ≫ p.target.ι ≫ 𝟙 Y' = p.source.ι ≫ f
  rw [Category.comp_id]
  apply (cancel_mono e.hom).mp
  simpa only [Scheme.PartialIso.IsOver, Category.assoc, H] using hp

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Y') (e : Y ≅ Y') (H : g = f ≫ e.hom)

include H

/-- The actual original whole image factor followed by the actual target isomorphism gives a literal closed factorization of the SAME new actual map. -/
theorem targetIsoImageFactor_triangle : f.toImage ≫ (f.imageι ≫ e.hom) = g := by
  rw [← Category.assoc, f.toImage_imageι, H]

/-- The SAME actual map after an actual entire target isomorphism internally produces its actual native image isomorphism to the SAME original native image, without an image certificate. -/
def targetIsoImageIso : g.image ≅ f.image := by
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  exact imageIsoOfClosedFactor g (f.imageι ≫ e.hom) f.toImage (targetIsoImageFactor_triangle f g e H)

/-- The actual entire native image isomorphism retains the literal whole closed image embedding triangle. -/
theorem targetIsoImageIso_embedding :
    (targetIsoImageIso f g e H).hom ≫ f.imageι ≫ e.hom = g.imageι := by
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  exact imageIsoOfClosedFactor_hom_embedding g (f.imageι ≫ e.hom) f.toImage (targetIsoImageFactor_triangle f g e H)

/-- The actual entire native image isomorphism retains the SAME original whole canonical source-image factor triangle. -/
theorem targetIsoImageIso_toImage : g.toImage ≫ (targetIsoImageIso f g e H).hom = f.toImage := by
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  exact toImage_imageIsoOfClosedFactor_hom g (f.imageι ≫ e.hom) f.toImage (targetIsoImageFactor_triangle f g e H)

/-- The SAME actual map's native image factor is birational after its actual target isomorphism, with its native image and native comparison constructed internally. -/
theorem toImage_birationalOver_of_targetIso (hbr : Scheme.BirationalOver f.toImage (𝟙 f.image)) :
    Scheme.BirationalOver g.toImage (𝟙 g.image) :=
  birationalOver_of_targetIso g.toImage f.toImage (targetIsoImageIso f g e H) (targetIsoImageIso_toImage f g e H) hbr

end Hironaka.Geometry.ProjectiveSecant
