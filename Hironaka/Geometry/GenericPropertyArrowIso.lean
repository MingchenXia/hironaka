import Hironaka.Geometry.GenericallyEtaleComposition
import Hironaka.Geometry.ProjectiveSecantProjectionTargetIso

/-!
# Native generic properties and whole images of the same actual isomorphic arrows
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.GenericPropertyArrowIso

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (s : X' ≅ X) (t : Y ≅ Y') (H : s.hom ≫ f ≫ t.hom = g)

/-- The SAME whole image is constructed from the actual source/target isomorphisms and ENTIRE map identity. -/
def imageIso : g.image ≅ f.image := by
  let : IsSchemeTheoreticallyDominant f.toImage := ProjectiveSecant.toImage_isSchemeTheoreticallyDominant f
  exact ProjectiveSecant.imageIsoOfClosedFactor g (f.imageι ≫ t.hom)
    (s.hom ≫ f.toImage) (by rw [Category.assoc, ← Category.assoc f.toImage,
      f.toImage_imageι, H])

/-- The actual WHOLE closed image embedding triangle. -/
theorem imageIso_embedding : (imageIso f g s t H).hom ≫ f.imageι ≫ t.hom = g.imageι := by
  let : IsSchemeTheoreticallyDominant f.toImage := ProjectiveSecant.toImage_isSchemeTheoreticallyDominant f
  exact ProjectiveSecant.imageIsoOfClosedFactor_hom_embedding g (f.imageι ≫ t.hom)
    (s.hom ≫ f.toImage) (by rw [Category.assoc, ← Category.assoc f.toImage,
      f.toImage_imageι, H])

/-- The actual WHOLE original source-to-image triangle. -/
theorem imageIso_toImage : g.toImage ≫ (imageIso f g s t H).hom = s.hom ≫ f.toImage := by
  let : IsSchemeTheoreticallyDominant f.toImage := ProjectiveSecant.toImage_isSchemeTheoreticallyDominant f
  exact ProjectiveSecant.toImage_imageIsoOfClosedFactor_hom g (f.imageι ≫ t.hom)
    (s.hom ≫ f.toImage) (by rw [Category.assoc, ← Category.assoc f.toImage,
      f.toImage_imageι, H])

include s t H in
/-- Native GE follows the SAME actual source and target isomorphisms. -/
theorem genericallyEtale_of_source_targetIso (hf : IsGenericallyEtale f) : IsGenericallyEtale g := by
  rw [← H]
  exact (isGenericallyEtale_of_etale s.hom).comp
    (hf.comp (isGenericallyEtale_of_etale t.hom))

/-- An actual source isomorphism transports the original native birational partial isomorphism. -/
theorem birationalOver_of_sourceIso {X X' Y : Scheme.{u}} (f : X ⟶ Y) (s : X' ≅ X)
    (hf : Scheme.BirationalOver f (𝟙 Y)) : Scheme.BirationalOver (s.hom ≫ f) (𝟙 Y) := by
  have hs : Scheme.BirationalOver (s.hom ≫ f) f := by
    refine ⟨Scheme.PartialIso.ofIso s, ?_⟩
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, Category.assoc]
  exact hs.trans hf

include s t H in
/-- Native BR onto the ENTIRE SAME native image uses its internally produced whole image comparison. -/
theorem toImage_birationalOver_of_source_targetIso
    (hf : Scheme.BirationalOver f.toImage (𝟙 f.image)) :
    Scheme.BirationalOver g.toImage (𝟙 g.image) :=
  ProjectiveSecant.birationalOver_of_targetIso g.toImage (s.hom ≫ f.toImage)
    (imageIso f g s t H) (imageIso_toImage f g s t H)
    (birationalOver_of_sourceIso f.toImage s hf)

/-- The actual native category-of-arrows isomorphism transports GE of its SAME map. -/
theorem genericallyEtale_of_arrowIso (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : IsGenericallyEtale f) : IsGenericallyEtale g := by
  let s := (asIso e.hom.left).symm
  let t := asIso e.hom.right
  apply genericallyEtale_of_source_targetIso f g s t _ hf
  change inv e.hom.left ≫ f ≫ e.hom.right = g
  have hw : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using
    congrArg (fun q : X ⟶ Y' => inv e.hom.left ≫ q) hw.symm

/-- The actual native arrow isomorphism transports BR onto each map's ENTIRE native image. -/
theorem toImage_birationalOver_of_arrowIso (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : Scheme.BirationalOver f.toImage (𝟙 f.image)) :
    Scheme.BirationalOver g.toImage (𝟙 g.image) := by
  let s := (asIso e.hom.left).symm
  let t := asIso e.hom.right
  apply toImage_birationalOver_of_source_targetIso f g s t _ hf
  change inv e.hom.left ≫ f ≫ e.hom.right = g
  have hw : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using
    congrArg (fun q : X ⟶ Y' => inv e.hom.left ≫ q) hw.symm

end Hironaka.Geometry.GenericPropertyArrowIso
