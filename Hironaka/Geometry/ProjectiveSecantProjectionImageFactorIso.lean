import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Intrinsic actual native scheme images of whole schematically dominant closed factors
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original ideal subscheme composite has its native Cartesian square along the SAME original closed immersion. Reused from EnvelopeProperty/Berkovich/SchemeIdealExtension.lean. -/
theorem ideal_subscheme_closed_composite_isPullback
    {Z Y : Scheme.{u}} (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    IsPullback (𝟙 I.subscheme) I.subschemeι (I.subschemeι ≫ j) j :=
  IsPullback.of_horiz_isIso_mono ⟨by simp⟩

/-- The entire actual ideal pushforward retracts under its SAME original closed immersion. Reused from EnvelopeProperty/Berkovich/SchemeIdealExtension.lean. -/
theorem ideal_comap_map_closedImmersion
    {Z Y : Scheme.{u}} (I : Z.IdealSheafData) (j : Z ⟶ Y) [IsClosedImmersion j] :
    (I.map j).comap j = I := by
  have h := (ideal_subscheme_closed_composite_isPullback I j).flip
  rw [Scheme.IdealSheafData.map,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (I.subschemeι ≫ j) j,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom (pullback.fst j (I.subschemeι ≫ j)),
    h.isoPullback_hom_fst, Scheme.IdealSheafData.ker_subschemeι]

/-- The actual whole canonical native image map has zero whole kernel. The native kernel/comap proof is reused from EnvelopeProperty/SchemeImageFlat.lean. -/
theorem toImage_isSchemeTheoreticallyDominant {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  have h : f.toImage.ker.map f.imageι = (⊥ : f.image.IdealSheafData).map f.imageι := by
    rw [Scheme.IdealSheafData.map_ker, f.toImage_imageι,
      Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
  have h' := congrArg (fun I => I.comap f.imageι) h
  simpa only [ideal_comap_map_closedImmersion] using h'

/-- The entire original closed embedding kernel is literally the SAME original map's native image embedding kernel. -/
theorem closedFactor_kernel_eq_image
    {X Y I : Scheme.{u}} (f : X ⟶ Y) (j : I ⟶ Y) [IsClosedImmersion j]
    (a : X ⟶ I) [IsSchemeTheoreticallyDominant a] (ht : a ≫ j = f) :
    j.ker = f.imageι.ker := by
  have h : j.ker = f.ker := by
    rw [← ht, Scheme.Hom.ker_comp, a.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  simpa only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι] using h

/-- The actual closed-immersion universal property and entire original kernel equality internally produce the actual native image isomorphism. -/
def imageIsoOfClosedFactor
    {X Y I : Scheme.{u}} (f : X ⟶ Y) (j : I ⟶ Y) [IsClosedImmersion j]
    (a : X ⟶ I) [IsSchemeTheoreticallyDominant a] (ht : a ≫ j = f) : f.image ≅ I := by
  let h := closedFactor_kernel_eq_image f j a ht
  let : IsIso (IsClosedImmersion.lift j f.imageι h.le) := IsClosedImmersion.isIso_lift j f.imageι h
  exact asIso (IsClosedImmersion.lift j f.imageι h.le)

/-- The actual native-image isomorphism retains the literal entire original closed embedding triangle. -/
theorem imageIsoOfClosedFactor_hom_embedding
    {X Y I : Scheme.{u}} (f : X ⟶ Y) (j : I ⟶ Y) [IsClosedImmersion j]
    (a : X ⟶ I) [IsSchemeTheoreticallyDominant a] (ht : a ≫ j = f) :
    (imageIsoOfClosedFactor f j a ht).hom ≫ j = f.imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The same actual native-image isomorphism retains the literal entire original source image triangle. -/
theorem toImage_imageIsoOfClosedFactor_hom
    {X Y I : Scheme.{u}} (f : X ⟶ Y) (j : I ⟶ Y) [IsClosedImmersion j]
    (a : X ⟶ I) [IsSchemeTheoreticallyDominant a] (ht : a ≫ j = f) :
    f.toImage ≫ (imageIsoOfClosedFactor f j a ht).hom = a := by
  rw [← cancel_mono j, Category.assoc, imageIsoOfClosedFactor_hom_embedding, f.toImage_imageι, ht]

end Hironaka.Geometry.ProjectiveSecant
