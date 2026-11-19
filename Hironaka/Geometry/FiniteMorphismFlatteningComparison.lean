import Hironaka.Geometry.FiniteMorphismFlatteningCartesian
import Hironaka.Geometry.FiniteMorphismFlatteningImage

/-!
# The global native generic-fibre closure has the actual algebra-image charts

The comparison constructs actual Cartesian squares, starting with the
original tensor maps, original chart inclusions, native generic fibre
and its actual kernel image. It supplies no gluing or transform certificate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka.Geometry.FiniteMorphismFlattening

open Algebra.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The original generic tensor algebra maps to the actual native generic residue point. -/
abbrev genericTensorToResidue : Spec (.of (FractionRing R ⊗[R] A)) ⟶
    Spec ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) :=
  genericTensorStructure R A ≫ Spec.map (fractionGenericResidueIso (.of R)).inv

/-- The actual original tensor map is the actual native generic fibre of the original chart map. -/
theorem chartGenericMap_native_isPullback (S : Subalgebra R (FractionRing R)) :
    IsPullback (chartGenericMap R A S) (genericTensorToResidue R A)
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)))
      ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) := by
  exact (chartGenericMap_isPullback_over_base R A S).of_iso
    (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (fractionGenericResidueIso (.of R)).inv)) (Iso.refl _)
    (by simp) (by simp [genericTensorToResidue]) (by simp)
    (by simpa using (fractionGenericResidueIso_structure (.of R)).symm)

variable (I : Ideal R) (g : R) (hg : g ∈ I) (hg0 : g ≠ 0)

/-- The original generic tensor chart maps into the actual native generic fibre of the actual base change. -/
def genericChartToGlobalFiber : Spec (.of (FractionRing R ⊗[R] A)) ⟶
    (baseChangedToBase R A I).fiber (genericPoint (Spec (.of R))) :=
  pullback.lift
    (chartGenericMap R A (affineBlowupFractionChart I g) ≫ chartBaseChangedMap R A I g hg hg0)
    (genericTensorToResidue R A) (by
      rw [Category.assoc, chartBaseChangedMap_structure]
      exact (chartGenericMap_native_isPullback R A (affineBlowupFractionChart I g)).w)

/-- The original generic tensor map is the actual open pullback of the actual native generic-fibre inclusion. -/
theorem genericChartToGlobalFiber_isPullback :
    IsPullback (chartGenericMap R A (affineBlowupFractionChart I g))
      (genericChartToGlobalFiber R A I g hg hg0)
      (chartBaseChangedMap R A I g hg hg0) (genericFiberInclusion R A I) := by
  have houter : IsPullback (chartGenericMap R A (affineBlowupFractionChart I g))
      (genericChartToGlobalFiber R A I g hg hg0 ≫
        (baseChangedToBase R A I).fiberToSpecResidueField (genericPoint (Spec (.of R))))
      (chartBaseChangedMap R A I g hg hg0 ≫ baseChangedToBase R A I)
      ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) := by
    simpa [genericChartToGlobalFiber, Scheme.Hom.fiberToSpecResidueField] using
      chartGenericMap_native_isPullback R A (affineBlowupFractionChart I g)
  exact houter.of_bot (by
    simp [genericChartToGlobalFiber, genericFiberInclusion, Scheme.Hom.fiberι])
    (IsPullback.of_hasPullback _ _)

/-- The actual affine algebra-image chart maps into the one global native closed transform. -/
def chartToGlobalTransform :
    Spec (.of (pureTransformAlgebra R A (affineBlowupFractionChart I g))) ⟶ globalTransform R A I :=
  (chartTransformImageIso R A (affineBlowupFractionChart I g)).hom ≫
    imageOpenMap (genericFiberInclusion R A I)
      (chartGenericMap R A (affineBlowupFractionChart I g))
      (genericChartToGlobalFiber R A I g hg hg0) (chartBaseChangedMap R A I g hg hg0)
      (genericChartToGlobalFiber_isPullback R A I g hg hg0)

/-- The actual affine closed transform and global native closed transform form a Cartesian square. -/
theorem chartToGlobalTransform_closed_isPullback :
    IsPullback (chartToGlobalTransform R A I g hg hg0)
      (chartTransformInclusion R A (affineBlowupFractionChart I g))
      (globalTransformInclusion R A I) (chartBaseChangedMap R A I g hg hg0) := by
  have hleft : IsPullback (chartTransformImageIso R A (affineBlowupFractionChart I g)).hom
      (chartTransformInclusion R A (affineBlowupFractionChart I g))
      (chartGenericMap R A (affineBlowupFractionChart I g)).imageι
      (𝟙 (Spec (.of (affineBlowupFractionChart I g ⊗[R] A)))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa [chartToGlobalTransform] using hleft.paste_horiz
    (imageOpenMap_isPullback (genericFiberInclusion R A I)
      (chartGenericMap R A (affineBlowupFractionChart I g))
      (genericChartToGlobalFiber R A I g hg hg0) (chartBaseChangedMap R A I g hg hg0)
      (genericChartToGlobalFiber_isPullback R A I g hg hg0)).flip

/-- Exact chart comparison: the original algebra-image structure is the actual restriction
of the single global native generic-fibre closure to the original blowup chart. -/
theorem chartToGlobalTransform_isPullback :
    IsPullback (chartToGlobalTransform R A I g hg hg0)
      (chartTransformMap R A (affineBlowupFractionChart I g))
      (globalTransformMap R A I) (affineBlowupChartInclusion I g hg hg0) := by
  simpa [globalTransformMap] using
    (chartToGlobalTransform_closed_isPullback R A I g hg hg0).paste_vert
      (chartBaseChangedMap_isPullback R A I g hg hg0)

end Hironaka.Geometry.FiniteMorphismFlattening
