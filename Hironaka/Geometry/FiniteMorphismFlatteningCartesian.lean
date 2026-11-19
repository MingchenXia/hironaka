import Hironaka.Geometry.FiniteMorphismFlatteningGeneric
import Hironaka.Geometry.FiniteMorphismFlatteningCharts
import Hironaka.Algebra.FiniteMorphismFlatteningLocalization

/-!
# The actual affine generic-fibre and original base-change squares

All maps use the original coefficient inclusions and the actual blowup
chart inclusion. Tensor cancellation supplies the generic-fibre square;
the native fraction-residue comparison identifies its point with the
actual native generic point.
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

/-- The original actual generic algebra tensor map. -/
abbrev chartGenericMap (S : Subalgebra R (FractionRing R)) :
    Spec (.of (FractionRing R ⊗[R] A)) ⟶ Spec (.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (tensorAlgMap R A S).toRingHom)

/-- The literal generic tensor coefficient map to the actual original fraction point. -/
abbrev genericTensorStructure :
    Spec (.of (FractionRing R ⊗[R] A)) ⟶ Spec (.of (FractionRing R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R ⊗[R] A)))

omit [IsDomain R] in
/-- Tensor cancellation gives the actual generic base change of the original chart algebra. -/
theorem chartGenericMap_isPullback (S : Subalgebra R (FractionRing R)) :
    IsPullback (chartGenericMap R A S) (genericTensorStructure R A)
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing R)))) := by
  have h : IsPushout
      (CommRingCat.ofHom (algebraMap S (FractionRing R)))
      (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
      (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R ⊗[R] A)))
      (CommRingCat.ofHom (tensorAlgMap R A S).toRingHom) :=
    (CommRingCat.isPushout_tensorProduct S (FractionRing R) (S ⊗[R] A)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (chartGenericTensorEquiv R A S).toRingEquiv.toCommRingCatIso
    (by simp) (by simp)
    (by ext k; simp [chartGenericTensorEquiv, Algebra.TensorProduct.one_def])
    (by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (chartGenericTensorEquiv_comp_includeRight R A S))
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ h).flip

omit [IsDomain R] in
private theorem tensorLeft_algebraMap (S : Subalgebra R (FractionRing R)) :
    algebraMap S (S ⊗[R] A) = Algebra.TensorProduct.includeLeftRingHom := by
  ext s
  simp

/-- The actual fraction point is the actual generic base change of the original fraction subalgebra. -/
theorem fractionChart_isPullback (S : Subalgebra R (FractionRing R)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing R))))
      (𝟙 (Spec (.of (FractionRing R))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  let : Algebra.IsPushout R S (FractionRing R) (FractionRing R) :=
    fractionSubalgebra_isPushout R S
  convert isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (FractionRing R) (FractionRing R)) using 1
  simp

/-- The generic tensor square is over the original base ring and retains the original fraction point. -/
theorem chartGenericMap_isPullback_over_base (S : Subalgebra R (FractionRing R)) :
    IsPullback (chartGenericMap R A S) (genericTensorStructure R A)
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  simpa using (chartGenericMap_isPullback R A S).paste_vert (fractionChart_isPullback R S)

variable (I : Ideal R) (g : R) (hg : g ∈ I) (hg0 : g ≠ 0)

/-- The original tensor spectrum maps into the literal original base-changed finite scheme. -/
def chartBaseChangedMap :
    Spec (.of (affineBlowupFractionChart I g ⊗[R] A)) ⟶ baseChanged R A I :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap (affineBlowupFractionChart I g)
      (affineBlowupFractionChart I g ⊗[R] A))) ≫ affineBlowupChartInclusion I g hg hg0)
    (Spec.map (CommRingCat.ofHom (S := affineBlowupFractionChart I g ⊗[R] A)
      (Algebra.TensorProduct.includeRight : A →ₐ[R]
        affineBlowupFractionChart I g ⊗[R] A).toRingHom)) (by
      rw [Category.assoc, affineBlowupChartInclusion_structure]
      exact (chartTensor_isPullback R A (affineBlowupFractionChart I g)).w)

/-- The actual tensor chart is Cartesian over the original native blowup chart. -/
theorem chartBaseChangedMap_isPullback :
    IsPullback (chartBaseChangedMap R A I g hg hg0)
      (Spec.map (CommRingCat.ofHom (algebraMap (affineBlowupFractionChart I g)
        (affineBlowupFractionChart I g ⊗[R] A))))
      (baseChangedMap R A I) (affineBlowupChartInclusion I g hg hg0) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (affineBlowupStructure I) (originalMap R A))
    (h₂₂ := affineBlowupStructure I)
  · simpa [chartBaseChangedMap, baseChangedMap, originalMap, tensorLeft_algebraMap,
      affineBlowupChartInclusion_structure] using
      chartTensor_isPullback R A (affineBlowupFractionChart I g) |>.flip
  · simp [chartBaseChangedMap, baseChangedMap]
  · exact (IsPullback.of_hasPullback _ _).flip

instance chartBaseChangedMap_isOpenImmersion :
    IsOpenImmersion (chartBaseChangedMap R A I g hg hg0) :=
  MorphismProperty.of_isPullback (chartBaseChangedMap_isPullback R A I g hg hg0).flip inferInstance

/-- The actual tensor chart retains the original coefficient map to the original base. -/
@[reassoc (attr := simp)]
theorem chartBaseChangedMap_structure :
    chartBaseChangedMap R A I g hg hg0 ≫ baseChangedToBase R A I =
      Spec.map (CommRingCat.ofHom (algebraMap (affineBlowupFractionChart I g)
        (affineBlowupFractionChart I g ⊗[R] A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowupFractionChart I g))) := by
  simp [chartBaseChangedMap, baseChangedToBase, baseChangedMap,
    affineBlowupChartInclusion_structure]

end Hironaka.Geometry.FiniteMorphismFlattening
