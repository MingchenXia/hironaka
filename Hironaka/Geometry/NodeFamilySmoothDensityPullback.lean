import Hironaka.Geometry.NodeFamilySmoothDensityBaseChange
import Mathlib.RingTheory.FiniteStability

/-!
# Density of the original relative node smooth locus after every actual field point

A genuine surjective tensor-polynomial presentation retains its exact variable images.
No converse base-change criterion for smoothness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace Hironaka.Geometry.NodeFamilySmoothDensityPullback

open Algebra.NodeBlowupChart Algebra.NodeFamilyBaseChange
open NodeFamilyFlat NodeFamilySmooth NodeFamilyGeometricPurity NodeFamilySmoothDensity

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K]

/-- A genuine surjective two-variable field presentation has at most one coordinate-zero prime. -/
theorem zeroGenerator_subsingleton {B : Type u} [CommRing B]
    (f : MvPolynomial (Fin 2) K →+* B) (hf : Function.Surjective f) :
    {p : PrimeSpectrum B | ∀ i : Fin 2, f (MvPolynomial.X i) ∈ p.asIdeal}.Subsingleton := by
  have hcomap (p : PrimeSpectrum B) (hp : ∀ i : Fin 2, f (MvPolynomial.X i) ∈ p.asIdeal) :
      p.asIdeal.comap f = MvPolynomial.idealOfVars (Fin 2) K := by
    apply ((idealOfVars_isMaximal K).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hp i
  intro p hp q hq
  apply PrimeSpectrum.ext
  apply Ideal.comap_injective_of_surjective f hf
  exact (hcomap p hp).trans (hcomap q hq).symm

variable {A : Type u} [CommRing A] [Algebra A K]

/-- The actual surjective coefficient-extended polynomial presentation, with no ideal-equality casts. -/
def tensorPolynomialMap (t : A) : MvPolynomial (Fin 2) K →ₐ[K] K ⊗[A] Node A t :=
  (Algebra.TensorProduct.map (AlgHom.id K K)
    (Ideal.Quotient.mkₐ A (Algebra.NodeChart.uChartIdeal A t))).comp
      (MvPolynomial.algebraTensorAlgEquiv A K).symm.toAlgHom

/-- Tensor right exactness proves surjectivity of this actual presentation. -/
theorem tensorPolynomialMap_surjective (t : A) : Function.Surjective (tensorPolynomialMap K t) :=
  (Algebra.FiniteType.baseChangeAux_surj K Ideal.Quotient.mk_surjective).comp
    (MvPolynomial.algebraTensorAlgEquiv A K).symm.surjective

/-- The actual variable images are the literal original node coordinates tensored with one. -/
theorem tensorPolynomialMap_X (t : A) (i : Fin 2) :
    tensorPolynomialMap K t (MvPolynomial.X i) = 1 ⊗ₜ[A] coordinate t i := by
  change (Algebra.TensorProduct.map (AlgHom.id K K)
    (Ideal.Quotient.mkₐ A (Algebra.NodeChart.uChartIdeal A t)))
      ((MvPolynomial.algebraTensorAlgEquiv A K).symm (MvPolynomial.X i)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X]
  rfl

/-- The actual projection from the affine tensor spectrum to the original node. -/
def tensorCoefficientProjection (t : A) :
    Spec (CommRingCat.of (K ⊗[A] Node A t)) ⟶ Spec (CommRingCat.of (Node A t)) :=
  Spec.map (CommRingCat.ofHom
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : Node A t →ₐ[A] K ⊗[A] Node A t)))

private theorem tensor_no_open_singleton (t : A)
    (x : Spec (CommRingCat.of (K ⊗[A] Node A t))) :
    ¬ IsOpen ({x} : Set (Spec (CommRingCat.of (K ⊗[A] Node A t)))) := by
  let e : Spec (CommRingCat.of (K ⊗[A] Node A t)) ≅
      Spec (CommRingCat.of (Node K (algebraMap A K t))) :=
    Scheme.Spec.mapIso (nodeBaseChangeEquiv K t).toRingEquiv.toCommRingCatIso.symm.op
  intro hx
  have ho := e.hom.homeomorph.isOpenMap _ hx
  rw [Set.image_singleton] at ho
  exact node_not_isOpen_singleton K _ _ ho

/-- The actual inverse image of the two original coordinate opens is dense on the tensor spectrum. -/
theorem tensor_coordinateUnion_preimage_dense (t : A) :
    Dense ((tensorCoefficientProjection K t) ⁻¹'
      ((coordinateOpen t 0 ⊔ coordinateOpen t 1 :
        (Spec (CommRingCat.of (Node A t))).Opens) : Set (Spec (CommRingCat.of (Node A t))))) := by
  apply dense_of_subsingleton_compl (tensor_no_open_singleton K t)
  intro p hp q hq
  apply zeroGenerator_subsingleton K (tensorPolynomialMap K t).toRingHom (tensorPolynomialMap_surjective K t)
  · change ¬ ((1 ⊗ₜ[A] coordinate t 0) ∉ p.asIdeal ∨
        (1 ⊗ₜ[A] coordinate t 1) ∉ p.asIdeal) at hp
    change ∀ i : Fin 2, tensorPolynomialMap K t (MvPolynomial.X i) ∈ p.asIdeal
    simp only [tensorPolynomialMap_X, Fin.forall_fin_two]
    exact ⟨not_not.mp (not_or.mp hp).1, not_not.mp (not_or.mp hp).2⟩
  · change ¬ ((1 ⊗ₜ[A] coordinate t 0) ∉ q.asIdeal ∨
        (1 ⊗ₜ[A] coordinate t 1) ∉ q.asIdeal) at hq
    change ∀ i : Fin 2, tensorPolynomialMap K t (MvPolynomial.X i) ∈ q.asIdeal
    simp only [tensorPolynomialMap_X, Fin.forall_fin_two]
    exact ⟨not_not.mp (not_or.mp hq).1, not_not.mp (not_or.mp hq).2⟩

local instance (t : A) : LocallyOfFinitePresentation (nodeMorphism t) :=
  nodeMorphism_locallyOfFinitePresentation t

/-- The original native relative smooth locus has dense actual inverse image on the tensor spectrum. -/
theorem tensor_original_smoothLocus_preimage_dense (t : A) :
    Dense ((tensorCoefficientProjection K t) ⁻¹'
      ((nodeMorphism t).smoothLocus : Set (Spec (CommRingCat.of (Node A t))))) :=
  (tensor_coordinateUnion_preimage_dense K t).mono
    (Set.preimage_mono (coordinateUnion_le_smoothLocus t))

/-- The genuine affine pullback isomorphism, before choosing a field-node presentation. -/
def nodeTensorIso (t : A) : nodeFieldBaseChange K t ≅
    Spec (CommRingCat.of (K ⊗[A] Node A t)) :=
  pullbackSymmetry
    (Spec.map (CommRingCat.ofHom (algebraMap A (Node A t))))
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≪≫ pullbackSpecIso A K (Node A t)

/-- This native tensor isomorphism preserves the literal original-node projection. -/
theorem nodeTensorIso_original (t : A) :
    (nodeTensorIso K t).hom ≫ tensorCoefficientProjection K t =
      pullback.fst (nodeMorphism t) (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  dsimp only [nodeTensorIso, Iso.trans_hom, tensorCoefficientProjection, nodeMorphism]
  rw [Category.assoc, pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd]

/-- After every field point, the actual inverse image of the original node relative smooth locus is dense. -/
theorem original_smoothLocus_preimage_dense (t : A) :
    Dense ((pullback.fst (nodeMorphism t) (Spec.map (CommRingCat.ofHom (algebraMap A K)))) ⁻¹'
      ((nodeMorphism t).smoothLocus : Set (Spec (CommRingCat.of (Node A t))))) := by
  have h := (tensor_original_smoothLocus_preimage_dense K t).preimage
    (nodeTensorIso K t).hom.isOpenEmbedding.isOpenMap
  change Dense (((nodeTensorIso K t).hom ≫ tensorCoefficientProjection K t) ⁻¹'
    ((nodeMorphism t).smoothLocus : Set (Spec (CommRingCat.of (Node A t))))) at h
  rw [nodeTensorIso_original] at h
  exact h

end Hironaka.Geometry.NodeFamilySmoothDensityPullback
