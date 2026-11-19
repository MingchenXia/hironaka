import Hironaka.Geometry.ProjectiveSecantProjectionScalarRepresentative
import Hironaka.Geometry.ProjectiveProjectionPointFinite

/-!
# The SAME actual independently normalized scalar projection retains the ENTIRE original projection coefficient triangle
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveProjectionPoint ProjectiveRationalPointCoordinates
open ProjectiveSpaceBaseChange ProjectiveLinearCoordinates BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  {X XL : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (j : XL ⟶ projectiveSpace L (n + 1)) [IsClosedImmersion j] (a : XL ⟶ X)
  (H : a ≫ i = j ≫ projectiveCoefficientMap φ (n + 1))
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

omit [IsClosedImmersion i] [IsClosedImmersion j] in
include H in
/-- Original outside-ness and the literal WHOLE original ambient coefficient triangle internally prove outside-ness of the SAME actual new scalar scheme point. -/
theorem scalarPoint_outside_original_source (hout : pointImage k n p ∉ Set.range i) :
    pointImage L n (scalarPoint k L φ n p hp) ∉ Set.range j := by
  have hpoint := congrArg (fun m : Spec (CommRingCat.of L) ⟶ projectiveSpace k (n + 1) =>
    m (⊥ : PrimeSpectrum L)) (scalarPoint_original k L φ n p hp)
  change projectiveCoefficientMap φ (n + 1)
      (pointImage L n (scalarPoint k L φ n p hp)) =
    p (Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum L)) at hpoint
  rw [show Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum L) = (⊥ : PrimeSpectrum k) from Subsingleton.elim _ _] at hpoint
  rintro ⟨x, hx⟩
  apply hout
  refine ⟨a x, ?_⟩
  have he := congrArg (fun m : XL ⟶ projectiveSpace k (n + 1) => m x) H
  change i (a x) = projectiveCoefficientMap φ (n + 1) (j x) at he
  rw [hx, hpoint] at he
  exact he

include H in
/-- Original closed-source geometry and the actual original rational outside centre internally produce the literal ENTIRE actual projection coefficient triangle, after the internally constructed actual inverse target automorphism. No vector, target automorphism or scheme-map comparison certificate is supplied. -/
theorem projectionFromPoint_scalar_coefficient_triangle (hout : pointImage k n p ∉ Set.range i) :
    let q := scalarPoint k L φ n p hp
    let hq := scalarPoint_structure k L φ n p hp
    let hout' := scalarPoint_outside_original_source k L φ n i j a H p hp hout
    projectionFromPoint L n q hq j hout' ≫ (scalarPointTargetAutomorphism k L φ n p hp).inv ≫
      projectiveCoefficientMap φ n = a ≫ projectionFromPoint k n p hp i hout := by
  let q := scalarPoint k L φ n p hp
  let hq := scalarPoint_structure k L φ n p hp
  let hout' := scalarPoint_outside_original_source k L φ n i j a H p hp hout
  let v := pointVector k n p hp
  let hv := pointVector_ne_zero k n p hp
  let w := pointVector L n q hq
  let hw := pointVector_ne_zero L n q hq
  let gi := GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal
  let gj := GradedQuotient.gradedMk (ProjectiveGrading L (n + 1)) (representativeIdeal L n j).toIdeal
  let f := pointProjectionGradedMap k n p hp
  let f' := pointProjectionGradedMap L n q hq
  let b : ProjectiveGrading k (n + 1) →+*ᵍ ProjectiveGrading L (n + 1) := coefficientGradedMap φ
  let α := scalarProjectionTargetCoefficientGradedMap k n p hp L φ
  let hα := General.Morph.relevant_of_irrelevant_le α (scalarProjectionTargetCoefficientGradedMap_irrelevant_le k n p hp L φ)
  let hb := General.Morph.relevant_of_irrelevant_le b (coefficientGradedMap_irrelevant_le φ)
  let hi := General.Morph.relevant_of_irrelevant_le gi (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n i))
  let hj := General.Morph.relevant_of_irrelevant_le gj (GradedQuotient.irrelevant_le_map _ (representativeIdeal L n j))
  let hf := originalVectorProjectionGraded_relevant k n i v hv (pointVector_outside k n p hp i hout)
  let hf' := originalVectorProjectionGraded_relevant L n j w hw (pointVector_outside L n q hq j hout')
  have N := General.Morph.map_coefficient_square f f' α b gi gj hα hb hi hj hf hf'
    (originalSourceRepresentativeCoefficientMap k L n i j a)
    (originalSourceRepresentativeCoefficientMap_embedding k L n i j a φ H)
    (pointProjectionGraded_coefficient_square k n p hp L φ)
  have htarget : General.Morph.map α hα =
      (scalarPointTargetAutomorphism k L φ n p hp).inv ≫ projectiveCoefficientMap φ n :=
    (General.Morph.map_eq_native α (scalarProjectionTargetCoefficientGradedMap_irrelevant_le k n p hp L φ)).trans
      (scalarProjectionTargetCoefficientGradedMap_native k n p hp L φ)
  rw [htarget] at N
  have NN := congrArg (fun m => (representativeIso L n j).hom ≫ m) N
  change projectionFromVector L n j w hw (pointVector_outside L n q hq j hout') ≫
      (scalarPointTargetAutomorphism k L φ n p hp).inv ≫ projectiveCoefficientMap φ n =
    a ≫ projectionFromVector k n i v hv (pointVector_outside k n p hp i hout)
  rw [projectionFromVector_eq_originalGradedMap, projectionFromVector_eq_originalGradedMap]
  simpa only [gi, gj, f, f', pointProjectionGradedMap, originalCoordinateAmbientGradedMap,
    v, hv, w, hw, originalSourceRepresentativeCoefficientMap, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp, projectiveSpace, GradedRingHom.comp_assoc] using NN

end Hironaka.Geometry.ProjectiveSecant
