import Hironaka.Geometry.ProjectiveSecantProjectionScalarCoefficient

/-!
# Entire same-centre point projections preserve actual original source triangles
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint ProjectiveProjectionCenter
open ProjectiveProjection ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  {X Y : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (j : Y ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion j]
  (a : Y ⟶ X) (H : a ≫ i = j)

include H

omit [IsClosedImmersion i] [IsClosedImmersion j] in
/-- The same actual original point stays outside the actual source image by the WHOLE original embedding triangle alone. -/
theorem pointImage_outside_of_source_triangle (hout : pointImage k n p ∉ Set.range i) :
    pointImage k n p ∉ Set.range j := by
  rintro ⟨y, hy⟩
  apply hout
  refine ⟨a y, ?_⟩
  exact (congrArg (fun m : Y ⟶ projectiveSpace k (n + 1) => m y) H).trans hy

/-- The SAME literal actual point projection respects any actual original whole source/closed-embedding triangle, with no defining-ideal or projection-comparison certificate. -/
theorem projectionFromPoint_source_triangle (hout : pointImage k n p ∉ Set.range i) :
    projectionFromPoint k n p hp j (pointImage_outside_of_source_triangle k n p i j a H hout) =
      a ≫ projectionFromPoint k n p hp i hout := by
  let houtj := pointImage_outside_of_source_triangle k n p i j a H hout
  let v := pointVector k n p hp
  let hv := pointVector_ne_zero k n p hp
  let gi := GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal
  let gj := GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n j).toIdeal
  let f := pointProjectionGradedMap k n p hp
  let hi := General.Morph.relevant_of_irrelevant_le gi (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n i))
  let hj := General.Morph.relevant_of_irrelevant_le gj (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n j))
  let hf := originalVectorProjectionGraded_relevant k n i v hv (pointVector_outside k n p hp i hout)
  let hrep := originalSourceRepresentativeCoefficientMap k k n i j a
  have Hr : hrep ≫ General.Morph.map gi hi = General.Morph.map gj hj := by
    rw [General.Morph.map_eq_native gi (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n i)),
      General.Morph.map_eq_native gj (GradedQuotient.irrelevant_le_map _ (representativeIdeal k n j))]
    change ((representativeIso k n j).inv ≫ a ≫ (representativeIso k n i).hom) ≫
      originalInclusion k n (representativeIdeal k n i) = originalInclusion k n (representativeIdeal k n j)
    rw [Category.assoc, Category.assoc, representativeIso_hom_inclusion,
      H, originalRepresentativeIso_inv_inclusion]
  have N := General.Morph.map_naturality f gi gj hi hj hf hrep Hr
  have NN := congrArg (fun m => (representativeIso k n j).hom ≫ m) N
  change projectionFromVector k n j v hv (pointVector_outside k n p hp j houtj) =
    a ≫ projectionFromVector k n i v hv (pointVector_outside k n p hp i hout)
  rw [projectionFromVector_eq_originalGradedMap, projectionFromVector_eq_originalGradedMap]
  simpa only [gi, gj, f, pointProjectionGradedMap, originalCoordinateAmbientGradedMap,
    v, hv, hrep, originalSourceRepresentativeCoefficientMap, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp, GradedRingHom.comp_assoc] using NN

end Hironaka.Geometry.ProjectiveSecant
