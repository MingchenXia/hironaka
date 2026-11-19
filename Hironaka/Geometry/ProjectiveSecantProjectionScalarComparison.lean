import Hironaka.Geometry.ProjectiveSecantProjectionScalarCoefficient
import Hironaka.Geometry.ProjectiveSecantProjectionScalar

/-!
# The SAME actual independently normalized scalar projection equals the SAME original canonical scalar projection up to its internally produced target automorphism
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates ProjectiveSpaceBaseChange
open ProjectiveLinearCoordinates BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual closed immersion of the SAME canonical original scalar source, produced by the genuine native original embedding scalar square. -/
def scalarClosedInclusion :
    pullback (i ≫ projectiveSpaceStructure k (n + 1)) (Spec.map (CommRingCat.ofHom φ)) ⟶ projectiveSpace L (n + 1) :=
  originalProjectionScalar k L φ (n + 1) i (i ≫ projectiveSpaceStructure k (n + 1)) rfl

instance scalarClosedInclusion_isClosedImmersion : IsClosedImmersion (scalarClosedInclusion k L φ n i) := by
  dsimp only [scalarClosedInclusion, originalProjectionScalar]
  infer_instance

omit [IsClosedImmersion i] in
/-- The entire actual original canonical-source scalar embedding retains the literal whole original coefficient triangle. -/
theorem scalarClosedInclusion_original :
    scalarClosedInclusion k L φ n i ≫ projectiveCoefficientMap φ (n + 1) =
      pullback.fst (i ≫ projectiveSpaceStructure k (n + 1)) (Spec.map (CommRingCat.ofHom φ)) ≫ i :=
  originalProjectionScalar_original k L φ (n + 1) i _ rfl

omit [IsClosedImmersion i] in
/-- The entire actual scalar embedding retains the literal whole new-field structure triangle. -/
theorem scalarClosedInclusion_structure :
    scalarClosedInclusion k L φ n i ≫ projectiveSpaceStructure L (n + 1) =
      pullback.snd (i ≫ projectiveSpaceStructure k (n + 1)) (Spec.map (CommRingCat.ofHom φ)) :=
  originalProjectionScalar_structure k L φ (n + 1) i _ rfl

variable (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hout : pointImage k n p ∉ Set.range i)

omit [IsClosedImmersion i] in
include hout in
/-- Original actual outside-ness internally puts the SAME actual scalar centre outside the SAME canonical original scalar closed source. -/
theorem scalarClosedInclusion_centre_outside :
    pointImage L n (scalarPoint k L φ n p hp) ∉ Set.range (scalarClosedInclusion k L φ n i) :=
  scalarPoint_outside_original_source k L φ n i (scalarClosedInclusion k L φ n i)
    (pullback.fst _ _) (scalarClosedInclusion_original k L φ n i).symm p hp hout

/-- The SAME original closed source and original actual rational centre internally give the actual independently normalized finite projection on the SAME canonical scalar source. -/
def independentlyNormalizedScalarProjection :
    pullback (i ≫ projectiveSpaceStructure k (n + 1)) (Spec.map (CommRingCat.ofHom φ)) ⟶ projectiveSpace L n :=
  projectionFromPoint L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp)
    (scalarClosedInclusion k L φ n i) (scalarClosedInclusion_centre_outside k L φ n i p hp hout)

/-- Finiteness belongs to the SAME actual independently normalized scalar projection on the actual original canonical scalar source. -/
theorem independentlyNormalizedScalarProjection_isFinite :
    IsFinite (independentlyNormalizedScalarProjection k L φ n i p hp hout) :=
  projectionFromPoint_isFinite L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp)
    (scalarClosedInclusion k L φ n i) (scalarClosedInclusion_centre_outside k L φ n i p hp hout)

/-- The SAME actual independently normalized scalar projection, after its internally constructed actual inverse target automorphism, is EXACTLY the canonical scalar projection of the SAME original finite projection, as ENTIRE scheme maps on the canonical original scalar source. No coordinate or scheme comparison certificate is supplied. -/
theorem independentlyNormalizedScalarProjection_comparison :
    independentlyNormalizedScalarProjection k L φ n i p hp hout ≫
      (scalarPointTargetAutomorphism k L φ n p hp).inv =
    originalProjectionScalar k L φ n (projectionFromPoint k n p hp i hout)
      (i ≫ projectiveSpaceStructure k (n + 1)) (projectionFromPoint_structure k n p hp i hout) := by
  let E := scalarPointTargetAutomorphism k L φ n p hp
  have hE : E.inv ≫ projectiveSpaceStructure L n = projectiveSpaceStructure L n := by
    have h := congrArg (fun m => E.inv ≫ m) (scalarPointTargetAutomorphism_structure k L φ n p hp)
    change E.inv ≫ (E.hom ≫ projectiveSpaceStructure L n) = E.inv ≫ projectiveSpaceStructure L n at h
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm
  apply (isPullback_projectiveCoefficientMap φ n).hom_ext
  · rw [Category.assoc, originalProjectionScalar_original]
    exact projectionFromPoint_scalar_coefficient_triangle k L φ n i (scalarClosedInclusion k L φ n i)
      (pullback.fst _ _) (scalarClosedInclusion_original k L φ n i).symm p hp hout
  · rw [Category.assoc, hE, originalProjectionScalar_structure]
    change projectionFromPoint L n _ _ (scalarClosedInclusion k L φ n i) _ ≫ projectiveSpaceStructure L n = _
    rw [projectionFromPoint_structure, scalarClosedInclusion_structure]

end Hironaka.Geometry.ProjectiveSecant
