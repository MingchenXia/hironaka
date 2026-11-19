import Hironaka.Algebra.PluckerQuotTransitionContraction
import Hironaka.Geometry.QuotGrassmannPivotOriginalPullback
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The actual affine original contraction image is its original free quotient

The factor, its native left inverse, and the actual image isomorphism are
produced from the literal original matrices. No local rank certificate or
image comparison is supplied. Identification with the global contraction
restriction is a separate obligation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original native affine matrix maps preserve literal matrix composition. -/
theorem originalMatrixQuotientSheaf_comp (B : Type u) [CommRing B]
    {I E S : Type u} [Fintype I] [Fintype E] [Fintype S]
    (M : Matrix I E B) (J : Matrix S I B) :
    originalMatrixQuotientSheaf B M ≫ originalMatrixQuotientSheaf B J =
      originalMatrixQuotientSheaf B (J * M) := by
  let F := tilde.functor (.of B)
  let a := coordinateSheafIsoFree B E
  let b := coordinateSheafIsoFree B I
  let c := coordinateSheafIsoFree B S
  have hm : ModuleCat.ofHom M.mulVecLin ≫ ModuleCat.ofHom J.mulVecLin =
      ModuleCat.ofHom (J * M).mulVecLin := by
    apply ModuleCat.hom_ext
    exact (Matrix.mulVecLin_mul J M).symm
  exact (originalConjugatedFunctor_comp F a b c
    (ModuleCat.ofHom M.mulVecLin) (ModuleCat.ofHom J.mulVecLin)).trans
      (congrArg (fun h => a.inv ≫ F.map h ≫ c.hom) hm)

private theorem originalConjugatedFunctor_identity {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M : C} {M' : D} (e : F.obj M ≅ M') :
    e.inv ≫ F.map (𝟙 M) ≫ e.hom = 𝟙 M' := by
  rw [F.map_id, Category.id_comp, e.inv_hom_id]

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The same literal original polynomial contraction matrix as an actual native sheaf map. -/
def originalAffineContraction :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) (ι ⊕ κ) ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf)
        ((ι → ι ⊕ κ) × ι) :=
  originalMatrixQuotientSheaf (ChartRing R ι κ)
    (originalContractionMatrix (Equiv.refl (ι → ι ⊕ κ))
      (normalizedMatrix (universalMatrix R ι κ)))

/-- The original adjugate factor gives an actual native factor map. -/
def originalAffineContractionFactor :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι ⟶
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf)
        ((ι → ι ⊕ κ) × ι) :=
  originalMatrixQuotientSheaf (ChartRing R ι κ)
    (originalContractionFactor (Equiv.refl (ι → ι ⊕ κ))
      (normalizedMatrix (universalMatrix R ι κ)))

/-- The exact original frozen universal quotient factors the actual affine contraction. -/
theorem originalAffineContraction_factor :
    universalQuotient R ι κ ≫ originalAffineContractionFactor R ι κ =
      originalAffineContraction R ι κ := by
  rw [originalUniversalQuotient_eq_matrix]
  exact (originalMatrixQuotientSheaf_comp (ChartRing R ι κ) _ _).trans
    (congrArg (originalMatrixQuotientSheaf (ChartRing R ι κ))
      (originalContractionMatrix_eq_factor_mul _ _).symm)

/-- Projection onto the actual original identity-pivot rows, as an actual linear map. -/
def originalAffineContractionProjectionLinear :
    (((ι → ι ⊕ κ) × ι) → ChartRing R ι κ) →ₗ[ChartRing R ι κ]
      (ι → ChartRing R ι κ) where
  toFun v i := v (Sum.inl, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original pivot-row projection gives an actual native sheaf retraction. -/
def originalAffineContractionRetraction :
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf)
      ((ι → ι ⊕ κ) × ι) ⟶
    SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  (coordinateSheafIsoFree (ChartRing R ι κ) ((ι → ι ⊕ κ) × ι)).inv ≫
    (tilde.functor (.of (ChartRing R ι κ))).map
      (ModuleCat.ofHom (originalAffineContractionProjectionLinear R ι κ)) ≫
    (coordinateSheafIsoFree (ChartRing R ι κ) ι).hom

/-- The actual original native adjugate factor has its internally produced left inverse. -/
theorem originalAffineContractionFactor_retraction :
    originalAffineContractionFactor R ι κ ≫ originalAffineContractionRetraction R ι κ =
      𝟙 _ := by
  let B := ChartRing R ι κ
  let J := originalContractionFactor (Equiv.refl (ι → ι ⊕ κ))
    (normalizedMatrix (universalMatrix R ι κ))
  have hp : J.submatrix (fun i => (Sum.inl, i)) id = 1 := by
    exact originalContractionFactor_pivot_rows (Equiv.refl (ι → ι ⊕ κ))
      (Equiv.refl (ι ⊕ κ)) (universalMatrix R ι κ)
  have hl : ModuleCat.ofHom J.mulVecLin ≫
      ModuleCat.ofHom (originalAffineContractionProjectionLinear R ι κ) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change (J.submatrix (fun i => (Sum.inl, i)) id).mulVec v = v
    rw [hp, Matrix.one_mulVec]
  let F := tilde.functor (.of B)
  let a := coordinateSheafIsoFree B ι
  let b := coordinateSheafIsoFree B ((ι → ι ⊕ κ) × ι)
  exact (originalConjugatedFunctor_comp F a b a
    (ModuleCat.ofHom J.mulVecLin)
    (ModuleCat.ofHom (originalAffineContractionProjectionLinear R ι κ))).trans
      ((congrArg (fun h => a.inv ≫ F.map h ≫ a.hom) hl).trans
        (originalConjugatedFunctor_identity F a))

instance originalAffineContractionFactor_isSplitMono :
    IsSplitMono (originalAffineContractionFactor R ι κ) :=
  ⟨⟨originalAffineContractionRetraction R ι κ,
    originalAffineContractionFactor_retraction R ι κ⟩⟩

instance originalAffineContractionFactor_mono : Mono (originalAffineContractionFactor R ι κ) :=
  inferInstance

/-- The image factorization itself is produced from the actual original split epi and split mono. -/
def originalAffineContractionImageFactorisation :
    StrongEpiMonoFactorisation (originalAffineContraction R ι κ) where
  I := SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι
  e := universalQuotient R ι κ
  m := originalAffineContractionFactor R ι κ
  fac := originalAffineContraction_factor R ι κ

/-- The actual native original contraction image is the SAME actual original free quotient target. -/
def originalAffineContractionImageIso :
    Abelian.image (originalAffineContraction R ι κ) ≅
      SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι :=
  Abelian.imageIsoImage (originalAffineContraction R ι κ) ≪≫
    IsImage.isoExt (Image.isImage (originalAffineContraction R ι κ))
      (originalAffineContractionImageFactorisation R ι κ).toMonoIsImage

/-- The actual image isomorphism preserves the literal original adjugate inclusion. -/
theorem originalAffineContractionImageIso_inclusion :
    (originalAffineContractionImageIso R ι κ).hom ≫ originalAffineContractionFactor R ι κ =
      Abelian.image.ι (originalAffineContraction R ι κ) := by
  let C := originalAffineContraction R ι κ
  let F := originalAffineContractionImageFactorisation R ι κ
  let e := Abelian.imageIsoImage C
  have hi : (IsImage.isoExt (Image.isImage C) F.toMonoIsImage).hom ≫
      originalAffineContractionFactor R ι κ = image.ι C :=
    IsImage.isoExt_hom_m (Image.isImage C) F.toMonoIsImage
  exact (Category.assoc e.hom _ _).trans
    ((congrArg (fun h => e.hom ≫ h) hi).trans
      (Abelian.imageIsoImage_hom_comp_image_ι C))

/-- The SAME original frozen universal quotient is recovered by the actual native image isomorphism. -/
theorem originalAffineContractionImageIso_quotient :
    Abelian.factorThruImage (originalAffineContraction R ι κ) ≫
      (originalAffineContractionImageIso R ι κ).hom = universalQuotient R ι κ := by
  apply (cancel_mono (originalAffineContractionFactor R ι κ)).mp
  rw [Category.assoc, originalAffineContractionImageIso_inclusion, Abelian.image.fac,
    originalAffineContraction_factor]

end Hironaka.Geometry.QuotGrassmann
