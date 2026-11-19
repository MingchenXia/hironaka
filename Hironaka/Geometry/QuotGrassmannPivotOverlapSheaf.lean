import Hironaka.Geometry.QuotGrassmannPivotOverlapChange
import Hironaka.Geometry.QuotGrassmannAffine

/-!
# Actual native quotient sheaf matrices on the same affine overlap

The matrices use both actual original coefficient maps into the same native
overlap ring. Their exact matrix triangle produces an actual target sheaf
isomorphism and an exact original-source quotient-map triangle. Comparison
with native pullback of the original chart maps remains a separate interface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.ModuleFlatteningMinors ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual coordinate isomorphisms preserve composition of the original functor maps. -/
theorem originalConjugatedFunctor_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B K : C} {A' B' K' : D}
    (a : F.obj A ≅ A') (b : F.obj B ≅ B') (k : F.obj K ≅ K')
    (l : A ⟶ B) (m : B ⟶ K) :
    (a.inv ≫ F.map l ≫ b.hom) ≫ (b.inv ≫ F.map m ≫ k.hom) =
      a.inv ≫ F.map (l ≫ m) ≫ k.hom := by
  rw [F.map_comp]
  simp only [Category.assoc, b.hom_inv_id_assoc]

/-- A literal matrix constructs an actual map of native free sheaves on its original affine base. -/
def originalMatrixQuotientSheaf (B : Type u) [CommRing B] {I E : Type u}
    [Finite I] [Fintype E] (M : Matrix I E B) :
    SheafOfModules.free (R := (Spec (.of B)).ringCatSheaf) E ⟶
      SheafOfModules.free (R := (Spec (.of B)).ringCatSheaf) I :=
  (coordinateSheafIsoFree B E).inv ≫
    (tilde.functor (.of B)).map (ModuleCat.ofHom M.mulVecLin) ≫
    (coordinateSheafIsoFree B I).hom

/-- The actual inverse matrix of an actual unit pivot constructs a literal original linear equivalence. -/
def originalInverseMatrixLinearEquiv {B : Type u} [CommRing B] {I : Type u}
    [Fintype I] [DecidableEq I] (P : Matrix I I B) (hP : IsUnit P.det) :
    (I → B) ≃ₗ[B] (I → B) where
  __ := P⁻¹.mulVecLin
  invFun := P.mulVecLin
  left_inv v := by
    change P.mulVec (P⁻¹.mulVec v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  right_inv v := by
    change P⁻¹.mulVec (P.mulVec v) = v
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]

variable (R : Type u) [CommRing R] {ι κ τ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype τ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν)) (f : (ι ⊕ τ) ≃ (ι ⊕ ν))

/-- The actual overlap coefficient ring for these two original pivots. -/
abbrev OriginalOverlapRing := PivotOverlapRing R ι ν
  (pivotIndex (coordinateSelector ι ν) e) (pivotIndex (coordinateSelector ι ν) f)

/-- The first original coefficient-restricted matrix constructs its actual native sheaf map. -/
def originalOverlapLeftQuotient :
    SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) (ι ⊕ ν) ⟶
      SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) ι :=
  originalMatrixQuotientSheaf (OriginalOverlapRing R e f)
    (pivotOverlapMatrix R e (pivotIndex (coordinateSelector ι ν) f))

/-- The second original coefficient-restricted matrix constructs its actual native sheaf map. -/
def originalOverlapRightQuotient :
    SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) (ι ⊕ ν) ⟶
      SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) ι :=
  originalMatrixQuotientSheaf (OriginalOverlapRing R e f) (pivotOverlapRightMatrix R e f)

/-- The same actual selected other-pivot block, with no invertibility certificate input. -/
def originalOverlapPivotBlock : Matrix ι ι (OriginalOverlapRing R e f) :=
  selectedMatrix (pivotOverlapMatrix R e (pivotIndex (coordinateSelector ι ν) f)) (f ∘ Sum.inl)

omit [Fintype τ] [DecidableEq τ] in
/-- Its unit determinant is produced from the same literal original projective intersection. -/
theorem originalOverlapPivotBlock_isUnit : IsUnit (originalOverlapPivotBlock R e f).det := by
  have hs : coordinateSelector ι ν (pivotIndex (coordinateSelector ι ν) f) = f ∘ Sum.inl :=
    (coordinateSelector ι ν).apply_symm_apply _
  change IsUnit (columnMinor (pivotOverlapMatrix R e (pivotIndex (coordinateSelector ι ν) f))
    (f ∘ Sum.inl))
  rw [← hs]
  exact pivotOverlapMatrix_pivot_isUnit R e _

/-- The original actual inverse pivot basis change as a native linear equivalence. -/
def originalOverlapLinearEquiv : (ι → OriginalOverlapRing R e f) ≃ₗ[OriginalOverlapRing R e f]
    (ι → OriginalOverlapRing R e f) :=
  originalInverseMatrixLinearEquiv (originalOverlapPivotBlock R e f)
    (originalOverlapPivotBlock_isUnit R e f)

/-- An actual native target sheaf isomorphism over the same literal original overlap base. -/
def originalOverlapTargetSheafIso :
    SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) ι ≅
      SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) ι :=
  (coordinateSheafIsoFree (OriginalOverlapRing R e f) ι).symm ≪≫
    (tilde.functor (.of (OriginalOverlapRing R e f))).mapIso
      (originalOverlapLinearEquiv R e f).toModuleIso ≪≫
    coordinateSheafIsoFree (OriginalOverlapRing R e f) ι

set_option maxHeartbeats 1500000 in
/-- The actual original coefficient-restricted quotient maps commute on the whole native sheaves. -/
theorem originalOverlapQuotientSheaf_triangle :
    originalOverlapLeftQuotient R e f ≫ (originalOverlapTargetSheafIso R e f).hom =
      originalOverlapRightQuotient R e f := by
  let B := OriginalOverlapRing R e f
  let L := pivotOverlapMatrix R e (pivotIndex (coordinateSelector ι ν) f)
  let N := pivotOverlapRightMatrix R e f
  have hm : ModuleCat.ofHom L.mulVecLin ≫ (originalOverlapLinearEquiv R e f).toModuleIso.hom =
      ModuleCat.ofHom N.mulVecLin := by
    apply ModuleCat.hom_ext
    change ((originalOverlapPivotBlock R e f)⁻¹.mulVecLin).comp L.mulVecLin = N.mulVecLin
    rw [← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (pivotOverlap_normalize_eq_right R e f)
  let F := tilde.functor (.of B)
  let s := coordinateSheafIsoFree B (ι ⊕ ν)
  let t := coordinateSheafIsoFree B ι
  let u := (originalOverlapLinearEquiv R e f).toModuleIso.hom
  change (s.inv ≫ F.map (ModuleCat.ofHom L.mulVecLin) ≫ t.hom) ≫
    (t.inv ≫ F.map u ≫ t.hom) = s.inv ≫ F.map (ModuleCat.ofHom N.mulVecLin) ≫ t.hom
  calc
    _ = s.inv ≫ F.map (ModuleCat.ofHom L.mulVecLin ≫ u) ≫ t.hom :=
      originalConjugatedFunctor_comp F s t t (ModuleCat.ofHom L.mulVecLin) u
    _ = _ := congrArg (fun h ↦ s.inv ≫ F.map h ≫ t.hom) hm

end Hironaka.Geometry.QuotGrassmann
