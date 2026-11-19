import Hironaka.Geometry.QuotGrassmannPivotMatrixPullback
import Hironaka.Geometry.QuotGrassmannPivotOverlapMorphisms
import Hironaka.Algebra.PluckerQuotTransitionLinear

/-!
# True native pullbacks of the originally frozen normalized universal quotients

The original quotient maps themselves are retained. Their actual native
pullbacks use the actual two original overlap coefficient morphisms. The
actual original free-coordinate splittings give the same original common
free source, and the actual native target isomorphism intertwines these
true original pullbacks in their native free frames.
-/

noncomputable section

open scoped Classical
open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Original free-coordinate reindexing preserves the entire actual native matrix map. -/
theorem originalMatrixQuotientSheaf_reindex (B : Type u) [CommRing B]
    {I E T : Type u} [Fintype I] [Fintype E] [Fintype T]
    [DecidableEq I] [DecidableEq E] [DecidableEq T] (e : T → E) (M : Matrix I E B) :
    SheafOfModules.freeMap e ≫ originalMatrixQuotientSheaf B M =
      originalMatrixQuotientSheaf B (M.submatrix id e) := by
  apply originalFreeHomCoefficient_injective (Spec (.of B))
  intro j i
  have hc : originalFreeHomCoefficient
      (SheafOfModules.freeMap e ≫ originalMatrixQuotientSheaf B M) j i =
      originalFreeHomCoefficient (originalMatrixQuotientSheaf B M) (e j) i := by
    simp only [originalFreeHomCoefficient, ← Category.assoc, SheafOfModules.ιFree_freeMap]
  exact hc.trans ((originalMatrixQuotientSheaf_coefficient B M i (e j)).trans
    (originalMatrixQuotientSheaf_coefficient B (M.submatrix id e) i j).symm)

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The originally frozen normalized universal quotient is exactly its original full matrix sheaf map. -/
theorem originalUniversalQuotient_eq_matrix :
    universalQuotient R ι κ = originalMatrixQuotientSheaf (ChartRing R ι κ)
      (normalizedMatrix (universalMatrix R ι κ)) := by
  let B := ChartRing R ι κ
  let F := tilde.functor (.of B)
  let s := coordinateSheafIsoFree B (ι ⊕ κ)
  let t := coordinateSheafIsoFree B ι
  have hm : ModuleCat.ofHom (matrixQuotient (universalMatrix R ι κ)) =
      ModuleCat.ofHom (normalizedMatrix (universalMatrix R ι κ)).mulVecLin :=
    congrArg (fun l : ((ι ⊕ κ) → B) →ₗ[B] (ι → B) ↦ ModuleCat.ofHom l)
      (normalizedMatrix_mulVecLin (universalMatrix R ι κ)).symm
  exact congrArg (fun h ↦ s.inv ≫ F.map h ≫ t.hom) hm

/-- The true native pullback of the originally frozen quotient is the same original coefficient matrix map. -/
theorem originalUniversalQuotient_pullback {H : Type u} [CommRing H]
    (φ : ChartRing R ι κ →+* H) :
    originalPullbackFreeHom (Spec.map (CommRingCat.ofHom φ)) (universalQuotient R ι κ) =
      originalMatrixQuotientSheaf H ((normalizedMatrix (universalMatrix R ι κ)).map φ) :=
  (congrArg (originalPullbackFreeHom (Spec.map (CommRingCat.ofHom φ)))
    (originalUniversalQuotient_eq_matrix R ι κ)).trans
      (originalMatrixQuotientSheaf_pullback φ _)

/-- The true original quotient pullback retains its same original common free source under its actual splitting. -/
theorem originalUniversalQuotient_pullback_reindex {H T : Type u} [CommRing H] [Fintype T]
    [DecidableEq T] (e : (ι ⊕ κ) ≃ T) (φ : ChartRing R ι κ →+* H) :
    SheafOfModules.freeMap e.symm ≫
      originalPullbackFreeHom (Spec.map (CommRingCat.ofHom φ)) (universalQuotient R ι κ) =
    originalMatrixQuotientSheaf H ((splitNormalizedMatrix e (universalMatrix R ι κ)).map φ) :=
  (congrArg (fun q ↦ SheafOfModules.freeMap e.symm ≫ q)
    (originalUniversalQuotient_pullback R ι κ φ)).trans
      (originalMatrixQuotientSheaf_reindex H e.symm _)

variable {ι κ} {τ ν : Type u} [Fintype τ] [Fintype ν] [DecidableEq τ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν)) (f : (ι ⊕ τ) ≃ (ι ⊕ ν))

omit [Fintype τ] [DecidableEq τ] in
/-- The actual first native overlap quotient is the true pullback of the very originally frozen quotient. -/
theorem originalOverlapLeftQuotient_truePullback :
    SheafOfModules.freeMap e.symm ≫
      originalPullbackFreeHom (originalOverlapLeftMorphism R e f) (universalQuotient R ι κ) =
    originalOverlapLeftQuotient R e f :=
  originalUniversalQuotient_pullback_reindex R ι κ e
    (pivotOverlapPolynomialMap R e (pivotIndex (coordinateSelector ι ν) f))

omit [Fintype κ] [DecidableEq κ] in
/-- The actual second native overlap quotient is the true pullback of the very originally frozen quotient. -/
theorem originalOverlapRightQuotient_truePullback :
    SheafOfModules.freeMap f.symm ≫
      originalPullbackFreeHom (originalOverlapRightMorphism R e f) (universalQuotient R ι τ) =
    originalOverlapRightQuotient R e f :=
  originalUniversalQuotient_pullback_reindex R ι τ f (pivotOverlapRightPolynomialMap R e f)

/-- The actual same target sheaf isomorphism intertwines BOTH true native pullbacks of the original
frozen quotient maps, preserving the same original free source in their actual native free frames. -/
theorem originalOverlapQuotientSheaf_truePullback_triangle :
    (SheafOfModules.freeMap e.symm ≫
      originalPullbackFreeHom (originalOverlapLeftMorphism R e f) (universalQuotient R ι κ)) ≫
        (originalOverlapTargetSheafIso R e f).hom =
    SheafOfModules.freeMap f.symm ≫
      originalPullbackFreeHom (originalOverlapRightMorphism R e f) (universalQuotient R ι τ) :=
  (congrArg (fun q ↦ q ≫ (originalOverlapTargetSheafIso R e f).hom)
    (originalOverlapLeftQuotient_truePullback R e f)).trans
      ((originalOverlapQuotientSheaf_triangle R e f).trans
        (originalOverlapRightQuotient_truePullback R e f).symm)

/-- The actual target isomorphism between the true native pullback objects themselves. -/
def originalOverlapTrueTargetIso :
    (Scheme.Modules.pullback (originalOverlapLeftMorphism R e f)).obj
      (SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι) ≅
    (Scheme.Modules.pullback (originalOverlapRightMorphism R e f)).obj
      (SheafOfModules.free (R := (affineChart R ι τ).ringCatSheaf) ι) :=
  originalPullbackFreeIso (originalOverlapLeftMorphism R e f) ι ≪≫
    originalOverlapTargetSheafIso R e f ≪≫
      (originalPullbackFreeIso (originalOverlapRightMorphism R e f) ι).symm

/-- The first original quotient's true native pullback, retaining its actual unframed target object. -/
def originalOverlapTrueLeftQuotient :
    SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) (ι ⊕ ν) ⟶
    (Scheme.Modules.pullback (originalOverlapLeftMorphism R e f)).obj
      (SheafOfModules.free (R := (affineChart R ι κ).ringCatSheaf) ι) :=
  SheafOfModules.freeMap e.symm ≫
    (originalPullbackFreeIso (originalOverlapLeftMorphism R e f) (ι ⊕ κ)).inv ≫
      (Scheme.Modules.pullback (originalOverlapLeftMorphism R e f)).map (universalQuotient R ι κ)

/-- The second original quotient's true native pullback, retaining its actual unframed target object. -/
def originalOverlapTrueRightQuotient :
    SheafOfModules.free (R := (Spec (.of (OriginalOverlapRing R e f))).ringCatSheaf) (ι ⊕ ν) ⟶
    (Scheme.Modules.pullback (originalOverlapRightMorphism R e f)).obj
      (SheafOfModules.free (R := (affineChart R ι τ).ringCatSheaf) ι) :=
  SheafOfModules.freeMap f.symm ≫
    (originalPullbackFreeIso (originalOverlapRightMorphism R e f) (ι ⊕ τ)).inv ≫
      (Scheme.Modules.pullback (originalOverlapRightMorphism R e f)).map (universalQuotient R ι τ)

/-- Actual frame isomorphisms transport the precise original quotient triangle to the original target objects. -/
theorem originalFromFreeFrames_triangle {C : Type*} [Category C] {S A B T U : C}
    (q : S ⟶ A) (r : S ⟶ B) (a : A ≅ T) (b : B ≅ U) (t : T ≅ U)
    (h : (q ≫ a.hom) ≫ t.hom = r ≫ b.hom) : q ≫ (a ≪≫ t ≪≫ b.symm).hom = r := by
  apply (cancel_mono b.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, b.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using h

set_option maxHeartbeats 1500000 in
/-- The same actual isomorphism intertwines BOTH true native original quotient pullbacks, on their
actual unframed target objects and the same original common free source. -/
theorem originalOverlapTrueQuotient_triangle :
    originalOverlapTrueLeftQuotient R e f ≫ (originalOverlapTrueTargetIso R e f).hom =
      originalOverlapTrueRightQuotient R e f := by
  apply originalFromFreeFrames_triangle
    (originalOverlapTrueLeftQuotient R e f) (originalOverlapTrueRightQuotient R e f)
    (originalPullbackFreeIso (originalOverlapLeftMorphism R e f) ι)
    (originalPullbackFreeIso (originalOverlapRightMorphism R e f) ι)
    (originalOverlapTargetSheafIso R e f)
  simpa only [originalOverlapTrueLeftQuotient, originalOverlapTrueRightQuotient,
    originalPullbackFreeHom, Category.assoc] using
      originalOverlapQuotientSheaf_truePullback_triangle R e f

end Hironaka.Geometry.QuotGrassmann
