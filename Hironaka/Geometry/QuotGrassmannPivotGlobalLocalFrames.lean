import Hironaka.Geometry.QuotGrassmannPivotOverSplit

/-!
# Actual original free local frames of the SAME global native image quotient

The global image is unchanged. Its actual restricted source quotient and local
free target isomorphism are derived from the original internally produced split
factorization and actual over-site image comparison, not supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The actual local image factorization uses the internally produced original split maps. -/
def originalOverPivotImageFactorisation :
    StrongEpiMonoFactorisation
      (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)) := by
  letI := originalOverPivotQuotient_isSplitEpi R e
  letI := originalOverPivotFactor_isSplitMono R e
  exact {
    I := OriginalOverFree R ι ν (pivotIndex (coordinateSelector ι ν) e)
    e := originalOverPivotQuotient R ι ν _
    m := originalOverPivotFactor R ι ν _
    fac := originalOverPivotQuotient_factor R e }

/-- The SAME global original image has an actual native free frame on this original pivot. -/
def originalGlobalImagePivotFrame :
    (originalGlobalImageQuotient R ι ν).over
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) ≅
        OriginalOverFree R ι ν (pivotIndex (coordinateSelector ι ν) e) :=
  originalOverImageIso (projectiveModel R ι ν)
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
    (originalGlobalContraction R ι ν) ≪≫
      IsImage.isoExt
        (Image.isImage (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)))
        (originalOverPivotImageFactorisation R e).toMonoIsImage

/-- The actual SAME global quotient map is recovered as the actual original local quotient. -/
theorem originalGlobalImagePivotFrame_quotient :
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))).map
        (originalGlobalQuotient R ι ν) ≫
      (originalGlobalImagePivotFrame R e).hom =
        originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e) := by
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let c := originalOverImageIso X U (originalGlobalContraction R ι ν)
  let d := IsImage.isoExt
    (Image.isImage (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)))
    (originalOverPivotImageFactorisation R e).toMonoIsImage
  have hc := originalOverImageIso_factor X U (originalGlobalContraction R ι ν)
  have hd := IsImage.e_isoExt_hom
    (Image.isImage (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)))
    (originalOverPivotImageFactorisation R e).toMonoIsImage
  exact (Category.assoc (F.map (originalGlobalQuotient R ι ν)) c.hom d.hom).symm.trans
    ((congrArg (fun h => h ≫ d.hom) hc).trans hd)

/-- The actual SAME global image inclusion is recovered as the actual original local split factor. -/
theorem originalGlobalImagePivotFrame_inclusion :
    (originalGlobalImagePivotFrame R e).hom ≫
      originalOverPivotFactor R ι ν (pivotIndex (coordinateSelector ι ν) e) =
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))).map
        (originalGlobalImageInclusion R ι ν) := by
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let c := originalOverImageIso X U (originalGlobalContraction R ι ν)
  let d := IsImage.isoExt
    (Image.isImage (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)))
    (originalOverPivotImageFactorisation R e).toMonoIsImage
  have hd : d.hom ≫ originalOverPivotFactor R ι ν (pivotIndex (coordinateSelector ι ν) e) =
      image.ι (originalOverContraction R ι ν (pivotIndex (coordinateSelector ι ν) e)) :=
    IsImage.isoExt_hom_m _ _
  exact (Category.assoc c.hom d.hom _).trans
    ((congrArg (fun h => c.hom ≫ h) hd).trans
      (originalOverImageIso_inclusion X U (originalGlobalContraction R ι ν)))

variable (ι ν)

/-- Every actual original injective pivot has its actual native global-image free frame. -/
def actualOriginalGlobalImageFrame (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    (originalGlobalImageQuotient R ι ν).over (coordinateOpen R ι ν j) ≅
      SheafOfModules.free
        (R := (projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j)) ι := by
  classical
  let e := actualPivotSplitting ι ν j hj
  let P (t : Fin (pluckerDimension ι ν + 1)) :=
    (originalGlobalImageQuotient R ι ν).over (coordinateOpen R ι ν t) ≅
      SheafOfModules.free
        (R := (projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν t)) ι
  exact Eq.mp (congrArg P (actualPivotSplitting_pivotIndex ι ν j hj))
    (originalGlobalImagePivotFrame R e)

/-- The actual original global image has native generating data on its original pivot cover. -/
def originalGlobalImageLocalGeneratorsData :
    (originalGlobalImageQuotient R ι ν).LocalGeneratorsData where
  I := {j : Fin (pluckerDimension ι ν + 1) // Function.Injective (coordinateSelector ι ν j)}
  X j := coordinateOpen R ι ν j.val
  coversTop := by
    rw [_root_.Opens.coversTop_iff]
    exact iSup_pivotOpen_eq_top R ι ν
  generators j := (SheafOfModules.free.generatingSections
    (R := (projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j.val)) ι).ofEpi
      (actualOriginalGlobalImageFrame R ι ν j.val j.property).inv

/-- Every actual original generating index is the SAME original finite row index. -/
theorem originalGlobalImageLocalGeneratorsData_index
    (j : (originalGlobalImageLocalGeneratorsData R ι ν).I) :
    ((originalGlobalImageLocalGeneratorsData R ι ν).generators j).I = ι := rfl

/-- The original actual local generating maps are native isomorphisms, produced from actual image frames. -/
instance originalGlobalImageLocalGeneratorsData_isLocallyFreeData :
    (originalGlobalImageLocalGeneratorsData R ι ν).IsLocallyFreeData := by
  constructor
  intro j
  change IsIso ((SheafOfModules.free.generatingSections
    (R := (projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j.val)) ι).ofEpi
      (actualOriginalGlobalImageFrame R ι ν j.val j.property).inv).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  exact (congrArg IsIso (Category.id_comp
    (actualOriginalGlobalImageFrame R ι ν j.val j.property).inv)).mpr inferInstance

/-- The SAME actual original global image quotient is natively locally free. -/
instance originalGlobalImageQuotient_isLocallyFree :
    (originalGlobalImageQuotient R ι ν).IsLocallyFree :=
  (originalGlobalImageLocalGeneratorsData R ι ν).isLocallyFree

/-- The SAME actual original local generating data is finite, with the SAME actual original row indices. -/
instance originalGlobalImageLocalGeneratorsData_isFiniteType :
    (originalGlobalImageLocalGeneratorsData R ι ν).IsFiniteType where
  isFiniteType j := ⟨by change Finite ι; infer_instance⟩

/-- The SAME actual original global image quotient has native finite type. -/
instance originalGlobalImageQuotient_isFiniteType :
    (originalGlobalImageQuotient R ι ν).IsFiniteType := by
  constructor
  refine ⟨(originalGlobalImageLocalGeneratorsData R ι ν).shrink, ?_⟩
  constructor
  intro j
  exact ⟨by change Finite ι; infer_instance⟩

end Hironaka.Geometry.QuotGrassmann
