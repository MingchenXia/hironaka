import Hironaka.Geometry.QuotGrassmannPivotOverImage
import Hironaka.Geometry.QuotGrassmannPivotOverScalars

/-!
# Actual original local pivot maps extracted from the SAME global contraction

The actual r, q=C r, s, and J=s C are native sheaf maps built from the original
rows and columns of the SAME original global contraction and its original frame.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- The actual original source restricted to the same native original coordinate over-site. -/
abbrev OriginalOverSource (j : Fin (pluckerDimension ι ν + 1)) :=
  (SheafOfModules.free (R := (projectiveModel R ι ν).ringCatSheaf) (ι ⊕ ν)).over
    (coordinateOpen R ι ν j)

/-- The actual original target restricted to the same native original coordinate over-site. -/
abbrev OriginalOverTarget (j : Fin (pluckerDimension ι ν + 1)) :=
  (originalGlobalContractionTarget R ι ν).over (coordinateOpen R ι ν j)

/-- The native free sheaf on the SAME original quotient row index. -/
abbrev OriginalOverFree (j : Fin (pluckerDimension ι ν + 1)) :=
  SheafOfModules.free
    (R := (projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j)) ι

/-- Restriction of the SAME actual original global contraction. -/
def originalOverContraction (j : Fin (pluckerDimension ι ν + 1)) :
    OriginalOverSource R ι ν j ⟶ OriginalOverTarget R ι ν j :=
  (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
    (coordinateOpen R ι ν j)).map (originalGlobalContraction R ι ν)

/-- The actual original selected pivot rows and frame construct the native local retraction. -/
def originalOverPivotRetraction (j : Fin (pluckerDimension ι ν + 1)) :
    OriginalOverTarget R ι ν j ⟶ OriginalOverFree R ι ν j :=
  ∑ i : ι,
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν j)).map
        (Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν)
          (coordinateSelector ι ν j, i)) ≫
    (originalGlobalCoordinateFrame R ι ν j).hom ≫ SheafOfModules.ιFree i

/-- The actual local quotient is extracted from the SAME original global contraction. -/
def originalOverPivotQuotient (j : Fin (pluckerDimension ι ν + 1)) :
    OriginalOverSource R ι ν j ⟶ OriginalOverFree R ι ν j :=
  originalOverContraction R ι ν j ≫ originalOverPivotRetraction R ι ν j

/-- The original pivot columns produce an actual native section into the actual original source. -/
def originalOverPivotSection (j : Fin (pluckerDimension ι ν + 1)) :
    OriginalOverFree R ι ν j ⟶ OriginalOverSource R ι ν j :=
  Sigma.desc fun i =>
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν j)).map (SheafOfModules.ιFree (coordinateSelector ι ν j i))

/-- The native local factor is extracted from the SAME original global contraction. -/
def originalOverPivotFactor (j : Fin (pluckerDimension ι ν + 1)) :
    OriginalOverFree R ι ν j ⟶ OriginalOverTarget R ι ν j :=
  originalOverPivotSection R ι ν j ≫ originalOverContraction R ι ν j

/-- The actual local retraction preserves its exact original selected native target projections. -/
theorem originalOverPivotRetraction_projection (j : Fin (pluckerDimension ι ν + 1)) (i : ι) :
    originalOverPivotRetraction R ι ν j ≫
      originalOverFreeProjection (projectiveModel R ι ν) (coordinateOpen R ι ν j) i =
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν j)).map
        (Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν)
          (coordinateSelector ι ν j, i)) ≫
      (originalGlobalCoordinateFrame R ι ν j).hom := by
  classical
  simp [originalOverPivotRetraction, Preadditive.sum_comp, Category.assoc,
    originalOverFreeProjection_inclusion, CategoryTheory.comp_ite]

/-- The original local section preserves the SAME actual original pivot basis columns. -/
theorem originalOverPivotSection_inclusion (j : Fin (pluckerDimension ι ν + 1)) (i : ι) :
    SheafOfModules.ιFree i ≫ originalOverPivotSection R ι ν j =
      (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
        (coordinateOpen R ι ν j)).map (SheafOfModules.ιFree (coordinateSelector ι ν j i)) :=
  Sigma.ι_desc _ i

/-- The actual local quotient has the exact original native selected-row coefficients. -/
theorem originalOverPivotQuotient_coefficient (j : Fin (pluckerDimension ι ν + 1))
    (a : ι ⊕ ν) (i : ι) :
    (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
      (coordinateOpen R ι ν j)).map (SheafOfModules.ιFree a) ≫
      originalOverPivotQuotient R ι ν j ≫
        originalOverFreeProjection (projectiveModel R ι ν) (coordinateOpen R ι ν j) i =
    originalOverContractionEntry R ι ν j a (coordinateSelector ι ν j, i) := by
  simp only [originalOverPivotQuotient, Category.assoc, originalOverPivotRetraction_projection]
  simp only [originalOverContractionEntry, originalOverContraction, Functor.map_comp,
    Category.assoc]

/-- The actual local factor has the exact original native selected-column coefficients. -/
theorem originalOverPivotFactor_coefficient (j : Fin (pluckerDimension ι ν + 1))
    (i : ι) (row : (ι → ι ⊕ ν) × ι) :
    SheafOfModules.ιFree i ≫ originalOverPivotFactor R ι ν j ≫
      (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
        (coordinateOpen R ι ν j)).map
          (Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν) row) ≫
        (originalGlobalCoordinateFrame R ι ν j).hom =
      originalOverContractionEntry R ι ν j (coordinateSelector ι ν j i) row := by
  simp only [originalOverPivotFactor, ← Category.assoc,
    originalOverPivotSection_inclusion]
  simp only [originalOverContractionEntry, originalOverContraction, Functor.map_comp,
    Category.assoc]

end Hironaka.Geometry.QuotGrassmann
