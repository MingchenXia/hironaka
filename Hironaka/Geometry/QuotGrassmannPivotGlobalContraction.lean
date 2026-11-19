import Hironaka.Geometry.QuotGrassmannPivotTwisting
import Hironaka.Geometry.QuotGrassmannPivotOverlapRatio
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The actual original global contraction and its native abelian image

Every coordinate is from the same original graded quotient. The target is an
actual finite product of the actual positive twisting sheaf. The image quotient
is constructed internally; local freeness is a subsequent theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open ProjectiveIdeal Twisting

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ] [DecidableEq ι]

private theorem originalCoproductProductEntry
    {C : Type*} [Category C] {E S : Type u} (L T : C)
    [HasCoproduct (fun (_ : E) => L)] [HasProduct (fun (_ : S) => T)]
    (p : E → S → (L ⟶ T)) (a : E) (s : S) :
    Sigma.ι (fun (_ : E) => L) a ≫
      Sigma.desc (fun b => Pi.lift (p b)) ≫ Pi.π (fun (_ : S) => T) s = p a s := by
  rw [Sigma.ι_desc_assoc, Pi.lift_π]

/-- The actual original degree-one homogeneous-fraction sheaf on the same model. -/
def originalPositiveTwisting : (projectiveModel R ι κ).Modules :=
  projectiveTwistingSheaf
    (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι κ))
      (pluckerIdeal R ι κ).toIdeal) 1

/-- An actual original projective coordinate as a native unit-to-twisting morphism. -/
def originalGlobalCoordinate (j : Fin (pluckerDimension ι κ + 1)) :
    SheafOfModules.unit (projectiveModel R ι κ).ringCatSheaf ⟶
      originalPositiveTwisting R ι κ :=
  originalCoordinateGlobalMorphism _
    ⟨coordinateClass R ι κ j, coordinateClass_homogeneous R ι κ j⟩

/-- The actual finite product indexed by all original selector rows. -/
def originalGlobalContractionTarget : (projectiveModel R ι κ).Modules :=
  ∏ᶜ fun (_ : (ι → ι ⊕ κ) × ι) => originalPositiveTwisting R ι κ

/-- The original replacement selector determines its actual projective coordinate. -/
def originalContractionCoordinate (s : (ι → ι ⊕ κ) × ι) (a : ι ⊕ κ) :
    Fin (pluckerDimension ι κ + 1) :=
  (coordinateSelector ι κ).symm (Function.update s.1 s.2 a)

/-- Actual product lift of the original global replacement coordinates of one free column. -/
def originalGlobalContractionColumn (a : ι ⊕ κ) :
    SheafOfModules.unit (projectiveModel R ι κ).ringCatSheaf ⟶
      originalGlobalContractionTarget R ι κ :=
  Pi.lift fun s => originalGlobalCoordinate R ι κ (originalContractionCoordinate ι κ s a)

/-- The internally constructed native global original-coordinate contraction. -/
def originalGlobalContraction :
    SheafOfModules.free (R := (projectiveModel R ι κ).ringCatSheaf) (ι ⊕ κ) ⟶
      originalGlobalContractionTarget R ι κ :=
  Sigma.desc (originalGlobalContractionColumn R ι κ)

/-- Every entry is the literal original coordinate morphism, as a whole native sheaf map. -/
theorem originalGlobalContraction_entry (a : ι ⊕ κ) (s : (ι → ι ⊕ κ) × ι) :
    SheafOfModules.ιFree a ≫ originalGlobalContraction R ι κ ≫
      Pi.π (fun (_ : (ι → ι ⊕ κ) × ι) => originalPositiveTwisting R ι κ) s =
        originalGlobalCoordinate R ι κ (originalContractionCoordinate ι κ s a) := by
  exact originalCoproductProductEntry
    (SheafOfModules.unit (projectiveModel R ι κ).ringCatSheaf)
    (originalPositiveTwisting R ι κ)
    (fun a s => originalGlobalCoordinate R ι κ (originalContractionCoordinate ι κ s a)) a s

/-- The actual native abelian image object of the constructed original contraction. -/
def originalGlobalImageQuotient : (projectiveModel R ι κ).Modules :=
  Abelian.image (originalGlobalContraction R ι κ)

/-- The actual original free-source quotient to the constructed global image. -/
def originalGlobalQuotient :
    SheafOfModules.free (R := (projectiveModel R ι κ).ringCatSheaf) (ι ⊕ κ) ⟶
      originalGlobalImageQuotient R ι κ :=
  Abelian.factorThruImage (originalGlobalContraction R ι κ)

instance originalGlobalQuotient_epi : Epi (originalGlobalQuotient R ι κ) :=
  inferInstanceAs (Epi (Abelian.factorThruImage (originalGlobalContraction R ι κ)))

/-- The native kernel-of-cokernel inclusion of the same actual image. -/
def originalGlobalImageInclusion : originalGlobalImageQuotient R ι κ ⟶
    originalGlobalContractionTarget R ι κ :=
  Abelian.image.ι (originalGlobalContraction R ι κ)

instance originalGlobalImageInclusion_mono : Mono (originalGlobalImageInclusion R ι κ) :=
  inferInstanceAs (Mono (Abelian.image.ι (originalGlobalContraction R ι κ)))

/-- The actual global image quotient factors the literal original contraction. -/
theorem originalGlobalQuotient_triangle :
    originalGlobalQuotient R ι κ ≫ originalGlobalImageInclusion R ι κ =
      originalGlobalContraction R ι κ :=
  Abelian.image.fac (originalGlobalContraction R ι κ)

/-- Every original coordinate is preserved by the actual global image quotient triangle. -/
theorem originalGlobalQuotient_entry (a : ι ⊕ κ) (s : (ι → ι ⊕ κ) × ι) :
    SheafOfModules.ιFree a ≫ originalGlobalQuotient R ι κ ≫
      originalGlobalImageInclusion R ι κ ≫
        Pi.π (fun (_ : (ι → ι ⊕ κ) × ι) => originalPositiveTwisting R ι κ) s =
      originalGlobalCoordinate R ι κ (originalContractionCoordinate ι κ s a) := by
  rw [← Category.assoc (originalGlobalQuotient R ι κ), originalGlobalQuotient_triangle]
  exact originalGlobalContraction_entry R ι κ a s

end Hironaka.Geometry.QuotGrassmann
