import Hironaka.Geometry.QuotGrassmannPivotOverFree
import Hironaka.Geometry.QuotGrassmannAffine
import Hironaka.Geometry.QuotGrassmannPivotContractionCoefficients
import Hironaka.Algebra.PluckerQuotTransitionProjection

/-!
# The SAME actual native original contraction has its original scalar pivot factorization

Every endomorphism is formed from the actual global contraction's original
column and row and its actual original coordinate frame. The whole original
pivot identities are proved using the actual entire original coordinate-ring
isomorphism, never assumed as native scalar equations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- The actual framed original column-row coefficient of the SAME native global contraction. -/
def originalOverContractionEntry (j : Fin (pluckerDimension ι ν + 1))
    (a : ι ⊕ ν) (row : (ι → ι ⊕ ν) × ι) :
    End (SheafOfModules.unit
      ((projectiveModel R ι ν).ringCatSheaf.over (coordinateOpen R ι ν j))) :=
  (SheafOfModules.overFunctor.{u} (projectiveModel R ι ν).ringCatSheaf
    (coordinateOpen R ι ν j)).map
      (SheafOfModules.ιFree a ≫ originalGlobalContraction R ι ν ≫
        Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν) row) ≫
    (originalGlobalCoordinateFrame R ι ν j).hom

variable {ι ν} {κ : Type u} [Fintype κ] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The entire original polynomial-to-actual-native-section ring map on this SAME pivot open. -/
def originalOverPivotScalarMap : ChartRing R ι κ →+*
    Γ(projectiveModel R ι ν,
      coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) :=
  (ProjectiveSpectrum.Proj.awayToSection _
    (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e))).hom.comp
      (pivotPolynomialAwayEquiv R e).toRingHom

/-- The actual original native coefficient is the image of its literal original contraction entry. -/
theorem originalOverContractionEntry_polynomial
    (a : ι ⊕ ν) (row : (ι → ι ⊕ ν) × ι) :
    originalOverUnitCoefficient (projectiveModel R ι ν)
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
      (originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e) a row) =
    originalOverPivotScalarMap R e
      (originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν))
        (pivotUniversalMatrix R e) row a) :=
  originalGlobalContraction_polynomial_coefficient R e a row

/-- The SAME actual native contraction's original pivot block is the whole native identity. -/
theorem originalOverContractionEntry_pivot_block (i h : ι) :
    originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
      (e (Sum.inl h)) (e ∘ Sum.inl, i) = if i = h then 𝟙 _ else 0 := by
  classical
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let φ := originalOverPivotScalarMap R e
  have hp := originalContractionMatrix_pivot_block (Equiv.refl (ι → ι ⊕ ν))
    e (universalMatrix R ι κ)
  have he := congrArg (fun M : Matrix ι ι (ChartRing R ι κ) => φ (M i h)) hp
  change φ (originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν))
    (pivotUniversalMatrix R e) (e ∘ Sum.inl, i) (e (Sum.inl h))) =
      φ ((1 : Matrix ι ι (ChartRing R ι κ)) i h) at he
  have hc := originalOverContractionEntry_polynomial R e (e (Sum.inl h)) (e ∘ Sum.inl, i)
  have hv : originalOverUnitCoefficient X U
      (originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
        (e (Sum.inl h)) (e ∘ Sum.inl, i)) =
      originalOverUnitCoefficient X U (if i = h then 𝟙 _ else 0) := by
    apply hc.trans
    apply he.trans
    by_cases hih : i = h
    · subst h
      rw [if_pos rfl, show (1 : Matrix ι ι (ChartRing R ι κ)) i i = 1 by simp, map_one]
      rfl
    · rw [if_neg hih]
      rw [show (1 : Matrix ι ι (ChartRing R ι κ)) i h = 0 by simp [hih], map_zero, map_zero]
  exact originalOverUnitEnd_ext_one_top X U hv

/-- Every SAME original native contraction entry has its internally proved whole pivot factorization. -/
theorem originalOverContractionEntry_pivot_factor
    (a : ι ⊕ ν) (row : (ι → ι ⊕ ν) × ι) :
    originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e) a row =
      ∑ h : ι,
        originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
          (e (Sum.inl h)) row ≫
        originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
          a (e ∘ Sum.inl, h) := by
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let φ := originalOverPivotScalarMap R e
  let C := originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν)) (pivotUniversalMatrix R e)
  have hp := originalContractionMatrix_pivot_factor (Equiv.refl (ι → ι ⊕ ν))
    e (universalMatrix R ι κ)
  have he := congrArg (fun M : Matrix ((ι → ι ⊕ ν) × ι) (ι ⊕ ν) (ChartRing R ι κ) =>
    φ (M row a)) hp
  change φ (C row a) = φ (∑ h : ι, C row (e (Sum.inl h)) * C (e ∘ Sum.inl, h) a) at he
  rw [map_sum] at he
  simp only [map_mul] at he
  have hv : originalOverUnitCoefficient X U
      (originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e) a row) =
      originalOverUnitCoefficient X U
        (∑ h : ι,
          originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
            (e (Sum.inl h)) row ≫
          originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e)
            a (e ∘ Sum.inl, h)) := by
    rw [map_sum]
    simp_rw [originalOverUnitEnd_comp_one_top]
    rw [originalOverContractionEntry_polynomial]
    calc
      _ = ∑ h : ι, φ (C row (e (Sum.inl h))) * φ (C (e ∘ Sum.inl, h) a) := he
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _
        exact congrArg₂ (fun b c : Γ(X, U) => b * c)
          (originalOverContractionEntry_polynomial R e (e (Sum.inl h)) row).symm
          (originalOverContractionEntry_polynomial R e a (e ∘ Sum.inl, h)).symm
  exact originalOverUnitEnd_ext_one_top X U hv

end Hironaka.Geometry.QuotGrassmann
