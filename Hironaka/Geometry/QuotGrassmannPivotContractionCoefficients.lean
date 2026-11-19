import Hironaka.Geometry.QuotGrassmannPivotTwistingFrame
import Hironaka.Geometry.QuotGrassmannPivotGlobalContraction
import Hironaka.Algebra.PluckerQuotTransitionContraction

/-!
# Actual global original contraction coefficients in the original native frame

The source is the SAME original global contraction. Its actual over-site
restriction and actual native twisting frame produce the original native
projective-coordinate ratios; no coefficient equality is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Twisting ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual global native coordinate morphism, restricted and framed, has its literal ratio. -/
theorem originalNativeCoordinateMorphism_coefficient
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (a b : 𝒜 1) :
    (((SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf (Proj.basicOpen 𝒜 a.val)).map
        (originalCoordinateGlobalMorphism 𝒜 b) ≫
      (projectiveTwistingCoordinateFrame 𝒜 1 a).hom).val.app
        (.op (Over.mk (𝟙 (Proj.basicOpen 𝒜 a.val)))))
          (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 a.val)) =
    (ProjectiveSpectrum.Proj.awayToSection 𝒜 a.val)
      (HomogeneousLocalization.Away.mk 𝒜 a.property 1 b.val b.property) := by
  let T := projectiveTwistingSheaf 𝒜 1
  let U := Proj.basicOpen 𝒜 a.val
  have hb : (originalCoordinateGlobalMorphism 𝒜 b).val.app (.op U)
      (1 : Γ(Proj 𝒜, U)) = projectiveTwistingCoordinateSection 𝒜 1 b U :=
    congrArg (fun s : T.sections => s.val (.op U))
      (T.unitHomEquiv.apply_symm_apply (originalCoordinateGlobalSection 𝒜 b))
  exact (congrArg (fun t => (projectiveTwistingCoordinateFrame 𝒜 1 a).hom.val.app
    (.op (Over.mk (𝟙 U))) t) hb).trans (originalNativeCoordinateFrame_ratio 𝒜 a b)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (ι κ : Type u)
  [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The actual native original coordinate frame on the same original model's same original open. -/
def originalGlobalCoordinateFrame (j : Fin (pluckerDimension ι κ + 1)) :
    (originalPositiveTwisting R ι κ).over (coordinateOpen R ι κ j) ≅
      SheafOfModules.unit
        ((projectiveModel R ι κ).ringCatSheaf.over (coordinateOpen R ι κ j)) :=
  projectiveTwistingCoordinateFrame _ 1
    ⟨coordinateClass R ι κ j, coordinateClass_homogeneous R ι κ j⟩

/-- The actual SAME-model global contraction has its literal original projective ratio coefficient. -/
theorem originalGlobalContraction_original_coefficient
    (j : Fin (pluckerDimension ι κ + 1))
    (a : ι ⊕ κ) (s : (ι → ι ⊕ κ) × ι) :
    (((SheafOfModules.overFunctor (projectiveModel R ι κ).ringCatSheaf
        (coordinateOpen R ι κ j)).map
      (SheafOfModules.ιFree a ≫ originalGlobalContraction R ι κ ≫
        Pi.π (fun (_ : (ι → ι ⊕ κ) × ι) => originalPositiveTwisting R ι κ) s) ≫
      (originalGlobalCoordinateFrame R ι κ j).hom).val.app
        (.op (Over.mk (𝟙 (coordinateOpen R ι κ j)))))
          (1 : Γ(projectiveModel R ι κ, coordinateOpen R ι κ j)) =
      (ProjectiveSpectrum.Proj.awayToSection _ (coordinateClass R ι κ j))
        (nativePivotRatio R ι κ j (originalContractionCoordinate ι κ s a)) := by
  let F := SheafOfModules.overFunctor (projectiveModel R ι κ).ringCatSheaf
    (coordinateOpen R ι κ j)
  have hentry := congrArg (fun h => F.map h ≫ (originalGlobalCoordinateFrame R ι κ j).hom)
    (originalGlobalContraction_entry R ι κ a s)
  have hev := congrArg (fun h => h.val.app
    (.op (Over.mk (𝟙 (coordinateOpen R ι κ j))))
      (1 : Γ(projectiveModel R ι κ, coordinateOpen R ι κ j))) hentry
  exact hev.trans (originalNativeCoordinateMorphism_coefficient _
    ⟨coordinateClass R ι κ j, coordinateClass_homogeneous R ι κ j⟩
    ⟨coordinateClass R ι κ (originalContractionCoordinate ι κ s a),
      coordinateClass_homogeneous R ι κ (originalContractionCoordinate ι κ s a)⟩)

variable {ι κ} {ν : Type u} [Fintype ν] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The SAME actual global contraction coefficient is the image of its exact original
normalized polynomial contraction entry under the SAME entire original pivot ring iso. -/
theorem originalGlobalContraction_polynomial_coefficient
    (a : ι ⊕ ν) (s : (ι → ι ⊕ ν) × ι) :
    (((SheafOfModules.overFunctor (projectiveModel R ι ν).ringCatSheaf
        (coordinateOpen R ι ν (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e))).map
      (SheafOfModules.ιFree a ≫ originalGlobalContraction R ι ν ≫
        Pi.π (fun (_ : (ι → ι ⊕ ν) × ι) => originalPositiveTwisting R ι ν) s) ≫
      (originalGlobalCoordinateFrame R ι ν
        (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e)).hom).val.app
        (.op (Over.mk (𝟙 (coordinateOpen R ι ν
          (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e))))))
          (1 : Γ(projectiveModel R ι ν, coordinateOpen R ι ν
            (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e))) =
      (ProjectiveSpectrum.Proj.awayToSection _ (coordinateClass R ι ν
        (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e)))
        (pivotPolynomialAwayEquiv R e
          (Algebra.PluckerQuot.originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν))
            (Algebra.PluckerQuot.pivotUniversalMatrix R e) s a)) := by
  have hr := (pivotPolynomialAwayEquiv_minor R e (Function.update s.1 s.2 a)).trans
    (pivotRatioHom_coordinate R ι ν _ _)
  exact (originalGlobalContraction_original_coefficient R ι ν
    (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e) a s).trans
      (congrArg (fun t => (ProjectiveSpectrum.Proj.awayToSection _
        (coordinateClass R ι ν (Algebra.PluckerQuot.pivotIndex (coordinateSelector ι ν) e))) t)
          hr.symm)

end Hironaka.Geometry.QuotGrassmann
