import Hironaka.Geometry.ProjectiveSecantEquation
import Hironaka.Geometry.ProjectiveProjectionPointFinite

/-!
# An internally constructed actual nonempty secant-centre open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection
open Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual zero homogeneous prime in the original ambient polynomial domain. -/
def ambientGenericPoint : ProjectiveSpectrum (ProjectiveGrading k (n + 1)) where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa using (inferInstance : (⊥ : Ideal (MvPolynomial (Fin (n + 2)) k)).IsPrime)
  not_irrelevant_le h := by
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 2))))
    exact MvPolynomial.X_ne_zero (0 : Fin (n + 2)) hX

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]
  (hdim : topologicalKrullDim X < n)

/-- The actual parameter open comes from the original geometric dimension, rather than a caller's general-position certificate. -/
def secantCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  Proj.basicOpen (ProjectiveGrading k (n + 1))
    (MvPolynomial.rename Fin.succ (secantEquation k n i hdim).val.2)

/-- Genuine native scheme nonemptiness is witnessed by the original ambient generic point. -/
theorem secantCenterOpen_nonempty : (secantCenterOpen k n i hdim : Set (projectiveSpace k (n + 1))).Nonempty := by
  refine ⟨ambientGenericPoint k n, ?_⟩
  change MvPolynomial.rename Fin.succ (secantEquation k n i hdim).val.2 ≠ 0
  exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective (n + 1))).not.mpr
    (secantEquation k n i hdim).property.2.2.1

/-- Every actual centre in the internally constructed open is outside the original closed image. -/
theorem secantCenterOpen_avoids_image (c : projectiveSpace k (n + 1))
    (hc : c ∈ secantCenterOpen k n i hdim) : c ∉ Set.range i := by
  intro hi
  rw [← zeroLocus_representativeIdeal_eq_range k n i] at hi
  change MvPolynomial.rename Fin.succ (secantEquation k n i hdim).val.2 ∉ c.asHomogeneousIdeal at hc
  exact hc (hi (secantEquation k n i hdim).property.2.2.2)

/-- The original rational centre in this actual parameter open gives a finite map on the original source. -/
def projectionFromSecantOpen
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ secantCenterOpen k n i hdim) :
    X ⟶ projectiveSpace k n :=
  ProjectiveProjectionPoint.projectionFromPoint k n p hp i
    (secantCenterOpen_avoids_image k n i hdim _ hc)

/-- Finiteness for the literal original projection is retained on the actual internally produced parameter open. -/
theorem projectionFromSecantOpen_isFinite
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ secantCenterOpen k n i hdim) :
    IsFinite (projectionFromSecantOpen k n i hdim p hp hc) :=
  ProjectiveProjectionPoint.projectionFromPoint_isFinite k n p hp i
    (secantCenterOpen_avoids_image k n i hdim _ hc)

/-- The actual parameter-open projection preserves the original coefficient triangle. -/
@[reassoc]
theorem projectionFromSecantOpen_structure
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ secantCenterOpen k n i hdim) :
    projectionFromSecantOpen k n i hdim p hp hc ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) :=
  ProjectiveProjectionPoint.projectionFromPoint_structure k n p hp i
    (secantCenterOpen_avoids_image k n i hdim _ hc)

end Hironaka.Geometry.ProjectiveSecant
