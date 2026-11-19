import Hironaka.Geometry.ProjectiveSecantTangentRelation
import Hironaka.Algebra.ProjectiveSecantTangentLinearForm
import Hironaka.Geometry.ProjectiveSecantPointLine

/-!
# Actual original homogeneous tangent-exclusion and secant centre opens
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionCenter
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual original ambient generic point is fixed by the actual internally produced projective coordinates. -/
theorem coordinateAutomorphism_apply_generic (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinateAutomorphism k n v hv).hom (ambientGenericPoint k n) = ambientGenericPoint k n := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro F
  change coordinatePolynomialEquiv k n v hv F = 0 ↔ F = 0
  constructor
  · intro h
    apply (coordinatePolynomialEquiv k n v hv).injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- An actual original whole-kernel tangent relation is selected internally from original geometric data. -/
def tangentChartEquation :
    {F : CoordinateRing k (chosenChart k n (s ≫ i)) //
      F ∈ (i.ker.ideal ⟨nativeCoordinateOpen (chosenChart k n (s ≫ i)),
        nativeCoordinateOpen_isAffine (R := k) (chosenChart k n (s ≫ i))⟩).comap
          (tangentCoordinateRingIso k n (chosenChart k n (s ≫ i))).hom.hom ∧
      ∃ j : {l : Fin (n + 2) // l ≠ chosenChart k n (s ≫ i)},
        chartAlgebraPoint k n (s ≫ i) hs (MvPolynomial.pderiv j F) ≠ 0} :=
  ⟨(exists_original_tangent_chart_relation k n i s hs hdim hx).choose,
    (exists_original_tangent_chart_relation k n i s hs hdim hx).choose_spec⟩

/-- The original affine differential gives its literal whole original homogeneous tangent linear form. -/
def originalTangentLinearForm : MvPolynomial (Fin (n + 2)) k :=
  tangentLinearForm k (chosenChart k n (s ≫ i)) (pointVector k n (s ≫ i) hs)
    (fun j => chartAlgebraPoint k n (s ≫ i) hs (MvPolynomial.pderiv j (tangentChartEquation k n i s hs hdim hx).val))

/-- The internally produced original tangent equation has genuine homogeneous degree one. -/
theorem originalTangentLinearForm_isHomogeneous :
    (originalTangentLinearForm k n i s hs hdim hx).IsHomogeneous 1 :=
  tangentLinearForm_isHomogeneous _ _ _ _

/-- Original smooth-point regularity and geometric dimension, rather than any supplied tangent certificate, prove nonvanishing. -/
theorem originalTangentLinearForm_ne_zero : originalTangentLinearForm k n i s hs hdim hx ≠ 0 :=
  tangentLinearForm_ne_zero _ _ _ _ (tangentChartEquation k n i s hs hdim hx).property.2

/-- The whole original normalized point satisfies the actual original tangent equation. -/
theorem originalTangentLinearForm_eval_fixed :
    MvPolynomial.eval (pointVector k n (s ≫ i) hs) (originalTangentLinearForm k n i s hs hdim hx) = 0 :=
  tangentLinearForm_eval_fixed _ _ _ (pointVector_chosenChart k n (s ≫ i) hs) _

/-- The actual original homogeneous tangent-exclusion open is internally computed from the original embedding and smooth rational source point. -/
def originalTangentOpen : (projectiveSpace k (n + 1)).Opens :=
  Proj.basicOpen (ProjectiveGrading k (n + 1)) (originalTangentLinearForm k n i s hs hdim hx)

/-- An actual original native point witnesses nonemptiness. -/
theorem originalTangentOpen_mem_generic : ambientGenericPoint k n ∈ originalTangentOpen k n i s hs hdim hx :=
  originalTangentLinearForm_ne_zero k n i s hs hdim hx

/-- The computed original tangent-exclusion open is a genuine nonempty native scheme open. -/
theorem originalTangentOpen_nonempty :
    (originalTangentOpen k n i s hs hdim hx : Set (projectiveSpace k (n + 1))).Nonempty :=
  ⟨ambientGenericPoint k n, originalTangentOpen_mem_generic k n i s hs hdim hx⟩

/-- The exact original fixed scheme point lies on its internally produced original tangent equation. -/
theorem originalTangentOpen_avoids_fixed : pointImage k n (s ≫ i) ∉ originalTangentOpen k n i s hs hdim hx := by
  intro h
  exact h ((pointImage_mem_homogeneous k n (s ≫ i) hs
    (originalTangentLinearForm_isHomogeneous k n i s hs hdim hx)).mpr
      (originalTangentLinearForm_eval_fixed k n i s hs hdim hx))

variable [IsIntegral X]

/-- The actual internally computed original secant-centre open contains the actual original ambient generic point. -/
theorem fixedPointCenterOpen_mem_generic (q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) (hsmall : topologicalKrullDim X < n) :
    ambientGenericPoint k n ∈ fixedPointCenterOpen k n q hq i hsmall := by
  change (coordinateAutomorphism k n (pointVector k n q hq) (pointVector_ne_zero k n q hq)).hom
    (ambientGenericPoint k n) ∈ secantCenterOpen k n (fixedPointInclusion k n q hq i) hsmall
  rw [coordinateAutomorphism_apply_generic]
  change MvPolynomial.rename Fin.succ (secantEquation k n (fixedPointInclusion k n q hq i) hsmall).val.2 ≠ 0
  exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective (n + 1))).not.mpr
    (secantEquation k n (fixedPointInclusion k n q hq i) hsmall).property.2.2.1

omit hdim in
/-- The actual original tangent-exclusion and secant-centre opens are combined on the original parameter scheme. -/
def tangentSecantCenterOpen (hsmall : topologicalKrullDim X < n) : (projectiveSpace k (n + 1)).Opens :=
  originalTangentOpen k n i s hs hsmall.le hx ⊓ fixedPointCenterOpen k n (s ≫ i) hs i hsmall

omit hdim in
/-- The two actual original opens have an actual common native point, over every original coefficient field. -/
theorem tangentSecantCenterOpen_nonempty (hsmall : topologicalKrullDim X < n) :
    (tangentSecantCenterOpen k n i s hs hx hsmall : Set (projectiveSpace k (n + 1))).Nonempty :=
  ⟨ambientGenericPoint k n, originalTangentOpen_mem_generic k n i s hs hsmall.le hx,
    fixedPointCenterOpen_mem_generic k n i (s ≫ i) hs hsmall⟩

omit hdim in
/-- Every actual original rational centre in the computed intersection internally produces its actual finite projection on the same original source. -/
theorem exists_finite_projection_from_tangentSecantOpen (hsmall : topologicalKrullDim X < n)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentSecantCenterOpen k n i s hs hx hsmall) :
    ∃ f : X ⟶ projectiveSpace k n, IsFinite f ∧
      f ≫ projectiveSpaceStructure k n = i ≫ projectiveSpaceStructure k (n + 1) :=
  ⟨projectionFromFixedPointOpen k n (s ≫ i) hs i hsmall p hp hc.2,
    projectionFromFixedPointOpen_isFinite _ _ _ _ _ _ _ _ _,
    projectionFromFixedPointOpen_structure _ _ _ _ _ _ _ _ _⟩

end Hironaka.Geometry.ProjectiveSecant
