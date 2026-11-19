/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesDegreeComplex
import Hironaka.Geometry.ProperSteinProjectiveCechReesHomogeneousCharts

/-! # The SAME actual whole original complex frame and original homogeneous action

Closed original-monomial proof pattern adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechHomogeneousAction.lean`,
SHA256 14d780e16f281d917cdfc09f3fa699b2b10a8d6457bf14cf79b0717369e1bd6b.
Only native Mathlib+own actual original native subset/section producers are used.
-/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousComplexFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The ACTUAL original Rees scalar endomorphism of the SAME original R-linear diagram. -/
def scalarNatural (p : reesAlgebra I) :
    ReesDegreeComplex.originalBaseDiagram I f U ⟶ ReesDegreeComplex.originalBaseDiagram I f U where
  app S := (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
    (p • 𝟙 ((ReesInverseImageDiagram.baseDiagram I f U).obj S))
  naturality S T h := by
    let F := ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))
    let D := ReesInverseImageDiagram.baseDiagram I f U
    change F.map (D.map h) ≫ F.map (p • 𝟙 (D.obj T)) =
      F.map (p • 𝟙 (D.obj S)) ≫ F.map (D.map h)
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    ext x
    exact ((D.map h).hom.map_smul p x).symm

/-- The SAME original actual scalar on the ENTIRE original native subset complex. -/
def scalarComplex (p : reesAlgebra I) :
    subsetCechComplex (ReesDegreeComplex.originalBaseDiagram I f U) ⟶
      subsetCechComplex (ReesDegreeComplex.originalBaseDiagram I f U) :=
  subsetCechComplexMap (scalarNatural I f U p)

variable [X.IsSeparated] [Fintype ι] (hU : ∀ j, IsAffineOpen (U j))
include hU

/-- The actual SAME entire complex isomorphism evaluated at an original cochain term. -/
def termFrame (n : ℕ) :
    subsetCechCardPiece (ReesDegreeComplex.originalBaseDiagram I f U) (n+1) ≃ₗ[R]
      ⨁ d : ℕ, subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U d) (n+1) :=
  ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) n).mapIso
    (ReesDegreeComplex.inverseImageDegreeComplexIso I f U hU)).toLinearEquiv

/-- EVERY actual entire-frame coefficient is precisely the SAME original nonempty chart coefficient. -/
theorem termFrame_apply_of_card (n : ℕ)
    (c : subsetCechCardPiece (ReesDegreeComplex.originalBaseDiagram I f U) (n+1))
    (d : ℕ) (S : Finset ι) (hS : S.card=n+1) :
    (termFrame I f U hU n c d).val S =
      ReesPowerFrames.sectionPowerEquiv I f
        (ReesDegreeComplex.nonemptyIntersection_isAffine U hU S (Finset.card_pos.mp (by omega)))
        (c.val S) d := by
  change (SubsetDirectSum.cardinalEquiv (fun j => ReesPowerDiagram.powerDiagram I f U j) (n+1)
    (SubsetNonemptyComparison.cardinalEquiv (ReesDegreeComplex.originalBaseDiagram I f U)
      (SubsetDirectSum.diagram (fun j => ReesPowerDiagram.powerDiagram I f U j))
      (ReesDegreeComplex.nonemptyFrame I f U hU) (n+1) (by omega) c) d).val S = _
  rw [SubsetDirectSum.cardinalEquiv_apply,
    SubsetNonemptyComparison.cardinalEquiv_apply_of_card _ _ _ _ _ _ S hS]
  rfl

/-- Every original inverse-frame summand restricts to the SAME original local inverse-frame summand. -/
theorem termFrame_symm_lof_restrict (n d : ℕ)
    (x : subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U d) (n+1))
    (S : Finset ι) (hS : S.card=n+1) :
    ((termFrame I f U hU n).symm
      (DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) d x)).val S =
    (ReesPowerFrames.sectionPowerEquiv I f
      (ReesDegreeComplex.nonemptyIntersection_isAffine U hU S (Finset.card_pos.mp (by omega)))).symm
      (DirectSum.lof R ℕ (fun j => ReesPowerDiagram.powerSections I f j (actualSchemeSubsetOpen U S)) d (x.val S)) := by
  apply (ReesPowerFrames.sectionPowerEquiv I f
    (ReesDegreeComplex.nonemptyIntersection_isAffine U hU S (Finset.card_pos.mp (by omega)))).injective
  rw [LinearEquiv.apply_symm_apply]
  apply DirectSum.ext
  intro k
  have h := congrArg
    (fun z : ⨁ j : ℕ, subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1) => (z k).val S)
    ((termFrame I f U hU n).apply_symm_apply
      (DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) d x))
  rw [termFrame_apply_of_card I f U hU n _ k S hS] at h
  refine h.trans ?_
  by_cases hk : k=d
  · subst k
    rw [DirectSum.lof_apply, DirectSum.lof_apply]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk,
      DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
    rfl

/-- The ENTIRE actual original cochain action is the ORIGINAL multiplication and EXACT original degree shift. -/
theorem term_homogeneous {e : ℕ} (a : ↥(I^e)) (d n : ℕ)
    (x : subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U d) (n+1)) :
    termFrame I f U hU n
      (((scalarComplex I f U (ReesMultiplication.monomial I e a)).f n).hom
        ((termFrame I f U hU n).symm
          (DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) d x))) =
      DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) (e+d)
        (((ReesPowerDiagram.homogeneousComplexMap I f U a d).f n).hom x) := by
  apply DirectSum.ext
  intro k
  apply Subtype.ext
  funext S
  by_cases hS : S.card=n+1
  · rw [termFrame_apply_of_card I f U hU n _ k S hS]
    change ReesPowerFrames.sectionPowerEquiv I f
      (ReesDegreeComplex.nonemptyIntersection_isAffine U hU S (Finset.card_pos.mp (by omega)))
      (ReesHomogeneousCharts.scalarAction I f (actualSchemeSubsetOpen U S) (ReesMultiplication.monomial I e a)
        (((termFrame I f U hU n).symm
          (DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) d x)).val S)) k = _
    rw [termFrame_symm_lof_restrict I f U hU n d x S hS]
    rw [ReesHomogeneousCharts.homogeneous_action]
    by_cases hk : k=e+d
    · subst k
      rw [DirectSum.lof_apply, DirectSum.lof_apply]
      rfl
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk,
        DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
      rfl
  · exact ((termFrame I f U hU n _ k).property S hS).trans
      ((DirectSum.lof R ℕ (fun j => subsetCechCardPiece (ReesPowerDiagram.powerDiagram I f U j) (n+1)) (e+d)
        (((ReesPowerDiagram.homogeneousComplexMap I f U a d).f n).hom x) k).property S hS).symm

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousComplexFrames
