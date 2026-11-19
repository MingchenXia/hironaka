/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesInverseImageDiagram
import Hironaka.Geometry.ProperSteinProjectiveCechSubsetDirectSum
import Hironaka.Geometry.ProperSteinProjectiveCechSubsetNonemptyComparison
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerDiagram
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerFrames

/-! # Literal original coefficient restriction and the SAME native subset complex -/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ScalarRestriction
variable {R S ι : Type u} [CommRing R] [CommRing S] [LinearOrder ι]
  (φ : R →+* S) (D : Finset ι ⥤ ModuleCat.{u} S)

/-- The entire original scalar-restricted complex retains EVERY original section, restriction, sign and sum. -/
def restrictSubsetIso :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj
        (subsetCechComplex D) ≅
      subsetCechComplex (D ⋙ ModuleCat.restrictScalars φ) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => by
    let E :
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj
          (subsetCechComplex D)).X n ≃ₗ[R]
          (subsetCechComplex (D ⋙ ModuleCat.restrictScalars φ)).X n := {
      toFun := fun x => ⟨(show subsetCechCardPiece D (n+1) from x).val,
        (show subsetCechCardPiece D (n+1) from x).property⟩
      invFun := fun x => ⟨(show subsetCechCardPiece (D ⋙ ModuleCat.restrictScalars φ) (n+1) from x).val,
        (show subsetCechCardPiece (D ⋙ ModuleCat.restrictScalars φ) (n+1) from x).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    exact E.toModuleIso) (by
      intro n m h
      have hm : n+1=m := h
      subst m
      simp only [Functor.mapHomologicalComplex_obj_d, subsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)
end ScalarRestriction

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The SAME actual whole inverse-image section diagram, with only its ORIGINAL R scalars restricted. -/
def originalBaseDiagram : Finset ι ⥤ ModuleCat.{u} R :=
  ReesInverseImageDiagram.baseDiagram I f U ⋙
    ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))

/-- The actual original Rees inverse-image complex retains its WHOLE original R coefficient action. -/
def originalScalarComplexIso :
    ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).obj
        (subsetCechComplex (ReesInverseImageDiagram.baseDiagram I f U)) ≅
      subsetCechComplex (originalBaseDiagram I f U) :=
  restrictSubsetIso (algebraMap R (reesAlgebra I)) (ReesInverseImageDiagram.baseDiagram I f U)

section AffineOriginalIntersections
variable [X.IsSeparated] (hU : ∀ j, IsAffineOpen (U j))
include hU

omit [LinearOrder ι] in
/-- ORIGINAL separatedness makes EVERY NONEMPTY original finite affine intersection affine. -/
theorem nonemptyIntersection_isAffine (S : Finset ι) (hS : S.Nonempty) :
    IsAffineOpen (actualSchemeSubsetOpen U S) := by
  simpa [actualSchemeSubsetOpen, Finset.inf_eq_iInf] using
    IsAffineOpen.biInf (S : Set ι) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (fun j _ => hU j)

/-- The GENUINE original power frame on EVERY NONEMPTY original intersection. -/
def nonemptyFrame (S : Finset ι) (hS : S.Nonempty) :
    (originalBaseDiagram I f U).obj S ≅
      (SubsetDirectSum.diagram (fun d => ReesPowerDiagram.powerDiagram I f U d)).obj S :=
  (ReesPowerFrames.sectionPowerEquiv I f (nonemptyIntersection_isAffine U hU S hS)).toModuleIso

omit [LinearOrder ι] in
/-- EVERY original nonempty subset restriction commutes with the SAME actual entire power frames. -/
theorem nonemptyFrame_naturality (S T : Finset ι) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    (originalBaseDiagram I f U).map (homOfLE hST) ≫ (nonemptyFrame I f U hU T hT).hom =
      (nonemptyFrame I f U hU S hS).hom ≫
        (SubsetDirectSum.diagram (fun d => ReesPowerDiagram.powerDiagram I f U d)).map (homOfLE hST) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact ReesPowerFrames.sectionPowerEquiv_naturality I f (actualSchemeSubsetOpen_antitone U hST)
    (nonemptyIntersection_isAffine U hU T hT) (nonemptyIntersection_isAffine U hU S hS) s

variable [Fintype ι]

/-- The ENTIRE original inverse-image complex is the genuine direct sum of ORIGINAL ideal-power complexes. -/
def inverseImageDegreeComplexIso :
    subsetCechComplex (originalBaseDiagram I f U) ≅
      SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d) :=
  SubsetNonemptyComparison.complexIso (originalBaseDiagram I f U)
      (SubsetDirectSum.diagram (fun d => ReesPowerDiagram.powerDiagram I f U d))
      (nonemptyFrame I f U hU) (nonemptyFrame_naturality I f U hU) ≪≫
    SubsetDirectSum.complexIso (fun d => ReesPowerDiagram.powerDiagram I f U d)

/-- The actual original Rees coefficient action is retained through the WHOLE original degree-complex comparison. -/
def originalDegreeComplexIso :
    ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).obj
        (subsetCechComplex (ReesInverseImageDiagram.baseDiagram I f U)) ≅
      SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d) :=
  originalScalarComplexIso I f U ≪≫ inverseImageDegreeComplexIso I f U hU

/-- The SAME native original pulled-back coordinate complex genuinely decomposes into the SAME original powers. -/
def nativeOriginalDegreeComplexIso :
    ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).obj
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
        (SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf)
        (fun j => ReesChartSections.projection I f ⁻¹ᵁ U j)
        (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f)))) ≅
      SubsetDirectSum.complexSum (fun d => ReesPowerDiagram.powerComplex I f U d) :=
  ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).mapIso
      (ReesInverseImageDiagram.nativeComplexIso I f U).symm ≪≫
    originalDegreeComplexIso I f U hU
end AffineOriginalIntersections

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeComplex
