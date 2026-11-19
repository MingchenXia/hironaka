/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesDegreeComplex
import Hironaka.Geometry.ProperSteinProjectiveCechReesCohomology
import Mathlib.Algebra.Module.TransferInstance

/-! # The SAME original power homologies and the actual finite Rees action

The closed native action-transfer pattern is adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechHomologyModule.lean`,
SHA256 0477d74b281ceab28e5bb262d77ee9345e940285b3337f59a12f399f4468614f;
the original ΓSpec coefficient action is replaced by the already actual
original Rees ring action and genuine same-source native subset producer.
No native cohomology-finiteness or homogeneous-action output is assumed.
The genuine homogeneous monomial formula is a SEPARATE subsequent producer.
-/
open CategoryTheory AlgebraicGeometry Limits
open scoped DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeHomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The SAME actual native complex of original-family regular sections on original inverse-image coordinates. -/
abbrev nativeComplex : CochainComplex (ModuleCat.{u} (reesAlgebra I)) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
    (SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf)
    (fun j => ReesChartSections.projection I f ⁻¹ᵁ U j)
    (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f)))

/-- The SAME genuine native original ideal-power homologies, with their unchanged original R action. -/
abbrev powerHomology (p : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (⨁ d : ℕ, (ReesPowerDiagram.powerComplex I f U d).homology p)

/-- Genuine exact scalar restriction commutes with the ACTUAL original native complex homology. -/
def scalarHomologyIso (p : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapHomologicalComplex (.up ℕ)).obj
        (nativeComplex I f U)).homology p ≅
      (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj ((nativeComplex I f U).homology p) :=
  ((nativeComplex I f U).sc p).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I)))

section AffineOriginalCover
variable [X.IsSeparated] [Fintype ι] (hU : ∀ j, IsAffineOpen (U j))
include hU

/-- The ENTIRE actual original native homology is genuinely the SAME original-power homology sum. -/
def homologyEquiv (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        ((nativeComplex I f U).homology p) ≃ₗ[R] powerHomology I f U p :=
  ((scalarHomologyIso I f U p).symm ≪≫
    HomologicalComplex.homologyMapIso (ReesDegreeComplex.nativeOriginalDegreeComplexIso I f U hU) p ≪≫
    SubsetDirectSum.complexSumHomologyIso (fun d => ReesPowerDiagram.powerComplex I f U d) p).toLinearEquiv

/-- Transfer the ACTUAL original native Rees coefficient action through the genuine WHOLE comparison. -/
@[instance_reducible]
def reesModule (p : ℕ) : Module (reesAlgebra I) (powerHomology I f U p) := by
  let : Module (reesAlgebra I)
      ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        ((nativeComplex I f U).homology p)) := ((nativeComplex I f U).homology p).isModule
  exact (homologyEquiv I f U hU p).symm.toAddEquiv.module (reesAlgebra I)

/-- The WHOLE original homology comparison is linear for the SAME actual transported original Rees action. -/
def coefficientEquiv (p : ℕ) :
    letI := reesModule I f U hU p
    (nativeComplex I f U).homology p ≃ₗ[reesAlgebra I] powerHomology I f U p := by
  letI := reesModule I f U hU p
  let : Module (reesAlgebra I)
      ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        ((nativeComplex I f U).homology p)) := ((nativeComplex I f U).homology p).isModule
  exact ((homologyEquiv I f U hU p).symm.toAddEquiv.linearEquiv (reesAlgebra I)).symm

/-- EVERY actual original Rees scalar acts on EVERY original class through the specified original action. -/
theorem reesModule_smul (p : ℕ) (a : reesAlgebra I) (x : powerHomology I f U p) :
    letI := reesModule I f U hU p
    a • x = coefficientEquiv I f U hU p
      (a • (coefficientEquiv I f U hU p).symm x) := by
  let := reesModule I f U hU p
  rfl

/-- Restricting the actual transported Rees action recovers the UNCHANGED ORIGINAL R action on every class. -/
theorem originalScalar (p : ℕ) (r : R) (x : powerHomology I f U p) :
    letI := reesModule I f U hU p
    algebraMap R (reesAlgebra I) r • x = r • x := by
  let := reesModule I f U hU p
  change homologyEquiv I f U hU p (r • (homologyEquiv I f U hU p).symm x) = r • x
  simpa only [LinearEquiv.apply_symm_apply] using
    (homologyEquiv I f U hU p).map_smul r ((homologyEquiv I f U hU p).symm x)

/-- The SAME original R module and original Rees action form the actual original scalar tower. -/
theorem originalScalarTower (p : ℕ) :
    letI := reesModule I f U hU p
    IsScalarTower R (reesAlgebra I) (powerHomology I f U p) := by
  let := reesModule I f U hU p
  constructor
  intro r a x
  rw [Algebra.smul_def r a, mul_smul, originalScalar]
end AffineOriginalCover

section OriginalProjectiveProducer
variable {n : ℕ} (i : X ⟶ projectiveSpace R n) [IsClosedImmersion i]
include i

/-- Original projectivity INTERNALLY derives original separatedness over the affine coefficient base. -/
theorem projectiveSeparated : X.IsSeparated := by
  let : IsProper (i ≫ projectiveSpaceStructure R n) := inferInstance
  constructor
  rw [← terminal.comp_from (i ≫ projectiveSpaceStructure R n)]
  infer_instance

/-- ONLY ORIGINAL projective data determine the actual original Rees action on the SAME coordinate power homologies. -/
@[instance_reducible]
def projectiveReesModule (p : ℕ) :
    Module (reesAlgebra I) (powerHomology I (i ≫ projectiveSpaceStructure R n) (originalClosedCoordinateOpens i) p) := by
  letI := projectiveSeparated i
  exact reesModule I (i ≫ projectiveSpaceStructure R n) (originalClosedCoordinateOpens i)
    (originalClosedCoordinateOpens_isAffine i) p

/-- Original Noetherian PROJECTIVE geometry proves finite the ENTIRE actual original-power native homology sum. -/
theorem projective_finite [IsNoetherianRing R] (p : ℕ) :
    letI := projectiveReesModule I i p
    Module.Finite (reesAlgebra I)
      (powerHomology I (i ≫ projectiveSpaceStructure R n) (originalClosedCoordinateOpens i) p) := by
  let := projectiveSeparated i
  let := reesModule I (i ≫ projectiveSpaceStructure R n) (originalClosedCoordinateOpens i)
    (originalClosedCoordinateOpens_isAffine i) p
  let : Module.Finite (reesAlgebra I)
      ((nativeComplex I (i ≫ projectiveSpaceStructure R n) (originalClosedCoordinateOpens i)).homology p) :=
    ReesCohomology.nativeCech_finite I i p
  exact Module.Finite.equiv (coefficientEquiv I (i ≫ projectiveSpaceStructure R n)
    (originalClosedCoordinateOpens i) (originalClosedCoordinateOpens_isAffine i) p)
end OriginalProjectiveProducer

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreeHomology
