/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesLinearCharts
import Hironaka.Geometry.ProperSteinProjectiveCechReesCoefficients
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalAffine

/-! # Actual original coefficient identity and original-base power frames

The actual affine chart coefficient is proved equal to the original section
coefficient on the ENTIRE ring. Original regular-section degree frames are
constructed from the actual canonical Rees action, not supplied as inputs.
The scalar-identity argument follows the closed native pattern in the recorded
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechDegreeComplex.lean`,
SHA256 f65e1c3fd6700cc0fcedde2a625417206d8130555ec06a0c09a883e220cdcfa3,
without its external ordered-Cech imports.
-/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum Polynomial
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual affine coefficient map is the WHOLE original section coefficient map. -/
theorem chartCoefficient_eq_sectionCoefficient {U : X.Opens} (hU : IsAffineOpen U) :
    ReesRestriction.chartCoefficient f hU = Infinitesimal.sectionCoefficient f U := by
  have hj : hU.fromSpec.appLE U ⊤ (by simp) = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    change (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (𝟙 _) = _
    simp
  have h := ReesLinearCharts.affineChartCoefficientSquare f hU.fromSpec
    (Spec.preimage (hU.fromSpec ≫ f)) (by simp) U (by simp)
  rw [hj, Iso.inv_hom_id, Category.comp_id] at h
  have hc := congrArg (fun q => ((Scheme.ΓSpecIso (.of R)).inv ≫ q).hom) h
  simpa [ReesRestriction.chartCoefficient, Infinitesimal.sectionCoefficient] using hc.symm

/-- Restricting the actual chart Rees action to R recovers the SAME original chart scalar action. -/
def chartBaseScalarEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    letI := ReesRestriction.chartAlgebra f hU
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.chartModule I f hU) ≃ₗ[R]
      reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) := by
  letI := ReesRestriction.chartAlgebra f hU
  refine {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := ?_ }
  intro r p
  let p' : reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) := p
  change ReesChartSections.reesCoefficient I f hU (algebraMap R (reesAlgebra I) r) *
    p' = r • p'
  rw [show ReesChartSections.reesCoefficient I f hU (algebraMap R (reesAlgebra I) r) =
    algebraMap R (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))) r from
      (ReesBaseChange.reesMap (A := Γ(X, U)) I).commutes r]
  exact (Algebra.smul_def r p').symm

/-- ENTIRE original regular sections decompose into their genuine original affine ideal powers. -/
def regularBasePowerEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    letI := ReesRestriction.chartAlgebra f hU
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f U) ≃ₗ[R]
      ⨁ d : ℕ, ↥((I.map (ReesRestriction.chartCoefficient f hU))^d) := by
  letI := ReesRestriction.chartAlgebra f hU
  exact ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).mapIso
      (ReesLinearCharts.chartLinearIso I f hU)).toLinearEquiv ≪≫ₗ
    chartBaseScalarEquiv I f hU ≪≫ₗ
    (ReesCoefficients.powerEquiv (I.map (ReesRestriction.chartCoefficient f hU))).restrictScalars R

/-- EVERY original power-frame coordinate is its literal actual chart polynomial coefficient. -/
theorem regularBasePowerEquiv_apply {U : X.Opens} (hU : IsAffineOpen U)
    (s : (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
      (ReesLinearCharts.regularSections I f U)) (d : ℕ) :
    letI := ReesRestriction.chartAlgebra f hU
    (regularBasePowerEquiv I f hU s d : Γ(X, U)) =
      ((ReesChartSections.chartSectionsIso I f hU).hom
        (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from s) : Γ(X, U)[X]).coeff d := by
  let := ReesRestriction.chartAlgebra f hU
  rw [regularBasePowerEquiv, LinearEquiv.trans_apply]
  exact congrArg Subtype.val (ReesCoefficients.coefficients_apply _ _ d)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerCharts
