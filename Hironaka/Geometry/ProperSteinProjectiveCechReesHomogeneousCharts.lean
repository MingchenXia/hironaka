/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerFrames

/-! # Actual original homogeneous action on ENTIRE original Rees chart sections

Closed monomial-action pattern adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechHomogeneousAction.lean`,
SHA256 14d780e16f281d917cdfc09f3fa699b2b10a8d6457bf14cf79b0717369e1bd6b.
Only native Mathlib+owned project producers are imported; original section
coefficient powers and canonical actual Rees action are retained throughout.
-/
open CategoryTheory AlgebraicGeometry
open scoped Polynomial DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual original homogeneous coefficient multiplies the SAME actual section ideal powers. -/
def originalPowerMultiply (U : X.Opens) {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    ReesPowerDiagram.powerSections I f d U →ₗ[R] ReesPowerDiagram.powerSections I f (e+d) U := by
  letI := (Infinitesimal.sectionCoefficient f U).toAlgebra
  exact ReesMultiplication.powerMultiply I a d

/-- The ORIGINAL scalar action on ENTIRE original regular sections, restricted only to R. -/
def scalarAction (U : X.Opens) (p : reesAlgebra I) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f U) →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f U) :=
  ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
    (p • 𝟙 (ReesLinearCharts.regularSections I f U))).hom

/-- Each actual inverse-frame original summand is its literal original chart monomial. -/
theorem sectionPowerEquiv_symm_lof {U : X.Opens} (hU : IsAffineOpen U) (d : ℕ)
    (x : ReesPowerDiagram.powerSections I f d U) :
    ((ReesChartSections.chartSectionsIso I f hU).hom
      (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from
        (ReesPowerFrames.sectionPowerEquiv I f hU).symm
          (DirectSum.lof R ℕ (fun k => ReesPowerDiagram.powerSections I f k U) d x)) : Γ(X, U)[X]) =
      Polynomial.monomial d
        (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from x).val := by
  apply Polynomial.ext
  intro k
  have h := congrArg (fun z : ⨁ j : ℕ, ReesPowerDiagram.powerSections I f j U =>
    (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^k) from z k).val)
      ((ReesPowerFrames.sectionPowerEquiv I f hU).apply_symm_apply
        (DirectSum.lof R ℕ (fun j => ReesPowerDiagram.powerSections I f j U) d x))
  rw [ReesPowerFrames.sectionPowerEquiv_apply] at h
  refine h.trans ?_
  by_cases hk : k=d
  · subst k
    rw [DirectSum.lof_apply]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hk)]
    rfl

/-- The ENTIRE actual chart action is the literal ORIGINAL homogeneous coefficient and original degree shift. -/
theorem homogeneous_action {U : X.Opens} (hU : IsAffineOpen U) {e : ℕ} (a : ↥(I^e))
    (d : ℕ) (x : ReesPowerDiagram.powerSections I f d U) :
    ReesPowerFrames.sectionPowerEquiv I f hU
      (scalarAction I f U (ReesMultiplication.monomial I e a)
        ((ReesPowerFrames.sectionPowerEquiv I f hU).symm
          (DirectSum.lof R ℕ (fun k => ReesPowerDiagram.powerSections I f k U) d x))) =
      DirectSum.lof R ℕ (fun k => ReesPowerDiagram.powerSections I f k U) (e+d)
        (originalPowerMultiply I f U a d x) := by
  let E := ReesPowerFrames.sectionPowerEquiv I f hU
  let s := E.symm (DirectSum.lof R ℕ (fun k => ReesPowerDiagram.powerSections I f k U) d x)
  let μ := ReesMultiplication.monomial I e a
  have hs :
      ((ReesChartSections.chartSectionsIso I f hU).hom
        (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from
          scalarAction I f U μ s) : Γ(X, U)[X]) =
      Polynomial.monomial (e+d)
        (Infinitesimal.sectionCoefficient f U a *
          (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from x).val) := by
    have hl := (ReesLinearCharts.chartLinearIso I f hU).toLinearEquiv.map_smul μ
      (show ReesLinearCharts.regularSections I f U from s)
    have hp := congrArg (fun p : ReesLinearCharts.chartModule I f hU =>
      (show reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) from p).val) hl
    change ((ReesChartSections.chartSectionsIso I f hU).hom _ : Γ(X, U)[X]) = _ at hp
    erw [hp]
    change Polynomial.map (ReesRestriction.chartCoefficient f hU) (Polynomial.monomial e a.val) *
      ((ReesChartSections.chartSectionsIso I f hU).hom
        (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from s) : Γ(X, U)[X]) = _
    rw [sectionPowerEquiv_symm_lof I f hU d x, Polynomial.map_monomial,
      Polynomial.monomial_mul_monomial]
    exact congrArg (Polynomial.monomial (e+d))
      (congrArg (fun c : Γ(X, U) => c *
        (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from x).val)
        (RingHom.congr_fun (ReesPowerCharts.chartCoefficient_eq_sectionCoefficient f hU) a))
  apply DirectSum.ext
  intro k
  apply Subtype.ext
  rw [ReesPowerFrames.sectionPowerEquiv_apply]
  change ((ReesChartSections.chartSectionsIso I f hU).hom
    (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from
      scalarAction I f U μ s) : Γ(X, U)[X]).coeff k = _
  rw [hs]
  by_cases hk : k=e+d
  · subst k
    rw [DirectSum.lof_apply]
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
    rfl
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hk]
    simp only [Polynomial.coeff_monomial, if_neg (Ne.symm hk)]
    rfl

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesHomogeneousCharts
