/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerCharts
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerDiagram

/-! # Literal original ideal-power frames and EVERY original restriction

All power modules use the SAME original section coefficient. Their comparison
with actual Rees-family regular sections retains the actual original R action,
EVERY actual polynomial coefficient, and EVERY original affine restriction.
-/
open CategoryTheory AlgebraicGeometry
open scoped DirectSum Polynomial
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The coefficient identity retains the SAME ambient element in each actual original power. -/
def chartPowerEquiv {U : X.Opens} (hU : IsAffineOpen U) (d : ℕ) :
    letI := ReesRestriction.chartAlgebra f hU
    ↥((I.map (ReesRestriction.chartCoefficient f hU))^d) ≃ₗ[R]
      ReesPowerDiagram.powerSections I f d U := by
  letI := ReesRestriction.chartAlgebra f hU
  refine {
    toFun := fun x => ⟨x.val, by
      simpa only [ReesPowerCharts.chartCoefficient_eq_sectionCoefficient f hU] using x.property⟩
    invFun := fun x => ⟨(show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from x).val, by
      simpa only [ReesPowerCharts.chartCoefficient_eq_sectionCoefficient f hU] using
        (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from x).property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := ?_ }
  intro r x
  apply Subtype.ext
  change ReesRestriction.chartCoefficient f hU r * x.val =
    Infinitesimal.sectionCoefficient f U r * x.val
  exact congrArg (fun c : Γ(X, U) => c * x.val)
    (RingHom.congr_fun (ReesPowerCharts.chartCoefficient_eq_sectionCoefficient f hU) r)

/-- ENTIRE original regular sections have the SAME original ideal-power coordinates and original R action. -/
def sectionPowerEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f U) ≃ₗ[R]
      ⨁ d : ℕ, ReesPowerDiagram.powerSections I f d U := by
  letI := ReesRestriction.chartAlgebra f hU
  exact ReesPowerCharts.regularBasePowerEquiv I f hU ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun d => chartPowerEquiv I f hU d)

/-- EVERY actual power-frame coordinate is the literal SAME original chart polynomial coefficient. -/
theorem sectionPowerEquiv_apply {U : X.Opens} (hU : IsAffineOpen U)
    (s : (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
      (ReesLinearCharts.regularSections I f U)) (d : ℕ) :
    (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from sectionPowerEquiv I f hU s d).val =
      ((ReesChartSections.chartSectionsIso I f hU).hom
        (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from s) : Γ(X, U)[X]).coeff d := by
  let := ReesRestriction.chartAlgebra f hU
  change (ReesPowerCharts.regularBasePowerEquiv I f hU s d : Γ(X, U)) = _
  exact ReesPowerCharts.regularBasePowerEquiv_apply I f hU s d

/-- The SAME original whole regular restriction, restricted only along the original R coefficient map. -/
def regularBaseRestriction {U V : X.Opens} (h : U ≤ V) :
    (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f V) →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
        (ReesLinearCharts.regularSections I f U) :=
  ((ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
    (ModuleCat.ofHom (ReesLinearCharts.regularRestriction I f h))).hom

/-- EVERY original affine inclusion commutes with the ENTIRE genuine original-power frames. -/
theorem sectionPowerEquiv_naturality {U V : X.Opens} (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (s : (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).obj
      (ReesLinearCharts.regularSections I f V)) :
    sectionPowerEquiv I f hU (regularBaseRestriction I f h s) =
      DirectSum.lmap (fun d => ReesPowerDiagram.powerRestriction I f d h)
        (sectionPowerEquiv I f hV s) := by
  apply DirectSum.ext
  intro d
  apply Subtype.ext
  rw [sectionPowerEquiv_apply]
  change ((ReesChartSections.chartSectionsIso I f hU).hom
    ((ReesFamily.family I f).presheaf.map _
      (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ V) from s)) : Γ(X, U)[X]).coeff d =
    X.presheaf.map _
      (show ↥((I.map (Infinitesimal.sectionCoefficient f V))^d) from sectionPowerEquiv I f hV s d).val
  rw [sectionPowerEquiv_apply]
  have hc := ConcreteCategory.congr_hom (ReesChartSections.chartSectionsIso_naturality I f h hU hV)
    (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ V) from s)
  have hd := congrArg (fun p : reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) =>
    (p : Γ(X, U)[X]).coeff d) hc
  simp only [ConcreteCategory.comp_apply] at hd
  erw [ReesChartSections.reesRestriction_coeff] at hd
  exact hd

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerFrames
