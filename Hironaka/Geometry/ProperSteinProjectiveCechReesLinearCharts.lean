/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesChartSections
import Hironaka.Geometry.ProperSteinProjectiveCechSheafPushforward
import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange

/-!
# Native original Rees-linear chart sections and EVERY original restriction

Only the closed native generic affine coefficient-square proof is adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesCechChartSections.lean`,
SHA256 f3fbb73e5c149ac23632c1a347f28300c68832aedab2eb8fcf18bdc545719a03.
External ordered-Cech imports and cohomology-finiteness assumptions are excluded.
The actual chart linearity below is derived for the SAME canonical original
Rees coefficientMap and literal original section/restriction maps.
-/
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesLinearCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem affineChartCoefficientSquare {S T : CommRingCat.{u}} {Z : Scheme.{u}}
    (g : Z ⟶ Spec S) (j : Spec T ⟶ Z) (φ : S ⟶ T) (hφ : j ≫ g = Spec.map φ)
    (W : Z.Opens) (hW : ⊤ ≤ j ⁻¹ᵁ W) :
    g.appLE ⊤ W (by simp) ≫ j.appLE W ⊤ hW ≫ (Scheme.ΓSpecIso T).hom =
      (Scheme.ΓSpecIso S).hom ≫ φ := by
  have hcomp : g.appLE ⊤ W (by simp) ≫ j.appLE W ⊤ hW =
      (Spec.map φ).appTop := by
    have h := Scheme.Hom.appLE_comp_appLE j g ⊤ W ⊤ (by simp) hW
    have hh : ∀ (a b : Spec T ⟶ Spec S) (e : a = b)
        (ha : ⊤ ≤ a ⁻¹ᵁ ⊤) (hb : ⊤ ≤ b ⁻¹ᵁ ⊤),
        a.appLE ⊤ ⊤ ha = b.appLE ⊤ ⊤ hb := by
      intro a b e ha hb
      subst b
      rfl
    exact h.trans ((hh _ _ hφ _ _).trans (by
      simpa only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top] using
        (Spec.map φ).appLE_eq_app (U := ⊤)))
  rw [← Category.assoc, hcomp]
  exact Scheme.ΓSpecIso_naturality φ

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- ENTIRE original inverse-image regular sections retain the SAME actual whole family coefficient action. -/
def regularSections (U : X.Opens) : ModuleCat (reesAlgebra I) := by
  let V := ReesChartSections.projection I f ⁻¹ᵁ U
  let L := SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf
  letI := localSectionsGlobalModule L V
  exact (ModuleCat.restrictScalars (ProperGeometricGlobalFunctions.coefficientMap
    (ReesFamily.familyProjection I f))).obj (ModuleCat.of Γ(ReesFamily.family I f, ⊤) (bundleSections L V))

/-- The actual entire chart Rees ring uses the SAME original Rees coefficient homomorphism. -/
def chartModule {U : X.Opens} (hU : IsAffineOpen U) : ModuleCat (reesAlgebra I) := by
  letI := (ReesChartSections.reesCoefficient I f hU).toAlgebra
  exact ModuleCat.of (reesAlgebra I) (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)))

/-- The WHOLE original structure action passes through the actual chart section map on EVERY Rees coefficient. -/
theorem chartCoefficient_apply {U : X.Opens} (hU : IsAffineOpen U) (r : reesAlgebra I) :
    (ReesChartSections.chartSectionsIso I f hU).hom
      ((ReesFamily.family I f).presheaf.map (ReesChartSections.projection I f ⁻¹ᵁ U).leTop.op
        (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f) r)) =
      ReesChartSections.reesCoefficient I f hU r := by
  have hc :
      (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv ≫
        (ReesFamily.familyProjection I f).appLE ⊤ (ReesChartSections.projection I f ⁻¹ᵁ U) (by simp) ≫
        (ReesChartSections.chartSectionsIso I f hU).hom =
      CommRingCat.ofHom (ReesChartSections.reesCoefficient I f hU) := by
    rw [ReesChartSections.chartSectionsIso_hom]
    rw [affineChartCoefficientSquare (ReesFamily.familyProjection I f)
      (ReesRestriction.chartMap I f hU) (CommRingCat.ofHom (ReesChartSections.reesCoefficient I f hU))
      (ReesChartSections.chartMap_rees I f hU) (ReesChartSections.projection I f ⁻¹ᵁ U)
      (by rw [ReesChartSections.chartMap_preimage I f hU])]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ConcreteCategory.congr_hom hc r

/-- The SAME actual whole chart section map is an actual original-Rees-linear equivalence. -/
def chartLinearIso {U : X.Opens} (hU : IsAffineOpen U) : regularSections I f U ≅ chartModule I f hU := by
  let E : regularSections I f U ≃ₗ[reesAlgebra I] chartModule I f hU := {
    (ReesChartSections.chartSectionsIso I f hU).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := by
      intro r s
      change (ReesChartSections.chartSectionsIso I f hU).hom
          ((ReesFamily.family I f).presheaf.map (ReesChartSections.projection I f ⁻¹ᵁ U).leTop.op
            (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f) r) *
              (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from s)) =
        ReesChartSections.reesCoefficient I f hU r *
          (ReesChartSections.chartSectionsIso I f hU).hom
            (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ U) from s)
      rw [map_mul, chartCoefficient_apply] }
  exact E.toModuleIso

/-- The ORIGINAL family sheaf restriction is linear over the SAME original Rees coefficients. -/
def regularRestriction {U V : X.Opens} (hUV : U ≤ V) :
    regularSections I f V →ₗ[reesAlgebra I] regularSections I f U := by
  let L := SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf
  letI := localSectionsGlobalModule L (ReesChartSections.projection I f ⁻¹ᵁ U)
  letI := localSectionsGlobalModule L (ReesChartSections.projection I f ⁻¹ᵁ V)
  exact ((ModuleCat.restrictScalars (ProperGeometricGlobalFunctions.coefficientMap
      (ReesFamily.familyProjection I f))).map
    (ModuleCat.ofHom (actualSchemeModuleRestriction L (show ReesChartSections.projection I f ⁻¹ᵁ U ≤
      ReesChartSections.projection I f ⁻¹ᵁ V from fun _ hx => hUV hx)))).hom

/-- The actual coefficientwise Rees restriction is linear for the SAME original whole Rees coefficient map. -/
def chartRestriction {U V : X.Opens} (hUV : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    chartModule I f hV →ₗ[reesAlgebra I] chartModule I f hU := by
  letI := (ReesChartSections.reesCoefficient I f hU).toAlgebra
  letI := (ReesChartSections.reesCoefficient I f hV).toAlgebra
  exact ({ toRingHom := ReesChartSections.reesRestriction I f hUV hU hV
           commutes' := fun r => RingHom.congr_fun
             (ReesChartSections.reesRestriction_comp_reesCoefficient I f hUV hU hV) r } :
    reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV)) →ₐ[reesAlgebra I]
      reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))).toLinearMap

/-- EVERY original whole section restriction commutes with the SAME genuine Rees-linear chart frames. -/
theorem chartLinearIso_naturality {U V : X.Opens} (hUV : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (chartLinearIso I f hU).hom.hom.comp (regularRestriction I f hUV) =
      (chartRestriction I f hUV hU hV).comp (chartLinearIso I f hV).hom.hom := by
  ext s
  exact congrArg (fun q => q (show Γ(ReesFamily.family I f, ReesChartSections.projection I f ⁻¹ᵁ V) from s))
    (ReesChartSections.chartSectionsIso_naturality I f hUV hU hV)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesLinearCharts
