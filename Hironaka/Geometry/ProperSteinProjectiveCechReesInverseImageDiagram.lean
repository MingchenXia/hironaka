/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesLinearCharts

/-! # The actual original Rees inverse-image diagram and its whole native comparison

The canonical family coefficient action, original sections and EVERY original
restriction are retained. No affine assertion on the empty intersection is used.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesInverseImageDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The actual inverse-image section diagram, using the unchanged actual global regular-function action. -/
def globalDiagram : Finset ι ⥤ ModuleCat.{u} Γ(ReesFamily.family I f, ⊤) := by
  let L : (ReesFamily.family I f).Modules := SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf
  letI : ∀ V : (ReesFamily.family I f).Opens,
      Module Γ(ReesFamily.family I f, ⊤) (bundleSections L V) :=
    fun V => localSectionsGlobalModule L V
  exact {
    obj := fun S => ModuleCat.of Γ(ReesFamily.family I f, ⊤)
      (bundleSections L (ReesChartSections.projection I f ⁻¹ᵁ actualSchemeSubsetOpen U S))
    map := fun h => ModuleCat.ofHom (actualSchemeModuleRestriction L
      (show ReesChartSections.projection I f ⁻¹ᵁ actualSchemeSubsetOpen U _ ≤
        ReesChartSections.projection I f ⁻¹ᵁ actualSchemeSubsetOpen U _ from
          fun _ hx => actualSchemeSubsetOpen_antitone U (leOfHom h) hx))
    map_id := by
      intro S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change L.presheaf.map (𝟙 _).op s = s
      rw [op_id, L.presheaf.map_id]
      rfl
    map_comp := by
      intro S T W h k
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change L.presheaf.map _ s = L.presheaf.map _ (L.presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl }

/-- The SAME entire original diagram retains the canonical ORIGINAL Rees coefficient map. -/
def baseDiagram : Finset ι ⥤ ModuleCat.{u} (reesAlgebra I) :=
  globalDiagram I f U ⋙ ModuleCat.restrictScalars
    (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f))

/-- The actual whole diagram agrees with the SAME original pulled-back-coordinate section diagram. -/
def nativeDiagramIso :
    baseDiagram I f U ≅ actualSchemeModuleBaseSubsetDiagram
      (SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf)
      (fun j => ReesChartSections.projection I f ⁻¹ᵁ U j)
      (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f)) := by
  let L : (ReesFamily.family I f).Modules := SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf
  let c := ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f)
  refine NatIso.ofComponents (fun S =>
    (ModuleCat.restrictScalars c).mapIso (actualSchemeModuleOpenIso L
      (actualSchemePushforwardSubsetOpen_eq (ReesChartSections.projection I f) U S))) ?_
  intro S T h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change L.presheaf.map _ (L.presheaf.map _ s) = L.presheaf.map _ (L.presheaf.map _ s)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- The ENTIRE original complex comparison preserves every actual original restriction and coefficient. -/
def nativeComplexIso :
    subsetCechComplex (baseDiagram I f U) ≅ subsetCechComplex
      (actualSchemeModuleBaseSubsetDiagram
        (SheafOfModules.unit (ReesFamily.family I f).ringCatSheaf)
        (fun j => ReesChartSections.projection I f ⁻¹ᵁ U j)
        (ProperGeometricGlobalFunctions.coefficientMap (ReesFamily.familyProjection I f))) :=
  (actualSubsetCechFunctor (K := reesAlgebra I) (I := ι)).mapIso (nativeDiagramIso I f U)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesInverseImageDiagram
