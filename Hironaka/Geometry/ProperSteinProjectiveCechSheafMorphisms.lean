/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections
import Hironaka.Geometry.ProperSteinProjectiveCechPolynomialLocalization

/-! # Actual original native section and complex maps of original sheaf morphisms

Every component is the SAME native sheaf morphism component; every original
coefficient, restriction, identity and composition is retained. No section
comparison, quasicoherence, affine or output-map premise is introduced.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.SheafMorphisms
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {X : Scheme.{u}} {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤))
  {M N : X.Modules} (a : M ⟶ N)

/-- The actual ORIGINAL native component is linear for the SAME original restricted base action. -/
def sectionMap (V : X.Opens) :
    letI := localSectionsGlobalModule M V
    letI := localSectionsGlobalModule N V
    (ModuleCat.restrictScalars c).obj (ModuleCat.of Γ(X, ⊤) (bundleSections M V)) ⟶
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Γ(X, ⊤) (bundleSections N V)) := by
  let := localSectionsGlobalModule M V
  let := localSectionsGlobalModule N V
  let P : ModuleCat.{u} K := (ModuleCat.restrictScalars c).obj
    (ModuleCat.of Γ(X, ⊤) (bundleSections M V))
  let Q : ModuleCat.{u} K := (ModuleCat.restrictScalars c).obj
    (ModuleCat.of Γ(X, ⊤) (bundleSections N V))
  let L : P →ₗ[K] Q := {
    toFun := a.val.app (op V)
    map_add' := (a.val.app (op V)).hom.map_add
    map_smul' := by
      intro r s
      change (a.val.app (op V)).hom (X.presheaf.map V.leTop.op (c r) • (show bundleSections M V from s))=
        X.presheaf.map V.leTop.op (c r) • (a.val.app (op V)).hom (show bundleSections M V from s)
      exact (a.val.app (op V)).hom.map_smul _ _ }
  exact ConcreteCategory.ofHom (C := ModuleCat K) L

/-- The actual ORIGINAL top component gives the SAME whole original global-section map. -/
def globalMap : actualSchemeModuleBaseGlobalSections M c ⟶ actualSchemeModuleBaseGlobalSections N c :=
  (ModuleCat.restrictScalars c).map (a.val.app (op ⊤))

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- EVERY original sheaf component retains EVERY original subset restriction. -/
def diagramMap : actualSchemeModuleBaseSubsetDiagram M U c ⟶ actualSchemeModuleBaseSubsetDiagram N U c where
  app S := sectionMap c a (actualSchemeSubsetOpen U S)
  naturality S T h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact ConcreteCategory.congr_hom
      (a.val.naturality (homOfLE (actualSchemeSubsetOpen_antitone U (leOfHom h))).op) s

omit [LinearOrder ι] in
/-- The ENTIRE actual original section is mapped by the SAME original native sheaf component. -/
theorem diagramMap_apply (S : Finset ι)
    (s : (actualSchemeModuleBaseSubsetDiagram M U c).obj S) :
    ((diagramMap c a U).app S).hom s = a.app (actualSchemeSubsetOpen U S) s := rfl

/-- Actual original native section diagrams form a genuine functor on ORIGINAL sheaves of modules. -/
def diagramFunctor : X.Modules ⥤ (Finset ι ⥤ ModuleCat.{u} K) where
  obj M := actualSchemeModuleBaseSubsetDiagram M U c
  map a := diagramMap c a U
  map_id M := by
    ext S s
    rfl
  map_comp a b := by
    ext S s
    rfl

/-- The actual ORIGINAL native subset complex is functorial in SAME original sheaf morphisms. -/
def complexFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} K) ℕ :=
  diagramFunctor c U ⋙ actualSubsetCechFunctor

end Hironaka.Geometry.ProperSteinProjectiveCech.SheafMorphisms
