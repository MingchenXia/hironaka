/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerDiagram
import Hironaka.Geometry.ProperSteinProjectiveCechPolynomialLocalization
import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange

/-! # SAME original power-zero complex and actual original regular sections

The actual original scalar, original sections and EVERY original restriction
are identified by their WHOLE original coefficient square. No finiteness,
affinity, separatedness, global-surjectivity or comparison certificate.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerZeroSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The WHOLE original global coefficient restricts to EXACTLY the SAME original open coefficient. -/
theorem coefficient_restriction (V : X.Opens) :
    (X.presheaf.map V.leTop.op).hom.comp (ProperGeometricGlobalFunctions.coefficientMap f) =
      Infinitesimal.sectionCoefficient f V := by
  have ht : ProperGeometricGlobalFunctions.coefficientMap f = Infinitesimal.sectionCoefficient f ⊤ := by
    have htop : f.appTop = f.appLE ⊤ ⊤ (by simp) := by
      simpa only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top] using f.app_eq_appLE (U := ⊤)
    unfold ProperGeometricGlobalFunctions.coefficientMap Infinitesimal.sectionCoefficient
    rw [htop]
    rfl
  rw [ht]
  exact ReesPowerDiagram.coefficient_naturality f (show V≤⊤ from le_top)

/-- The actual native original unit-section module with its SAME original coefficient action. -/
def unitSections (V : X.Opens) : ModuleCat.{u} R := by
  let := localSectionsGlobalModule (SheafOfModules.unit X.ringCatSheaf) V
  exact (ModuleCat.restrictScalars (ProperGeometricGlobalFunctions.coefficientMap f)).obj
    (ModuleCat.of Γ(X, ⊤) (bundleSections (SheafOfModules.unit X.ringCatSheaf) V))

/-- EVERY original unit section is the SAME whole original section in the ORIGINAL zeroth ideal power. -/
def sectionEquiv (V : X.Opens) :
    unitSections f V ≃ₗ[R] ReesPowerDiagram.powerSections I f 0 V := by
  let := localSectionsGlobalModule (SheafOfModules.unit X.ringCatSheaf) V
  let := (Infinitesimal.sectionCoefficient f V).toAlgebra
  exact {
    toFun := fun s => ⟨(show Γ(X, V) from s), by simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]⟩
    invFun := fun s => (show ↥((I.map (Infinitesimal.sectionCoefficient f V))^0) from s).val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r s
      apply Subtype.ext
      change X.presheaf.map V.leTop.op (ProperGeometricGlobalFunctions.coefficientMap f r) * (show Γ(X, V) from s) =
        Infinitesimal.sectionCoefficient f V r * (show Γ(X, V) from s)
      exact congrArg (fun c => c*(show Γ(X, V) from s)) (RingHom.congr_fun (coefficient_restriction f V) r) }

/-- The original entire section value is LITERALLY unchanged by the genuine original power-zero frame. -/
theorem sectionEquiv_apply (V : X.Opens) (s : unitSections f V) :
    (show ↥((I.map (Infinitesimal.sectionCoefficient f V))^0) from sectionEquiv I f V s).val =
      (show Γ(X, V) from s) := rfl

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The SAME ENTIRE native original regular-section diagram is the genuine original zeroth-power diagram. -/
def diagramIso :
    actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf) U
        (ProperGeometricGlobalFunctions.coefficientMap f) ≅
      ReesPowerDiagram.powerDiagram I f U 0 :=
  NatIso.ofComponents (fun S => (sectionEquiv I f (actualSchemeSubsetOpen U S)).toModuleIso) (by
    intro S T h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    rfl)

/-- The ENTIRE actual original native structure-sheaf complex has its SAME original power-zero sections and restrictions. -/
def complexIso :
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf) U
        (ProperGeometricGlobalFunctions.coefficientMap f)) ≅
      ReesPowerDiagram.powerComplex I f U 0 :=
  (actualSubsetCechFunctor (K := R) (I := ι)).mapIso (diagramIso I f U)

/-- ACTUAL original sheaf gluing identifies original global sections with SAME original power-zero native H0. -/
def globalHomologyIso (hU : iSup U=⊤) :
    actualSchemeModuleBaseGlobalSections (SheafOfModules.unit X.ringCatSheaf)
        (ProperGeometricGlobalFunctions.coefficientMap f) ≅
      (ReesPowerDiagram.powerComplex I f U 0).homology 0 :=
  actualSchemeModuleBaseGlobalHomologyIso (SheafOfModules.unit X.ringCatSheaf) U
      (ProperGeometricGlobalFunctions.coefficientMap f) hU ≪≫
    HomologicalComplex.homologyMapIso (complexIso I f U) 0

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerZeroSections
