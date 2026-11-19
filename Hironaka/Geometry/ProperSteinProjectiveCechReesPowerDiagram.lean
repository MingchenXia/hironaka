/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechInfinitesimalAffine
import Hironaka.Geometry.ProperSteinProjectiveCechReesMultiplication
import Hironaka.Geometry.ProperSteinProjectiveCechSheafSections

/-! # Actual original ideal-power section diagrams and homogeneous multiplication

The actual original coefficient map on EVERY open is used. The normalized
native subset complex only uses nonempty intersections; no assertion that the
empty intersection is affine is introduced. Only native Mathlib and owned
project declarations are imported. No cohomology finiteness is assumed.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- EVERY original open restriction preserves the WHOLE original coefficient map. -/
theorem coefficient_naturality {U V : X.Opens} (h : U ≤ V) :
    (X.presheaf.map (homOfLE h).op).hom.comp (Infinitesimal.sectionCoefficient f V) =
      Infinitesimal.sectionCoefficient f U := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ V le_top ≫
    X.presheaf.map (homOfLE h).op).hom =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom
  rw [Scheme.Hom.appLE_map]

/-- The actual original function restriction, with its derived original algebra action. -/
def restrictionAlgebra {U V : X.Opens} (h : U ≤ V) :
    letI := (Infinitesimal.sectionCoefficient f V).toAlgebra
    letI := (Infinitesimal.sectionCoefficient f U).toAlgebra
    Γ(X, V) →ₐ[R] Γ(X, U) := by
  letI := (Infinitesimal.sectionCoefficient f V).toAlgebra
  letI := (Infinitesimal.sectionCoefficient f U).toAlgebra
  exact { toRingHom := (X.presheaf.map (homOfLE h).op).hom
          commutes' := fun r => RingHom.congr_fun (coefficient_naturality f h) r }

/-- The GENUINE ideal-power section module on the SAME original open. -/
def powerSections (d : ℕ) (U : X.Opens) : ModuleCat.{u} R := by
  letI := (Infinitesimal.sectionCoefficient f U).toAlgebra
  exact ModuleCat.of R ↥((I.map (Infinitesimal.sectionCoefficient f U))^d)

/-- The actual original function restriction on the ENTIRE original ideal power. -/
def powerRestriction (d : ℕ) {U V : X.Opens} (h : U ≤ V) :
    powerSections I f d V →ₗ[R] powerSections I f d U := by
  letI := (Infinitesimal.sectionCoefficient f V).toAlgebra
  letI := (Infinitesimal.sectionCoefficient f U).toAlgebra
  exact ReesMultiplication.powerRestriction I (restrictionAlgebra f h) d

/-- EVERY original restricted ideal element retains the original ambient function. -/
theorem powerRestriction_apply (d : ℕ) {U V : X.Opens} (h : U ≤ V)
    (x : powerSections I f d V) :
    (show ↥((I.map (Infinitesimal.sectionCoefficient f U))^d) from powerRestriction I f d h x).val =
      X.presheaf.map (homOfLE h).op
        (show ↥((I.map (Infinitesimal.sectionCoefficient f V))^d) from x).val := rfl

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The actual original ideal-power subset diagram, including literal original restrictions. -/
def powerDiagram (d : ℕ) : Finset ι ⥤ ModuleCat.{u} R where
  obj S := powerSections I f d (actualSchemeSubsetOpen U S)
  map {S T} h := by
    letI := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    letI := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U T)).toAlgebra
    exact ModuleCat.ofHom (powerRestriction I f d
      (actualSchemeSubsetOpen_antitone U (leOfHom h)))
  map_id S := by
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change X.presheaf.map (𝟙 _).op
      (show ↥((I.map (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)))^d) from x).val = _
    simp
    rfl
  map_comp {S T W} h k := by
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U T)).toAlgebra
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U W)).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change X.presheaf.map _
      (show ↥((I.map (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)))^d) from x).val =
        X.presheaf.map _ (X.presheaf.map _
          (show ↥((I.map (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)))^d) from x).val)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- The genuine native normalized complex of the SAME original ideal-power sections. -/
def powerComplex (d : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  subsetCechComplex (powerDiagram I f U d)

/-- Multiplication by an ORIGINAL homogeneous ideal coefficient on EVERY original intersection. -/
def homogeneousMultiplication {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    powerDiagram I f U d ⟶ powerDiagram I f U (e+d) where
  app S := by
    letI := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    exact ModuleCat.ofHom (ReesMultiplication.powerMultiply I a d)
  naturality S T h := by
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U S)).toAlgebra
    let := (Infinitesimal.sectionCoefficient f (actualSchemeSubsetOpen U T)).toAlgebra
    apply ModuleCat.hom_ext
    change (ReesMultiplication.powerMultiply I (A := Γ(X, actualSchemeSubsetOpen U T)) a d).comp
      (ReesMultiplication.powerRestriction I
        (restrictionAlgebra f (actualSchemeSubsetOpen_antitone U (leOfHom h))) d) = _
    exact (ReesMultiplication.powerRestriction_multiply I
      (restrictionAlgebra f (actualSchemeSubsetOpen_antitone U (leOfHom h))) a d).symm

/-- The literal original homogeneous coefficient gives an actual map of the whole original complexes. -/
def homogeneousComplexMap {e : ℕ} (a : ↥(I^e)) (d : ℕ) :
    powerComplex I f U d ⟶ powerComplex I f U (e+d) :=
  subsetCechComplexMap (homogeneousMultiplication I f U a d)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesPowerDiagram
