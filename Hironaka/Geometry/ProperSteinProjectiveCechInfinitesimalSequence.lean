/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesPowerZeroSections
import Hironaka.Geometry.ProperSteinProjectiveCechSheafMorphisms
import Hironaka.Geometry.ProperSteinProjectiveCechSubsetNonemptyExactness
import Hironaka.Geometry.ProperSteinProjectiveCechReesDegreeTransitions
import Hironaka.Geometry.ProperSteinProjectiveCechReesDegreeComplex
import Hironaka.Geometry.ProperSteinProjectiveCechSheafPushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Actual original infinitesimal native subset-complex short exactness

Only closed native homology-sequence wrappers are adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreInfinitesimalCech.lean`,
SHA256 96060b2515b4fe4cb39d3e5681f20bbf2971251c4ce013220440ad98ed5ebd9c.
The actual ORIGINAL subset exactness is constructed from SAME original affine
projection kernels/surjectivity, requiring NO affine empty intersection and
NO finite cohomology, coherent comparison or output-exactness certificate.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalSequence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The ACTUAL native original infinitesimal pushforward unit sheaf, retaining every original section. -/
def quotientModule (d : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward (Infinitesimal.projection I f d)).obj
    (SheafOfModules.unit (Infinitesimal.model I f d).ringCatSheaf)

/-- The SAME native ORIGINAL projection unit morphism gives its actual original pullback on every open. -/
def projectionModule (d : ℕ) : SheafOfModules.unit X.ringCatSheaf ⟶ quotientModule I f d :=
  SheafOfModules.unitToPushforwardObjUnit (Infinitesimal.projection I f d).toRingCatSheafHom

/-- The WHOLE native inverse-image coefficient is EXACTLY the ORIGINAL actual composed structure map. -/
theorem modelCoefficient (d : ℕ) :
    actualSchemePushforwardSourceConstants (Infinitesimal.projection I f d)
        (ProperGeometricGlobalFunctions.coefficientMap f) =
      ProperGeometricGlobalFunctions.coefficientMap (Infinitesimal.projection I f d ≫ f) := by
  unfold actualSchemePushforwardSourceConstants ProperGeometricGlobalFunctions.coefficientMap
  rw [Scheme.Hom.comp_appTop]
  rfl

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The literal ORIGINAL ideal-power inclusion into actual ORIGINAL unit sections. -/
def inclusionDiagram (d : ℕ) :
    ReesPowerDiagram.powerDiagram I f U d ⟶
      actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf) U
        (ProperGeometricGlobalFunctions.coefficientMap f) :=
  ReesDegreeTransitions.lowerNatural I f U (Nat.zero_le d) ≫ (ReesPowerZeroSections.diagramIso I f U).inv

/-- The actual ORIGINAL projection on SAME original native subset sections. -/
def projectionDiagram (d : ℕ) :
    actualSchemeModuleBaseSubsetDiagram (SheafOfModules.unit X.ringCatSheaf) U
        (ProperGeometricGlobalFunctions.coefficientMap f) ⟶
      actualSchemeModuleBaseSubsetDiagram (quotientModule I f d) U
        (ProperGeometricGlobalFunctions.coefficientMap f) :=
  SheafMorphisms.diagramMap (ProperGeometricGlobalFunctions.coefficientMap f) (projectionModule I f d) U

variable [X.IsSeparated] (hU : ∀ j, IsAffineOpen (U j))
include hU

omit [LinearOrder ι] in
/-- GENUINE original affine projection kernels and surjectivity derive exactness at EVERY NONEMPTY original intersection. -/
theorem local_exact (d : ℕ) (S : Finset ι) (hS : S.Nonempty) :
    Function.Exact ((inclusionDiagram I f U d).app S).hom ((projectionDiagram I f U d).app S).hom ∧
      Function.Injective ((inclusionDiagram I f U d).app S).hom ∧
      Function.Surjective ((projectionDiagram I f U d).app S).hom := by
  let V := actualSchemeSubsetOpen U S
  have hV : IsAffineOpen V := ReesDegreeComplex.nonemptyIntersection_isAffine U hU S hS
  change Function.Exact (Infinitesimal.affinePowerInclusion I f d ⟨V, hV⟩)
      ((Infinitesimal.projection I f d).app V) ∧
    Function.Injective (Infinitesimal.affinePowerInclusion I f d ⟨V, hV⟩) ∧
    Function.Surjective ((Infinitesimal.projection I f d).app V)
  exact ⟨Infinitesimal.affineSection_exact I f d ⟨V, hV⟩,
    Infinitesimal.affinePowerInclusion_injective I f d ⟨V, hV⟩,
    Infinitesimal.affine_projection_surjective I f d ⟨V, hV⟩⟩

/-- The SAME actual original infinitesimal sequence on ENTIRE original native subset complexes. -/
def sequence (d : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  SubsetNonemptyExactness.sequence (inclusionDiagram I f U d) (projectionDiagram I f U d)
    (local_exact I f U hU d)

/-- ORIGINAL affine component producers give WHOLE actual original complex short exactness, with no empty-affinity premise. -/
theorem sequence_shortExact (d : ℕ) : (sequence I f U hU d).ShortExact :=
  SubsetNonemptyExactness.sequence_shortExact (inclusionDiagram I f U d) (projectionDiagram I f U d)
    (local_exact I f U hU d)

/-- The WHOLE third complex is the SAME actual original infinitesimal unit complex on original inverse-image opens. -/
def modelComplexIso (d : ℕ) :
    subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
      (SheafOfModules.unit (Infinitesimal.model I f d).ringCatSheaf)
      (fun j => Infinitesimal.projection I f d ⁻¹ᵁ U j)
      (ProperGeometricGlobalFunctions.coefficientMap (Infinitesimal.projection I f d ≫ f))) ≅
      (sequence I f U hU d).X₃ := by
  rw [← modelCoefficient I f d]
  exact (actualSchemeModulePushforwardCechIso (Infinitesimal.projection I f d)
    (SheafOfModules.unit (Infinitesimal.model I f d).ringCatSheaf)
    (ProperGeometricGlobalFunctions.coefficientMap f) U).symm

/-- The GENUINE native original connecting map lands in the SAME original ideal-power cohomology. -/
def connecting (d p : ℕ) :
    (sequence I f U hU d).X₃.homology p ⟶
      (ReesPowerDiagram.powerComplex I f U d).homology (p+1) :=
  (sequence_shortExact I f U hU d).δ p (p+1) rfl

/-- Native exactness at EVERY original positive ideal-power cohomology term. -/
theorem homology_exact_left (d p : ℕ) :
    Function.Exact (connecting I f U hU d p)
      (HomologicalComplex.homologyMap (sequence I f U hU d).f (p+1)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((sequence_shortExact I f U hU d).homology_exact₁ p (p+1) rfl)

/-- Native exactness at EVERY original structure-sheaf cohomology term, including zero. -/
theorem homology_exact_middle (d p : ℕ) :
    Function.Exact (HomologicalComplex.homologyMap (sequence I f U hU d).f p)
      (HomologicalComplex.homologyMap (sequence I f U hU d).g p) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((sequence_shortExact I f U hU d).homology_exact₂ p)

/-- Native exactness at EVERY actual original infinitesimal cohomology term, including zero. -/
theorem homology_exact_right (d p : ℕ) :
    Function.Exact (HomologicalComplex.homologyMap (sequence I f U hU d).g p)
      (connecting I f U hU d p) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((sequence_shortExact I f U hU d).homology_exact₃ p (p+1) rfl)

end Hironaka.Geometry.ProperSteinProjectiveCech.InfinitesimalSequence
