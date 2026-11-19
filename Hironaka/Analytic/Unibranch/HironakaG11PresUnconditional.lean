import Hironaka.Analytic.Unibranch.HironakaG11PresFinal
import Hironaka.Resolution.HironakaG8ResidualSuccClosure

/-! The positive-dimensional residual closes the padded-family input,
including the zero-dimensional base, and hence the compact G11 endpoint. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.HironakaG11PresUnconditional
open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
open HironakaG11PresReduction HironakaG11SingularCentreModification HironakaG11PresFinal

/-- The residual input holds in every required dimension and level. -/
theorem padFamilyResidualInputs : PadFamilyResidualInputs := by
  intro N k hk
  exact HironakaG8ResidualSuccClosure.lowerExpResidualStepBM_actual (Nat.zero_lt_of_lt hk) (k+1)

/-- Class-functorial resolution invariants exist in every dimension. -/
theorem classFunctorialInvariants : ClassFunctorialInvariants :=
  classFunctorialInvariants_of_residualInputs padFamilyResidualInputs

/-- Every compact reduced complex space has a resolution by finitely many
blowups with smooth centres in the singular loci. -/
theorem compactSingularCentreResolution : CompactSingularCentreResolution :=
  compactSingularCentreResolution_of_residualInputs padFamilyResidualInputs

/-- The full compact resolution endpoint. -/
theorem exists_endpoint (X : SourceReducedComplexSpace) (hX : CompactSpace X.obj.left) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) :=
  exists_endpoint_of_residualInputs padFamilyResidualInputs X hX
end Hironaka.Analytic.Unibranch.HironakaG11PresUnconditional
