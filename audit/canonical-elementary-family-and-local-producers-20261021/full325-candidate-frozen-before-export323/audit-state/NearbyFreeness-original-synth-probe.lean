import TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainCoefficientAlgebra
import TranscendentalNakamaye.Pending.HironakaRelativeNormalCanonicalCentreFreeness

/-! # One true real nonvanishing open for all original nearby normal degrees
Complete two-node mathematics precedes code. Original regularity/coherence
supply actual coefficient quotient domains and every nearby original kernel.
ONE uniform denominator gives ALL degrees on ONE actual open. Canonical centre
actions are independently descended on associated layers, never truncations.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainNearbyFreeness
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainCoefficientAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientPolynomialBaseChange HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalCentreScalars HironakaRelativeNormalCanonicalCentreFreeness
attribute [local instance] coefficientSubalgebraRing

set_option pp.all true
#synth NonAssocRing ℂ
#synth NonAssocCommRing ℂ
#synth NonAssocRing (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)
#synth NonAssocCommRing (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)
#synth Ring (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)
#synth CommRing (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)
#synth SetLike (Subring (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)) (Germ (𝓝 (0 : TranscendentalNakamaye.FirstPass.ComplexModel 1)) ℂ)
end
end TranscendentalNakamaye.Pending.HironakaSmoothCentreRealDomainNearbyFreeness
