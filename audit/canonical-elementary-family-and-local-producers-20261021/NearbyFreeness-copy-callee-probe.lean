/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainCoefficientAlgebra
import Hironaka.Resolution.HironakaRelativeNormalCanonicalCentreFreeness

/-! # One true real nonvanishing open for all original nearby normal degrees
Complete two-node mathematics precedes code. Original regularity/coherence
supply actual coefficient quotient domains and every nearby original kernel.
ONE uniform denominator gives ALL degrees on ONE actual open. Canonical centre
actions are independently descended on associated layers, never truncations.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainNearbyFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainCoefficientAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalCoefficientPolynomialBaseChange HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaRelativeNormalCentreScalars HironakaRelativeNormalCanonicalCentreFreeness
attribute [local instance] coefficientSubalgebraRing

set_option pp.all true
#print holGermSubring
#print HolGerm
#print coefficientGermHom
#print coefficientOriginKernel
end
end Hironaka.HironakaSmoothCentreRealDomainNearbyFreeness
