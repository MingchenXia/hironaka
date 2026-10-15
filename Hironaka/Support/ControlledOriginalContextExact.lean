/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.GeneralValue

section OriginalStepOneContext

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong
  Hironaka.MaximalOrderStepOneB Hironaka.StepOneRegime
  Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong
  Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction
  Hironaka.TangentDirectionAlong Hironaka.ResolutionDriver
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}


section OffCentre

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The divisor of `J̄` is that of `𝔍`. -/
theorem barMarked_E : (barMarked 𝔍).E = 𝔍.E := rfl

end OffCentre
end
end Hironaka.StepOneValue

end OriginalStepOneContext

section OriginalGeneralContext

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.CompanionReductionAlong Hironaka.CompanionRebase
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen
  Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal
  Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical
  Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong
  Hironaka.MaxOrderValue Hironaka.MonomialCaseAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

section Basic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (𝔪 : MarkedIdeal n X)

/-- The first entry of the general value is the order of the nonmonomial part. -/
theorem genInv_fst {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (genInv M 𝔪 T y)).1 = nmOrd (geoTransformAlong 𝔪 T) y := rfl

end Basic
end
end Hironaka.GeneralValue

end OriginalGeneralContext
