import Hironaka.Resolution.HironakaG8LocalCoeff
import Hironaka.Resolution.HironakaG8ClassStepCut
import Hironaka.Resolution.HironakaG11PresM8EmptyCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Hironaka.HironakaG8CoefficientBoundaryLocal

open Set TopologicalSpace
open Hironaka.HolomorphicIdealSheaves
open Hironaka.BlowupTowers
open Hironaka.MarkedIdeals
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (coeffMarkedAlong)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalCoeff
open Hironaka.HironakaG8ClassStepCut
open Hironaka.HironakaG11PresM8EmptyCore

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

theorem coefficient_local_any_boundary {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) :
    LocWPEquiv P (coeffMarkedAlong P) := by
  let P₀ : MarkedIdeal n X := { P with E := [] }
  have hP₀ : IsInvDomain r P₀ := isInvDomain_withE_of_sublist hP (List.nil_sublist _)
  have h₀ : LocWPEquiv P₀ (coeffMarkedAlong P₀) :=
    locWPEquiv_coeffMarkedAlong_of_nil P₀ hP₀ rfl
  have h := locEquiv_addE (κ := Kinds.wp) rfl h₀ P.E
  simpa [P₀, coeffMarkedAlong, HomogenizedIdealAlong.derivMarkedAlong,
    CoefficientIdeal.msum] using h

end
end Hironaka.HironakaG8CoefficientBoundaryLocal
