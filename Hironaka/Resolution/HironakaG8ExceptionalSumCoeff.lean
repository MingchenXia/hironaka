import Hironaka.Resolution.HironakaG8ExceptionalSumCompare

/-! # Exceptional-sum exponents from truncated coefficient exponents -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ExceptionalSumCoeff
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder DivisorExponentAlong HironakaG11InvBMLower
  HironakaG8ExceptionalSumCompare
open RestrictedIdealExtension (sumIdeal)

variable {n : ℕ} {Y : CMfd.{0} n}

/-- For nonzero coefficient ideals, their exponent equality below the mark
and the common geometric trace condition give exponent equality below the
mark for the coefficient-plus-exceptional sums. -/
theorem sum_exp_below_eq_of_coeff_exp_and_trace
    {N N' H : Set Y} {C C' : GermIdeal n Y} {S : List (Set Y)}
    (hS : ∀ D ∈ S, IsClosed D) {δ : ℕ}
    (hC : C.IsCoherent) (hC' : C'.IsCoherent)
    (hE : (exceptionalTermBM (n := n) S δ).IsCoherent)
    {y : Y} {r r' : Y → Y} (hr : IsLocalRetraction n N r y)
    (hr' : IsLocalRetraction n N' r' y) (hyH : y ∈ H)
    (hc : IsNonzeroAlongAt N C y) (hc' : IsNonzeroAlongAt N' C' y)
    (hcoeff : min (divExpAlong n N C H y) δ = min (divExpAlong n N' C' H y) δ)
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ S, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ N' → z ∈ H → ∀ D ∈ S, z ∈ D)) :
    min (divExpAlong n N (sumIdeal C (exceptionalTermBM S δ)) H y) δ =
      min (divExpAlong n N' (sumIdeal C' (exceptionalTermBM S δ)) H y) δ := by
  have holC := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hC
  have holC' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hC'
  have hnz := InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left (𝔠 := exceptionalTermBM S δ) holC hc
  have hnz' := InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left (𝔠 := exceptionalTermBM S δ) holC' hc'
  apply sum_exp_below_eq_of_trace hS hC hC' hE hr hr' hyH hnz hnz' ?_ htrace
  intro e he
  rw [isDivNearAlong_iff_le_divExpAlong hr hyH hc holC,
    isDivNearAlong_iff_le_divExpAlong hr' hyH hc' holC']
  omega

end
end Hironaka.HironakaG8ExceptionalSumCoeff
