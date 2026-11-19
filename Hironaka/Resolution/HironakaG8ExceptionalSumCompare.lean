import Hironaka.Resolution.HironakaG8ExceptionalDivisibility
import Hironaka.Resolution.HironakaG8ClassStepHistory

/-! # Truncated exponents of coefficient-plus-exceptional sums

Comparison below the mark reduces to the coefficient divisibilities and the
geometry of the traces in the original members.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ExceptionalSumCompare
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder DivisorExponentAlong HironakaG11InvBMLower
  HironakaG8ExceptionalDivisibility HironakaG8SumExponents HironakaG8ClassStepHistory
open RestrictedIdealExtension (sumIdeal)

variable {n : ℕ} {Y : CMfd.{0} n}

/-- Below the mark, agreement for the coefficient terms and for the trace
condition gives agreement for the sums' divisibility predicates. -/
theorem sum_divisible_below_iff_of_trace
    {N N' H : Set Y} {C C' : GermIdeal n Y} {S : List (Set Y)}
    (hS : ∀ D ∈ S, IsClosed D) {δ : ℕ}
    (hC : ∀ x g, C.mem x g → HolomorphicAt n g x)
    (hC' : ∀ x g, C'.mem x g → HolomorphicAt n g x)
    (hE : ∀ x g, (exceptionalTermBM (n := n) S δ).mem x g → HolomorphicAt n g x)
    (y : Y)
    (hcoeff : ∀ e ≤ δ, IsDivNearAlong n N C H e y ↔ IsDivNearAlong n N' C' H e y)
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ S, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ N' → z ∈ H → ∀ D ∈ S, z ∈ D))
    (e : ℕ) (heδ : e ≤ δ) :
    IsDivNearAlong n N (sumIdeal C (exceptionalTermBM S δ)) H e y ↔
      IsDivNearAlong n N' (sumIdeal C' (exceptionalTermBM S δ)) H e y := by
  rw [isDivNearAlong_sumIdeal_iff hC hE, isDivNearAlong_sumIdeal_iff hC' hE, hcoeff e heδ]
  by_cases he : e = 0
  · subst e
    exact and_congr_right fun _ => ⟨fun _ => isDivNearAlong_zero hE y,
      fun _ => isDivNearAlong_zero hE y⟩
  · have hepos : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    exact and_congr_right fun _ =>
      (exceptionalTerm_divisible_below_iff_trace hS hepos heδ y).trans
        (htrace.trans (exceptionalTerm_divisible_below_iff_trace hS hepos heδ y).symm)

/-- Under nonvanishing on both carriers, trace and coefficient comparison
give equality of the exponents truncated at the common mark. -/
theorem sum_exp_below_eq_of_trace
    {N N' H : Set Y} {C C' : GermIdeal n Y} {S : List (Set Y)}
    (hS : ∀ D ∈ S, IsClosed D) {δ : ℕ}
    (hC : C.IsCoherent) (hC' : C'.IsCoherent)
    (hE : (exceptionalTermBM (n := n) S δ).IsCoherent)
    {y : Y} {r r' : Y → Y} (hr : IsLocalRetraction n N r y)
    (hr' : IsLocalRetraction n N' r' y) (hyH : y ∈ H)
    (hnz : IsNonzeroAlongAt N (sumIdeal C (exceptionalTermBM S δ)) y)
    (hnz' : IsNonzeroAlongAt N' (sumIdeal C' (exceptionalTermBM S δ)) y)
    (hcoeff : ∀ e ≤ δ, IsDivNearAlong n N C H e y ↔ IsDivNearAlong n N' C' H e y)
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → ∀ D ∈ S, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ N' → z ∈ H → ∀ D ∈ S, z ∈ D)) :
    min (divExpAlong n N (sumIdeal C (exceptionalTermBM S δ)) H y) δ =
      min (divExpAlong n N' (sumIdeal C' (exceptionalTermBM S δ)) H y) δ := by
  have holC := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hC
  have holC' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hC'
  have holE := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hE
  have holSum := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent
    (RestrictedIdealExtension.isCoherent_sumIdeal hC hE)
  have holSum' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent
    (RestrictedIdealExtension.isCoherent_sumIdeal hC' hE)
  exact min_divExpAlong_eq_of_iff hr hr' hyH hnz hnz' holSum holSum' δ
    (fun e he => sum_divisible_below_iff_of_trace hS holC holC' holE y hcoeff htrace e he)

end
end Hironaka.HironakaG8ExceptionalSumCompare
