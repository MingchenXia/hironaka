import Hironaka.Resolution.HironakaG8CaseTSingleCutCosupport
import Hironaka.Invariant.InvDomainCompanion

/-!
# Case T: the singleton cut is well formed and nonzero at the point

The cut adds an ideal power; the original nonzero germ survives in the sum.
The actual deleted-boundary well-formedness remains an explicit input.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTSingleCutDomain
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  GermIdealOrder DivisorExponentAlong IdealWeightPowers HomogenizedGlueing
  HironakaG8CaseTSingleCut

/-- For a closed submanifold member, the actual singleton exceptional sum is
the corresponding ideal power. -/
theorem singleton_exceptional_sum_eq_power
    {n : ℕ} {X : CMfd.{u} n} (H : Set X) (hH : IsClosedSubmanifold n H) (d : ℕ) :
    finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) d) [H].length =
      idealPow (vanishingIdeal (n := n) H) d := by
  have hPow := GermIdealPullbackCalculus.isCoherent_idealPow
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) d
  exact CoefficientIdeal.finSumIdeal_one hPow

/-- A singleton cut is well formed when the original record is well formed
after deleting that member. -/
theorem isWellFormed_singleCut
    {n : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X) (G : List (Set X))
    (H : Set X) (hH : IsClosedSubmanifold n H)
    (hWA : ({ A with E := G } : MarkedIdeal n X).IsWellFormed) :
    (singleCut A G H).IsWellFormed := by
  have hPow := GermIdealPullbackCalculus.isCoherent_idealPow
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) A.d
  refine ⟨hWA.isClosedSubmanifold_N, ?_, hWA.isSNCDivisor, hWA.isTransverse⟩
  change (RestrictedIdealExtension.sumIdeal A.ideal
    (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d) [H].length)).IsCoherent
  rw [singleton_exceptional_sum_eq_power H hH]
  exact RestrictedIdealExtension.isCoherent_sumIdeal hWA.isCoherent hPow

/-- A witness that the original ideal is nonzero along the carrier at a
point is a witness for the cut sum at that same point. -/
theorem isNonzeroAlongAt_singleCut
    {n : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X) (G : List (Set X))
    (H : Set X) (hI : A.ideal.IsCoherent) {x : X}
    (hx : IsNonzeroAlongAt A.N A.ideal x) :
    IsNonzeroAlongAt (singleCut A G H).N (singleCut A G H).ideal x := by
  exact InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left
    (fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hf) hx

end
end Hironaka.HironakaG8CaseTSingleCutDomain
