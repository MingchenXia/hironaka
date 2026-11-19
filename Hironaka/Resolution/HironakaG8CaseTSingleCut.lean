import Hironaka.Resolution.HironakaG8CaseSplitAfterN
import Hironaka.Resolution.HironakaG8ClassStepCut

/-!
# Case T: local equivalence after cutting one boundary member

This is the literal singleton application of Step I.B. Well-formedness of
the remainder for each carrier is an explicit input and is not inferred from
ambient SNC alone.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTSingleCut
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG8LocalHistory HironakaG8LocalExcSum HironakaG8ClassStepCut
  HomogenizedGlueing IdealWeightPowers

/-- The Step I.B cut of one member, retaining the ordered remainder. -/
def singleCut {n : ℕ} {X : CMfd.{u} n} (A : MarkedIdeal n X)
    (G : List (Set X)) (H : Set X) : MarkedIdeal n X :=
  ⟨A.N, G, RestrictedIdealExtension.sumIdeal A.ideal
    (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) ([H].getD i ∅)) A.d) [H].length), A.d⟩

/-- The cut records are locally equivalent, provided deleting the selected
member leaves well-formed records for both original carriers. -/
theorem locWPEquiv_singleCut
    {n : ℕ} {X : CMfd.{u} n} (A B : MarkedIdeal n X)
    (G : List (Set X)) (H : Set X)
    (h : LocWPEquiv A B) (hE : A.E = [H] ++ G)
    (hSNC : IsSNCDivisor n A.E) (hH : IsClosedSubmanifold n H)
    (hWA : ({ A with E := G } : MarkedIdeal n X).IsWellFormed)
    (hWB : ({ B with E := G } : MarkedIdeal n X).IsWellFormed)
    (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d) :
    LocWPEquiv (singleCut A G H) (singleCut B G H) := by
  refine locEquiv_of_cutRel rfl ⟨A, B, [H], [H], h, ?_, hSNC, ?_, ?_, hWA, hWB, hdA, hdB, ?_, ?_⟩
  · exact hE
  · intro K hK
    exact Or.inl hK
  · intro K hK
    simp only [List.mem_singleton] at hK
    subst K
    exact hH
  · exact excRel_sumIdeal ({ A with E := G } : MarkedIdeal n X) hWA.isCoherent [H]
  · exact excRel_sumIdeal ({ B with E := G } : MarkedIdeal n X) hWB.isCoherent [H]

end
end Hironaka.HironakaG8CaseTSingleCut
