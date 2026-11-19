import Hironaka.Resolution.HironakaG8CaseNOrderComparison

/-!
# Case N: comparison from the original native local relation

The projected local relation and projected SNC condition are constructed
from the original records and original boundary. The ambient records here
have empty native boundaries; the original finite boundary is supplied as
an ordered prefix and no transversality to either carrier is assumed.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNNativeComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  DivisorExponentAlong GermIdealOrder HironakaActualProjectionTestRecord
  HironakaG8P1ArcPair HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

/-- For empty-boundary native records, original local equivalence and the
original SNC boundary supply the projection hypotheses of the one-sided
Case N comparison. -/
theorem order_le_of_local_equiv_and_notTangent
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEA : A.E = []) (hEB : B.E = []) (hdim : SameCarrierDim A B)
    {x : X} (hx : x ∈ A.cosupp) (hd : B.d = A.d)
    (F : List (Set X)) (hClosed : ∀ H ∈ F, IsClosed H)
    (hNotTangent : ∀ H ∈ F, x ∈ H →
      x ∉ cosupport n A.N (vanishingIdeal (n := n) H) 2)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x)
    (hLocal : LocWPEquiv ({ A with E := F } : MarkedIdeal n X)
      ({ B with E := F } : MarkedIdeal n X))
    (hSNC : IsSNCDivisor n F) :
    ordinaryTraceOrder B.N B.ideal x ≤ ordinaryTraceOrder A.N A.ideal x := by
  have hpA : projectionTest ({ A with E := F } : MarkedIdeal n X) =
      ({ (projectionTest A) with E := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest A).E } :
        MarkedIdeal (n+1) (projectionAmbient X)) := by
    simp [projectionTest, hEA]
    rfl
  have hpB : projectionTest ({ B with E := F } : MarkedIdeal n X) =
      ({ (projectionTest B) with E := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest B).E } :
        MarkedIdeal (n+1) (projectionAmbient X)) := by
    simp [projectionTest, hEB]
    rfl
  have hProjected := locWPEquiv_projectionTest hLocal
  rw [hpA, hpB] at hProjected
  have hProjectedSNC := HironakaG8ClassStepCut.isSNCDivisor_projectionTest
    (A := ({ A with E := F } : MarkedIdeal n X)) hSNC
  rw [hpA] at hProjectedSNC
  exact HironakaG8CaseNOrderComparison.order_le_of_projected_local_equiv_and_notTangent
    A B hA hB (hEB.trans hEA.symm) hdim hx hd F hClosed hNotTangent hgreater
    hProjected hProjectedSNC

end
end Hironaka.HironakaG8CaseNNativeComparison
