import Hironaka.Resolution.HironakaG8CaseNArcComparison

/-!
# Case N: one-sided original order inequality

The actual sharp arc point compares the original ordinary orders when the
marks agree. The projected local relation and its SNC boundary remain
explicit hypotheses.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNOrderComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupConstruction BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder ordinaryTraceOrder_cosupport_iff)
open scoped Hironaka.ProductComplexManifold

/-- The natural order-two avoidance condition on the A side yields the
original one-sided order inequality, under the retained projected relation. -/
theorem order_le_of_projected_local_equiv_and_notTangent
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (hd : B.d = A.d)
    (F : List (Set X)) (hClosed : ∀ H ∈ F, IsClosed H)
    (hNotTangent : ∀ H ∈ F, x ∈ H →
      x ∉ cosupport n A.N (vanishingIdeal (n := n) H) 2)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x)
    (hLocal : LocWPEquiv
      ({ (projectionTest A) with E := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest A).E } :
        MarkedIdeal (n+1) (projectionAmbient X))
      ({ (projectionTest B) with E := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest B).E } :
        MarkedIdeal (n+1) (projectionAmbient X)))
    (hSNC : IsSNCDivisor (n+1)
      (F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest A).E)) :
    ordinaryTraceOrder B.N B.ideal x ≤ ordinaryTraceOrder A.N A.ideal x := by
  obtain ⟨hπ1, S, _hS, hStages⟩ :=
    HironakaG8CaseNArcComparison.exists_arcFamily_with_sharp_point_and_normalized_order_eq
      A B hA hB hEB hdim hx F hClosed hNotTangent hgreater hLocal hSNC
  obtain ⟨facts, hPoints⟩ := hStages A.d (Nat.le_succ A.d)
  obtain ⟨y, _hyU, hyA, hyHigh, hyB, _hyOff, hOrder⟩ :=
    hPoints Set.univ Filter.univ_mem
  let T := (arcA1 x hπ1).append (S A.d).R
  let PA := geoTransformAlong (projectionTest A) T
  let PB := geoTransformAlong (projectionTest B) T
  have hDA : IsInvDomain (kA+1) PA := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain A hA) T facts.testA
  have hDB : IsInvDomain (kB+1) PB := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain B hB) T facts.testB
  have hyBCos : y ∈ PB.cosupp := facts.cosupp_eq ▸ hyA
  have hMark : PB.d = PA.d := by
    change (geoTransformAlong (projectionTest B) T).d =
      (geoTransformAlong (projectionTest A) T).d
    rw [d_geoTransformAlong, d_geoTransformAlong]
    exact hd
  change PB.d * ordinaryTraceOrder PA.N PA.ideal y =
    PA.d * ordinaryTraceOrder PB.N PB.ideal y at hOrder
  rw [hMark] at hOrder
  have hOrders : ordinaryTraceOrder PA.N PA.ideal y = ordinaryTraceOrder PB.N PB.ideal y :=
    Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hDA.one_le_d) hOrder
  have hCutB : (A.d+1) * (ordinaryTraceOrder B.N B.ideal x - B.d) ≤
      ordinaryTraceOrder PB.N PB.ideal y := by
    apply (ordinaryTraceOrder_cosupport_iff (W := PB.N) (I := PB.ideal)
      hDB.isWellFormed.isClosedSubmanifold_N hDB.isWellFormed.isCoherent
      hDB.isNonzeroAlongAt (PB.cosupp_subset_N hyBCos) _).mp
    exact hyB
  have hCutA : ¬ (A.d+1) * (ordinaryTraceOrder A.N A.ideal x - A.d) + 1 ≤
      ordinaryTraceOrder PA.N PA.ideal y := by
    intro hLe
    apply hyHigh
    exact (ordinaryTraceOrder_cosupport_iff (W := PA.N) (I := PA.ideal)
      hDA.isWellFormed.isClosedSubmanifold_N hDA.isWellFormed.isCoherent
      hDA.isNonzeroAlongAt (PA.cosupp_subset_N hyA) _).mpr hLe
  have hMul : (A.d+1) * (ordinaryTraceOrder B.N B.ideal x - B.d) ≤
      (A.d+1) * (ordinaryTraceOrder A.N A.ideal x - A.d) := by omega
  have hDiff : ordinaryTraceOrder B.N B.ideal x - B.d ≤
      ordinaryTraceOrder A.N A.ideal x - A.d :=
    Nat.le_of_mul_le_mul_left hMul (Nat.zero_lt_succ A.d)
  omega

end
end Hironaka.HironakaG8CaseNOrderComparison
