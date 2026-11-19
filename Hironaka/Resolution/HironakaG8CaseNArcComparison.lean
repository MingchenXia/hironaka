import Hironaka.Resolution.HironakaG8CaseNGenericPoint
import Hironaka.Resolution.HironakaG8CaseNPrefixRestriction

/-!
# Case N: comparing orders at an actual sharp arc point

The sharp point is selected by the native arc construction. The comparison
uses the retained local relation at its actual tower and drops only the
original strict prefix. This is a step toward Case N, not the full theorem.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseNArcComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupConstruction BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

/-- Under the native pair hypotheses and the retained projected local
relation, an actual sharp point off the old boundary has equal normalized
orders for the two native stage records. -/
theorem exists_arcFamily_with_sharp_point_and_normalized_order_eq
    {n kA kB : ℕ} {X : CMfd.{u} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
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
    ∃ (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
      (S : ℕ → ArcStage n (arcY1 x)), IsArcFamily x hπ1 S ∧
      ∀ r, A.d ≤ r+1 →
        ∃ _facts : ArcPairStageFacts A B
          ({ (projectionTest A) with E := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ (projectionTest A).E } :
              MarkedIdeal (n+1) (projectionAmbient X))
          ((arcA1 x hπ1).append (S r).R) (S r).z x r,
        ∀ O : Set (S r).Z, O ∈ 𝓝 (S r).z →
        ∃ y ∈ O,
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).cosupp ∧
          y ∉ cosupport (n+1)
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).ideal
            ((r+1) * (ordinaryTraceOrder A.N A.ideal x - A.d) + 1) ∧
          y ∈ cosupport (n+1)
            (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).N
            (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).ideal
            ((r+1) * (ordinaryTraceOrder B.N B.ideal x - B.d)) ∧
          (∀ H ∈ F, y ∉ strictAlong ((arcA1 x hπ1).append (S r).R)
            ((Prod.fst : projectionAmbient X → X) ⁻¹' H)) ∧
          (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).d *
            ordinaryTraceOrder
              (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N
              (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).ideal y =
          (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).d *
            ordinaryTraceOrder
              (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).N
              (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).ideal y := by
  let Fp := F.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·)
  let A' : MarkedIdeal (n+1) (projectionAmbient X) :=
    { (projectionTest A) with E := Fp ++ (projectionTest A).E }
  let B' : MarkedIdeal (n+1) (projectionAmbient X) :=
    { (projectionTest B) with E := Fp ++ (projectionTest B).E }
  have hsA : SameNID (projectionTest A) A' := ⟨rfl, rfl, rfl⟩
  have hsB : SameNID (projectionTest B) B' := ⟨rfl, rfl, rfl⟩
  have hLoc : LocWPEquiv A' B' := hLocal
  obtain ⟨hπ1, S, hS, hStages⟩ :=
    HironakaG8CaseNGenericPoint.exists_arcFamily_with_sharp_point_off_original_members
      A B hA hB hEB hdim hx A' B' hsA hsB hLoc.wEquiv hSNC hgreater F hClosed hNotTangent
  refine ⟨hπ1, S, hS, ?_⟩
  intro r hr
  obtain ⟨facts, hPoints⟩ := hStages r hr
  refine ⟨facts, ?_⟩
  intro O hO
  obtain ⟨y, hyO, _hyTrace, hyA, hyHigh, hyB, hyOff⟩ := hPoints O hO
  refine ⟨y, hyO, hyA, hyHigh, hyB, hyOff, ?_⟩
  let T := (arcA1 x hπ1).append (S r).R
  have hDA := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain A hA) T facts.testA
  have hDB := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain B hB) T facts.testB
  have hClosedFp : ∀ H ∈ Fp, IsClosed H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact (hClosed H₀ hH₀).preimage continuous_fst
  have hOffFp : ∀ H ∈ Fp, y ∉ strictAlong T H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact hyOff H₀ hH₀
  exact HironakaG8CaseNPrefixRestriction.normalized_order_eq_at_stage_off_original_prefix
    (projectionTest A) (projectionTest B) Fp hClosedFp hLoc T facts.testA'
    hDA hDB facts.boundary_eq.symm facts.sameCarrierDim hyA hOffFp

end
end Hironaka.HironakaG8CaseNArcComparison
