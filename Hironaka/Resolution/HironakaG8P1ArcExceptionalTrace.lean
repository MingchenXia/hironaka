import Hironaka.Resolution.HironakaG8P1ArcPairTrace
import Hironaka.Invariant.MemberInterAlong

set_option autoImplicit false

/-!
# The actual last arc divisor and the common native carrier trace

The literal last boundary member of a positive-length tower is its final
exceptional preimage. Avoidance of an original open forces it to project
outside that open. On the actual point-arc family this proves that the
common last divisor lies over parameter zero.

At a common arc-pair stage whose count reaches the mark, equality of
cosupports gives a germ inclusion of the two native carrier traces on that
divisor. Their native transversality and equal dimension give germ equality
by the existing filling theorem. The original order-greater-than-mark
hypothesis and the chosen stage size derive the count bound internally.

These are point-arc trace statements. They do not assert the directrix/order
comparison or the general-centre birth-chart result for case (r1).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcExceptionalTrace

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings DivisorExponentAlong RestrictEmptyTower MemberInterAlong
  BlowupFlatCoordinates HomogenizedGlueingTower
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower HironakaG8P1ArcPair
  HironakaG8P1ArcPairTrace

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-- The literal last native member is the exceptional preimage of the final
centre. If every actual centre avoids an original open, it lies outside
that open after projection. Positive tower length is essential. -/
theorem last_member_projects_outside_preserved_open
    {m : ℕ} {Y Z : CMfd.{u} m} (M : MarkedIdeal m Y) (O : Opens Y)
    (T : BlowupTower Y Z) (hAvoid : CentresAvoid O T) (hpos : 0 < T.length)
    (hne : (geoTransformAlong M T).E ≠ []) :
    ∀ y ∈ (geoTransformAlong M T).E.getLast hne, T.proj y ∉ (O : Set Y) := by
  cases T with
  | refl => simp only [BlowupTower.length_refl, Nat.lt_irrefl] at hpos
  | @step Z₀ Z T C π hπ =>
      have hLast : (geoTransformAlong M (.step T C π hπ)).E.getLast hne = π ⁻¹' C := by
        change (((geoTransformAlong M T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C)) ++
          [π ⁻¹' C]).getLast _ = π ⁻¹' C
        exact List.getLast_concat
      intro y hy hyO
      rw [hLast] at hy
      exact Set.disjoint_left.mp hAvoid.2 hy hyO

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual last native divisor at every point-arc stage lies over the
original zero-parameter hyperplane. It is not a supplied chart condition. -/
theorem last_parameter_zero_of_arcFamily
    (M : MarkedIdeal n X) {x : X}
    {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {S : ℕ → ArcStage n (arcY1 x)} (hS : IsArcFamily x hπ1 S) (r : ℕ)
    (hne : (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E ≠ []) :
    ∀ y ∈ (geoTransformAlong (projectionTest M) ((arcA1 x hπ1).append (S r).R)).E.getLast hne,
      (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0 := by
  have hpos : 0 < ((arcA1 x hπ1).append (S r).R).length := by
    rw [BlowupTower.length_append]
    change 0 < 1 + (S r).R.length
    omega
  have hAvoid := HironakaG8P1ArcOffHorizontal.centresAvoid_offHorizontal_arcFamily hS r
  intro y hy
  have hn := last_member_projects_outside_preserved_open (projectionTest M)
    (HironakaG8P1ArcOffHorizontal.offHorizontal X) ((arcA1 x hπ1).append (S r).R)
    hAvoid hpos hne y hy
  change ¬ ((((arcA1 x hπ1).append (S r).R).proj y).2 0 ≠ 0) at hn
  exact Classical.not_not.mp hn

/-- Once the actual A count reaches its mark, the two native carrier traces
on the literal common last member have the same germ at the arc point.
The only inclusion used is derived from equality of the cosupports. -/
theorem common_trace_germ_of_count_bound
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (A' : MarkedIdeal (n+1) (projectionAmbient X))
    {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {z : Z} {x : X} {r : ℕ} (facts : ArcPairStageFacts A B A' T z x r)
    (hbound : A.d ≤ (r + 1) * (ordinaryTraceOrder A.N A.ideal x - A.d)) :
    ∀ᶠ y in 𝓝 z,
      y ∈ (geoTransformAlong (projectionTest A) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA ↔
      y ∈ (geoTransformAlong (projectionTest B) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA := by
  let QA := geoTransformAlong (projectionTest A) T
  let QB := geoTransformAlong (projectionTest B) T
  let D := QA.E.getLast facts.nonemptyA
  have hQA : IsInvDomain (kA + 1) QA :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong (projection_test_isInvDomain A hA) T facts.testA
  have hQB : IsInvDomain (kB + 1) QB :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong (projection_test_isInvDomain B hB) T facts.testB
  have hdA : QA.d = A.d := d_geoTransformAlong (projectionTest A) T
  have hDivA : IsDivNearAlong (n+1) QA.N QA.ideal D QA.d z := by
    apply (facts.exponentA QA.d).mpr
    rw [hdA]
    exact hbound
  have hDA : D ∈ QA.E := List.getLast_mem facts.nonemptyA
  have hDB : D ∈ QB.E := facts.last_mem_B
  have hzA : z ∈ QA.N := QA.cosupp_subset_N facts.mem_cosupp
  have hzB : z ∈ QB.N := QB.cosupp_subset_N (facts.cosupp_eq ▸ facts.mem_cosupp)
  have hzD : z ∈ D := facts.mem_last
  obtain ⟨j, hjA⟩ := hQA.isWellFormed.isClosedSubmanifold_N.2 z hzA
  have hjB := (facts.sameCarrierDim z facts.mem_cosupp j).mp hjA
  have hAj := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem
    hQA.isWellFormed.isTransverse hDA hzA hzD hjA
  have hBj := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem
    hQB.isWellFormed.isTransverse hDB hzB hzD hjB
  obtain ⟨i, hi⟩ := List.get_of_mem hDA
  have hClosedA : IsClosedSubmanifold (n+1) (QA.N ∩ D) := by
    have h := MemberInterAlong.isClosedSubmanifold_inter_memberInter (Nat.succ_pos n)
      hQA.isWellFormed.isClosedSubmanifold_N.1 hQA.isWellFormed.isSNCDivisor
      hQA.isWellFormed.isTransverse {i}
    rw [DivisorExponentAlong.memberInter_singleton, hi] at h
    exact h
  have hsub : ∀ᶠ y in 𝓝 z, y ∈ QA.N ∩ D → y ∈ QB.N ∩ D := by
    filter_upwards [hDivA] with y hy hyND
    have hyCos : y ∈ QA.cosupp := hy hyND.1 hyND.2
    have hyCosB : y ∈ QB.cosupp := facts.cosupp_eq ▸ hyCos
    exact ⟨QB.cosupp_subset_N hyCosB, hyND.2⟩
  exact HironakaG8P1ForeignCount.eventually_mem_iff_of_subset hClosedA hAj.2 hBj.2 hsub

/-- The source's order-greater-than-mark condition derives the count bound
at every stage with `dA ≤ r+1`; no equality of orders or tangent spaces is
an input. -/
theorem common_trace_germ_of_order_gt
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (A' : MarkedIdeal (n+1) (projectionAmbient X))
    {Z : CMfd.{u} (n+1)} {T : BlowupTower (projectionAmbient X) Z}
    {z : Z} {x : X} {r : ℕ} (facts : ArcPairStageFacts A B A' T z x r)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) (hsize : A.d ≤ r + 1) :
    ∀ᶠ y in 𝓝 z,
      y ∈ (geoTransformAlong (projectionTest A) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA ↔
      y ∈ (geoTransformAlong (projectionTest B) T).N ∩
        (geoTransformAlong (projectionTest A) T).E.getLast facts.nonemptyA := by
  have hgap : 1 ≤ ordinaryTraceOrder A.N A.ideal x - A.d := by omega
  have hcount : r + 1 ≤ (r + 1) * (ordinaryTraceOrder A.N A.ideal x - A.d) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r + 1) hgap
  exact common_trace_germ_of_count_bound A B hA hB A' facts (hsize.trans hcount)

/-- In the order-greater-than-mark branch, ordinary native input constructs
the common arc family together with its actual zero-parameter last divisor
and the equal carrier-trace germ at every sufficiently long stage. The same
original A frame and its native geometric tangent trace remain available. -/
theorem exists_arcPairFamily_with_common_exceptional_trace
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x) :
    ∃ (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
        (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
      (Φs : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n)) (S : ℕ → ArcStage n (arcY1 x)),
      Φs.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φs.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φs, w ∈ A.N ↔
        Φs.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧ IsArcFamily x hπ1 S ∧
      ∀ r, ArcCountsRaw (k := kA) A x hπ1 (S r) r ∧
        ArcCountsRaw (k := kB) B x hπ1 (S r) r ∧
        ∃ facts : ArcPairStageFacts A B A' ((arcA1 x hπ1).append (S r).R) (S r).z x r,
        (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z ∧
        (∀ v ∈ (S r).e.source,
          (∀ i : Fin n, flatCoord Φs i (((arcA1 x hπ1).append (S r).R).proj v).1 =
            ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n)) ∧
        (∀ y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
            facts.nonemptyA, (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0) ∧
        (A.d ≤ r + 1 → ∀ᶠ y in 𝓝 (S r).z,
          y ∈ (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA ↔
          y ∈ (geoTransformAlong (projectionTest B) ((arcA1 x hπ1).append (S r).R)).N ∩
            (geoTransformAlong (projectionTest A) ((arcA1 x hπ1).append (S r).R)).E.getLast
              facts.nonemptyA) ∧
        ∃ V : Set (S r).Z, IsOpen V ∧ (S r).z ∈ V ∧ V ⊆ (S r).e.source ∧
          (∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φs) ∧
          ∀ (W : Set X), IsClosed W →
            ∀ (g : ComplexModel n → ℂ) (L : ComplexModel n →L[ℂ] ℂ),
              HasFDerivAt g L 0 →
              (∀ w ∈ W, w ∈ flatDomain Φs →
                g (Φs.toFun (chartAt (ComplexModel n) x w)) = g 0) →
              ∀ y ∈ strictAlong ((arcA1 x hπ1).append (S r).R)
                  ((Prod.fst : projectionAmbient X → X) ⁻¹' W),
                y ∈ V → (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0 →
                L (HironakaG8P1ArcTangentTrace.oldCoordinates ((S r).e y)) = 0 := by
  obtain ⟨hπ1, Φs, J, S, hsrc, hzero, hmask, hS, hAll⟩ :=
    exists_arcPairFamily_with_geometric_tangent_trace
      A B hA hB hEB hdim hx A' B' hsA hsB hW hE'
  refine ⟨hπ1, Φs, J, S, hsrc, hzero, hmask, hS, ?_⟩
  intro r
  obtain ⟨hcA, hcB, facts, hAtlas, hcoords, V, hV, hzV, hVsource, hVdomain, hTrace⟩ := hAll r
  refine ⟨hcA, hcB, facts, hAtlas, hcoords,
    last_parameter_zero_of_arcFamily A hS r facts.nonemptyA, ?_,
    V, hV, hzV, hVsource, hVdomain, hTrace⟩
  intro hsize
  exact common_trace_germ_of_order_gt A B hA hB A' facts hgreater hsize

end

end Hironaka.HironakaG8P1ArcExceptionalTrace
