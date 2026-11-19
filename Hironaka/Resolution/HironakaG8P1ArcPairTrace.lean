import Hironaka.Resolution.HironakaG8P1ArcPair
import Hironaka.Resolution.HironakaG8P1ArcTangentTrace

set_option autoImplicit false

/-!
# The common arc-pair stage with one actual original frame retained

The first record supplies its actual original coordinates, mask, atlas
charts and geometric differential trace. The second supplies the existing
weak arc family. Canonical arc-family uniqueness transports its raw counts
onto the first tower and point. No equality of the two original carriers,
no joint two-record raw constructor, and no tangent comparison is assumed.

The common-stage facts below are the post-construction argument of
`HironakaG8P1ArcPair.exists_arcPairStage`, separated from witness selection.
The common divisor is the literal last native boundary member.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcPairTrace

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong
  HironakaActualProjectionTestRecord HironakaActualSharedCartierTraceTests
  HironakaG8P1ArcTower HironakaG8P1ArcPair HironakaG8P1ArcChartFamily
  HironakaG8P1ArcTangentTrace HomogenizedGlueingTower

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual geometric facts at one common stage. The distinguished divisor is
the last member of the first native boundary, not an independently chosen set. -/
structure ArcPairStageFacts (A B : MarkedIdeal n X)
    (A' : MarkedIdeal (n+1) (projectionAmbient X))
    {Z : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Z)
    (z : Z) (x : X) (r : ℕ) : Prop where
  pointTower : PointTower T
  testA : IsGeoTestTower (projectionTest A) T
  testB : IsGeoTestTower (projectionTest B) T
  testA' : IsGeoTestTower A' T
  cosupp_eq : (geoTransformAlong (projectionTest A) T).cosupp =
    (geoTransformAlong (projectionTest B) T).cosupp
  sameCarrierDim : SameCarrierDim (geoTransformAlong (projectionTest A) T)
    (geoTransformAlong (projectionTest B) T)
  boundary_eq : (geoTransformAlong (projectionTest A) T).E =
    (geoTransformAlong (projectionTest B) T).E
  mem_cosupp : z ∈ (geoTransformAlong (projectionTest A) T).cosupp
  nonemptyA : (geoTransformAlong (projectionTest A) T).E ≠ []
  last_mem_B : (geoTransformAlong (projectionTest A) T).E.getLast nonemptyA ∈
    (geoTransformAlong (projectionTest B) T).E
  mem_last : z ∈ (geoTransformAlong (projectionTest A) T).E.getLast nonemptyA
  exponentA : ∀ e, IsDivNearAlong (n+1) (geoTransformAlong (projectionTest A) T).N
    (geoTransformAlong (projectionTest A) T).ideal
    ((geoTransformAlong (projectionTest A) T).E.getLast nonemptyA) e z ↔
      e ≤ (r + 1) * (ordinaryTraceOrder A.N A.ideal x - A.d)
  exponentB : ∀ e, IsDivNearAlong (n+1) (geoTransformAlong (projectionTest B) T).N
    (geoTransformAlong (projectionTest B) T).ideal
    ((geoTransformAlong (projectionTest A) T).E.getLast nonemptyA) e z ↔
      e ≤ (r + 1) * (ordinaryTraceOrder B.N B.ideal x - B.d)

/-- The existing post-count common-stage argument, applied to actual counts
on one already identified stage. No common history or divisor is an input. -/
theorem stage_facts_of_rawCounts
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) (x : X)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))))
    (s : ArcStage n (arcY1 x)) (r : ℕ)
    (hpt : PointTower ((arcA1 x hπ1).append s.R))
    (hcA : ArcCountsRaw (k := kA) A x hπ1 s r)
    (hcB : ArcCountsRaw (k := kB) B x hπ1 s r) :
    ArcPairStageFacts A B A' ((arcA1 x hπ1).append s.R) s.z x r := by
  obtain ⟨_hlen, hTA, hCosA, GA, hNA, hEA, hiA, hzGA, hCA⟩ := arcCounts_of_raw hcA
  obtain ⟨_hlenB, hTB, _hCosB, GB, hNB, hEB', hiB, hzGB, hCB⟩ := arcCounts_of_raw hcB
  set T := (arcA1 x hπ1).append s.R
  set QA := (projectionTest A).geoTransformAlong T with hQA
  set QB := (projectionTest B).geoTransformAlong T with hQB
  have hTA' : IsGeoTestTower A' T := isGeoTestTower_of_sameNID hsA hE' T hpt hTA
  have hcos : QA.cosupp = QB.cosupp := by
    rw [hQA, hQB, ← cosupp_eq_of_sameNID (sameNID_geoTransformAlong hsA T), (hW.2 T).2 hTA',
      cosupp_eq_of_sameNID (sameNID_geoTransformAlong hsB T)]
  have hdimQ : SameCarrierDim QA QB :=
    sameCarrierDim_along (projection_test_isInvDomain A hA).isWellFormed
      (projection_test_isInvDomain B hB).isWellFormed hsA hsB hW hE'
      (HironakaG8P1Assembly.sameCarrierDim_projectionTest hA hB hdim) T hpt hTA hTB
  have hEAB : QA.E = QB.E := by
    refine MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq ?_ T
    show A.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] =
      B.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    rw [hEB]
  obtain ⟨hneA, _hzNA, hzDA, hExpA⟩ :=
    HironakaG8P1Assembly.count_zero_exponent GA QA _ s.z hCA hNA hEA hiA hzGA
  obtain ⟨hneB, _hzNB, _hzDB, hExpB⟩ :=
    HironakaG8P1Assembly.count_zero_exponent GB QB _ s.z hCB hNB hEB' hiB hzGB
  have hlastEq : ∀ (l₁ l₂ : List (Set s.Z)) (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      l₁.getLast h₁ = l₂.getLast h₂ := by
    rintro _ _ rfl _ _
    rfl
  have hDD : QB.E.getLast hneB = QA.E.getLast hneA := hlastEq _ _ hEAB.symm _ _
  refine {
    pointTower := hpt
    testA := hTA
    testB := hTB
    testA' := hTA'
    cosupp_eq := hcos
    sameCarrierDim := hdimQ
    boundary_eq := hEAB
    mem_cosupp := hCosA
    nonemptyA := hneA
    last_mem_B := ?_
    mem_last := hzDA
    exponentA := hExpA
    exponentB := ?_ }
  · rw [← hEAB]
    exact List.getLast_mem hneA
  · intro e
    rw [← hDD]
    exact hExpB e

/-- Ordinary inputs construct one common point-arc family. The first record's
actual original frame, mask, charts and trace are retained; the second
record's weak-family raw counts are transported by canonical uniqueness. -/
theorem exists_arcPairFamily_with_geometric_tangent_trace
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E) :
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
        ArcPairStageFacts A B A' ((arcA1 x hπ1).append (S r).R) (S r).z x r ∧
        (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z ∧
        (∀ v ∈ (S r).e.source,
          (∀ i : Fin n, flatCoord Φs i (((arcA1 x hπ1).append (S r).R).proj v).1 =
            ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n)) ∧
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
                L (oldCoordinates ((S r).e y)) = 0 := by
  have hxB : x ∈ B.cosupp := by
    have h1 : A'.cosupp = B'.cosupp := (hW.2 .refl).2 trivial
    have h2 := cosupp_eq_of_sameNID hsA
    have h3 := cosupp_eq_of_sameNID hsB
    have hA0 := (projection_test_dictionary A hA).2.2.2.2.2.2.2
    have hB0 := (projection_test_dictionary B hB).2.2.2.2.2.2.2
    have hp : ((x, 0) : projectionAmbient X) ∈ (projectionTest B).cosupp := by
      rw [← h3, ← h1, h2, hA0]
      exact hx
    rw [hB0] at hp
    exact hp
  have hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) :=
    isBlowupAlong_blowupProj (n := n+1) (C := ({(x, 0)} : Set (projectionAmbient X)))
      (HironakaActualProjectionVerticalBlowupChart.projection_point_centre A hA x hx).2
  obtain ⟨Φs, J, S, hΦsSrc, hΦsZero, hMask, hS, hAllA⟩ :=
    exists_arcFamily_with_geometric_tangent_trace (n := n) (X := X) A hA x hx hπ1
  obtain ⟨S', hS', hcB⟩ := exists_arcFamily (n := n) (X := X) (k := kB) B hB x hxB hπ1
  have hCountsB : ∀ r, ArcCountsRaw (k := kB) B x hπ1 (S r) r :=
    arcCountsRaw_of_arcFamily_identify (n := n) (X := X) (k := kB) B x hπ1 hS hS' hcB
  refine ⟨hπ1, Φs, J, S, hΦsSrc, hΦsZero, hMask, hS, ?_⟩
  intro r
  obtain ⟨hcA, hAtlas, hcoords, V, hV, hzV, hVsource, hVdomain, hTrace⟩ := hAllA r
  have hpt := pointTower_arcFamily hS r
  have hStage := stage_facts_of_rawCounts (n := n) (X := X)
    A B hA hB hEB hdim x A' B' hsA hsB hW hE' hπ1 (S r) r hpt hcA (hCountsB r)
  exact ⟨hcA, hCountsB r, hStage, hAtlas, hcoords, V, hV, hzV, hVsource, hVdomain, hTrace⟩

end

end Hironaka.HironakaG8P1ArcPairTrace
