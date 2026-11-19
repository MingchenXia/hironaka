import Hironaka.Resolution.HironakaG3ControlledHistorySubsetTransport
import Hironaka.Resolution.HironakaActualSubmanifoldGermExtension
import Hironaka.Invariant.DropMembers
import Hironaka.Coherence.CartanIrreducible

/-!
# A finite consumer for a singular target in one proper smooth stratum

This module is a finite consumer of a given actual lower test tower. It does
not choose a lower resolution, prove generic non-erasure, or close the original
arbitrary-boundary G3 resolution goal.

The lower tower is an actual finite test tower, not a future-transport
certificate. The existing controlled-history constructor supplies its ambient
lift. The existing `DropMembers` theorem reattaches the initial members which
contain the chosen stratum. The target may be singular or reducible.

The exact projection-image identity transfers generic non-erasure proved by a
lower producer; it does not assert that arbitrary test towers preserve it.
Choosing a resolving lower tower, choosing the stratum, mixed components,
terminal normal crossings, and global gluing are separate remaining tasks.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3ContainingStratumHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace CoefficientIdealRestriction
  HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport

/-- The actual endpoint square and the derived arbitrary-subset strict
transport identify the projected target exactly. This transfers every retained
generic subset without assuming an all-future non-erasure certificate. -/
theorem projection_image_strictAlong_of_coupledHistory
    {d t : ℕ} {X : CMfd (d+t)} {P : CMfd d}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P}
    {Q : CMfd d} {Y : CMfd (d+t)}
    {T : BlowupTower P Q} {U : BlowupTower X Y} {η : Q → Y}
    (h : CoupledHistory N B J ι M T U η) (V : Set P) :
    U.proj '' strictAlong U (ι '' V) = ι '' (T.proj '' strictAlong T V) := by
  obtain ⟨_hc, _hr, _hI, _hNormal, _hE, _hTrans,
    _F, _hFη, hSquare, _hIdeal, _hBoundary⟩ := endpoint_of_coupledHistory h
  have hTransport := strictAlong_image_of_coupledHistory h V
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y ∈ η '' strictAlong T V := by
      rw [hTransport]
      exact hy
    obtain ⟨q, hq, rfl⟩ := hy'
    exact ⟨T.proj q, ⟨q, hq, rfl⟩, (congrFun hSquare q).symm.trans hyx⟩
  · rintro ⟨p, ⟨q, hq, hqp⟩, hpx⟩
    refine ⟨η q, ?_, ?_⟩
    · rw [← hTransport]
      exact ⟨q, hq, rfl⟩
    · calc
        U.proj (η q) = ι (T.proj q) := congrFun hSquare q
        _ = ι p := congrArg ι hqp
        _ = x := hpx

/-- A possibly singular analytic target contained in a proper smooth stratum
has an actual full-boundary ambient history for every actual intrinsic finite
test history. Only the retained boundary must be transverse to the stratum;
omitted members contain it and are reattached on the same constructed tower.

This is a finite lifting consumer, not a choice of lower resolution and not
the arbitrary-boundary embedded-resolution theorem. It remains in universe
zero, matching the existing source-facing finite constructor. -/
theorem exists_full_boundary_history_for_analytic_subset
    {d t : ℕ} {X : CMfd (d+t)} {N : Set X} (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) (ht : 0 < t)
    {E B : List (Set X)} (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (hTrans : IsTransverse (d+t) N B)
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    let V : Set N := (Subtype.val : N → X) ⁻¹' W
    let L := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
      (vanishingIdeal (n := d) V)
    ∀ {Q : CMfd d} (T : BlowupTower (CMfd.of N) Q), IsGeoTestTower L T →
      ∃ (Y : CMfd (d+t)) (U : BlowupTower X Y) (η : Q → Y),
        IsGeoTestTower (fullMarked E (vanishingIdeal (n := d+t) W)) U ∧
        U.length = T.length ∧
        CoupledHistory N B (vanishingIdeal (n := d+t) W)
          (Subtype.val : N → X) L T U η ∧
        Endpoint N B (vanishingIdeal (n := d+t) W)
          (Subtype.val : N → X) L T U η ∧
        CentresIn N U ∧
        IsSNCDivisor (d+t)
          (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E ∧
        (∀ H ∈ (geoTransformAlong (fullMarked B (vanishingIdeal (n := d+t) W)) U).E,
          H ∈ (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E) ∧
        (∀ H ∈ (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E,
          H ∉ (geoTransformAlong (fullMarked B (vanishingIdeal (n := d+t) W)) U).E →
            strictAlong U N ⊆ H) ∧
        η '' strictAlong T V = strictAlong U W ∧
        U.proj '' strictAlong U W =
          (Subtype.val : N → X) '' (T.proj '' strictAlong T V) ∧
        ((strictAlong U W).Nonempty ↔ (strictAlong T V).Nonempty) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  dsimp only
  intro Q T hTest
  let V : Set N := (Subtype.val : N → X) ⁻¹' W
  let J : GermIdeal (d+t) X := vanishingIdeal (n := d+t) W
  let L := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
    (vanishingIdeal (n := d) V)
  let M := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
    (GermIdeal.pullback (m := d) (Subtype.val : N → X) J)
  have hImage : (Subtype.val : N → X) '' V = W := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x, hWN hx⟩, hx, rfl⟩
  have hPullback : GermIdeal.pullback (m := d) (Subtype.val : N → X) J =
      vanishingIdeal (n := d) V := by
    dsimp only [J]
    rw [← hImage]
    exact HironakaActualSubmanifoldGermExtension.pullback_vanishing_image
      (Nat.le_add_right d t) hN V
  have hML : M = L := by
    dsimp only [M, L]
    rw [hPullback]
  have hTestM : IsGeoTestTower M T := by
    rw [hML]
    exact hTest
  have hJ : J.IsCoherent := CartanIrreducible.cartanCoherence W hWa
  have hNormal : (vanishingIdeal (n := d+t) N).Le J := by
    intro p f hf
    refine ⟨hf.1, ?_⟩
    filter_upwards [hf.2] with q hq hqW
    exact hq (hWN hqW)
  have hB : IsSNCDivisor (d+t) B :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hE hBsub
  obtain ⟨Y, U, η, hUB, hLength, hHistory, hEnd, hCentres, hAllSubsets⟩ :=
    exists_actual_finite_history_with_subset_transport hNc hN ht hB hTrans
      J hJ hNormal T hTestM
  have hFull : (fullMarked E J).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hJ, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  obtain ⟨hTestIff, hMembers, hMissing⟩ :=
    DropMembers.isGeoTestTower_withE_iff_of_centresIn (fullMarked E J) hFull
      (E' := B) (S := N) (fun _ hH => hBsub.subset hH) hOmitted U hCentres
  have hUE : IsGeoTestTower (fullMarked E J) U := hTestIff.mp hUB
  have hFullSNC : IsSNCDivisor (d+t) (geoTransformAlong (fullMarked E J) U).E :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hFull U hUE).isSNCDivisor
  have hTarget : η '' strictAlong T V = strictAlong U W := by
    simpa only [hImage] using hAllSubsets V
  have hProjection : U.proj '' strictAlong U W =
      (Subtype.val : N → X) '' (T.proj '' strictAlong T V) := by
    simpa only [hImage] using
      projection_image_strictAlong_of_coupledHistory hHistory V
  have hNonempty : (strictAlong U W).Nonempty ↔ (strictAlong T V).Nonempty := by
    rw [← hTarget]
    constructor
    · rintro ⟨y, q, hq, _hqy⟩
      exact ⟨q, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨η q, q, hq, rfl⟩
  have hHistoryL : CoupledHistory N B J (Subtype.val : N → X) L T U η := by
    simpa only [M, hPullback, L] using hHistory
  have hEndL : Endpoint N B J (Subtype.val : N → X) L T U η := by
    simpa only [M, hPullback, L] using hEnd
  exact ⟨Y, U, η, hUE, hLength, hHistoryL, hEndL, hCentres, hFullSNC,
    hMembers, hMissing, hTarget, hProjection, hNonempty⟩

end

end Hironaka.HironakaG3ContainingStratumHistory
