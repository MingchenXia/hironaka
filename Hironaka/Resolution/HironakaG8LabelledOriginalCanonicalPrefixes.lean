import Hironaka.Resolution.HironakaG8NativePrefixOriginalCanonical
import Hironaka.Resolution.HironakaG8LabelledNativeHead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LabelledOriginalCanonicalPrefixes
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres InvDomainTowerAlong
  HironakaEmbeddedAnalytic NormalCrossings HironakaG8NativePhaseCertificate HironakaG8LabelledNativeHistory
  HironakaG8LabelledNativeHead HironakaHolomorphicJetChartInvariance
  HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre HironakaG8NativePrefixOriginalCanonical
  HironakaActualOriginalPowerTransform HironakaActualPowerBoundaryExponents
  HironakaCoherentTransformExtension HironakaG11PresTowerState HironakaG11PresLineState
  HomogenizedGlueingTower

private abbrev original {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ, E, vanishingIdeal (n := n) W, 1⟩

private theorem simultaneous_prefix {n : ℕ} {X B : CMfd.{0} n} {I : Type}
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (H : BlowupTower X B) :
    ∀ {Y : CMfd.{0} n} (S : BlowupTower B Y),
      NativeSimultaneousStages (canonicalInvariant n) U P (H.append S) →
      NativeSimultaneousStages (canonicalInvariant n) U P H
  | _, .refl, h => h
  | _, .step S _ _ _, h => simultaneous_prefix U P H S h.1

/-- The already chosen atlas of a certified epoch has raw original
canonicality on every literal physical-head restriction. The full ordered
boundary is the pullback of the physical history's boundary and the raw
mark remains unchanged. -/
def RawEpochChartPrefixes {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (W : Set X) (E : List (Set X)) (H : ℕ → ℕ) (T : BlowupTower X Y) : Prop :=
  ∃ (I : Type) (A : NativeWindows X I W E H (phaseLevel W H)),
    (∀ i, IsGeoResolution (A.record i) (restrict (A.openSet i) T)) ∧
    ∀ (i : I) (j : ℕ),
      let P := A.record i
      let S := head T j
      let U := A.openSet i
      let Q := restrict U S
      let M := geoTransformAlong P Q
      IsCanonical P ((invFamily hn n).inv P) Q ∧ IsInvDomain n M ∧ M.d = P.d ∧
      M.E = (geoTransformAlong (original W E) S).E.map ((Subtype.val : openPreimage S U → _) ⁻¹' ·) ∧
      HSTowerState M ((Subtype.val : openPreimage S U → _) ⁻¹' strictAlong S W) H

set_option maxHeartbeats 1600000 in
/-- All chart prefixes are read from the simultaneous maxima retained in
the actual native phase certificate. The powered terminal CAN field is
unneeded for this induction. -/
theorem actual_native_phase_raw_chart_prefixes {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} {H : ℕ → ℕ} {T : BlowupTower X Y}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (h : ActualNativePhase W E H T) : RawEpochChartPrefixes hn W E H T := by
  obtain ⟨I, A, hEnd, hSync⟩ := h.nativeStages
  have hStage := hSync trivial
  refine ⟨I, A, ?_, ?_⟩
  · intro i
    let P := A.record i
    let S := restrict (A.openSet i) T
    have hCan := simultaneous_powered_prefix_raw_canonical hn A.openSet A.record A.domain
      A.exponent A.positive T hStage i
    have hTest := (invFamily hn n).isInvValue.isGeoTestTower_of_isCanonical (A.domain i) S hCan
    have hCurrent := isInvDomain_geoTransformAlong (A.domain i) S hTest
    have hCos := (original_power_transform P (A.domain i) (A.exponent i) (A.positive i) S hTest).2.cosupp_eq.trans
      (powerMarked_cosupp (geoTransformAlong P S) hCurrent (A.positive i))
    exact ⟨hTest, hCos.symm.trans (hEnd i).2.2⟩
  · intro i j P S U Q M
    have hSplit := head_append_tail T j
    have hStage' : NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered (S.append (tail T j)) := by
      rw [hSplit]
      exact hStage
    have hHead := simultaneous_prefix A.openSet A.powered S (tail T j) hStage'
    have hCan := simultaneous_powered_prefix_raw_canonical hn A.openSet A.record A.domain
      A.exponent A.positive S hHead i
    have hTest := (invFamily hn n).isInvValue.isGeoTestTower_of_isCanonical (A.domain i) Q hCan
    have hCurrent := isInvDomain_geoTransformAlong (A.domain i) Q hTest
    let G := original W E
    have hG : G.IsWellFormed := ⟨isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
      hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
    have hS : IsGeoTestTower G S := ((isGeoTestTower_iff_head_tail G T j).mp h.test).1
    have hb : P.E = (MarkedIdeal.pullback (Subtype.val : U → X) G).E := A.boundary i
    have hBound := geoTransformAlong_E_eq_of_E_eq hb Q
    rw [geoTransformAlong_restrict U hG.isClosedSubmanifold_N hG.isCoherent S hS] at hBound
    refine ⟨hCan, hCurrent, d_geoTransformAlong P Q, hBound, ?_⟩
    rw [← strictAlong_restrict U S W]
    exact HSTowerState.rebase (A.native i).hsTowerState Q hTest

/-- An actual decomposition of each labelled native epoch, including
after restriction or chart adoption. The beginning of each epoch
is its own physical base and the labels keep their original order. -/
inductive LabelledRawEpochPrefixes {n : ℕ} (hn : 0 < n) :
    {X Y : CMfd.{0} n} → Set X → List (Set X) →
      BlowupTower X Y → List (ℕ → ℕ) → Prop
  | finished {X Y : CMfd.{0} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
      (hLength : T.length = 0) (hW : IsClosedSubmanifold n W) :
      LabelledRawEpochPrefixes hn W E T []
  | phase {X B Y Z : CMfd.{0} n} {W : Set X} {E : List (Set X)}
      {T : BlowupTower X Y} {S : BlowupTower X B} {Q : BlowupTower B Z}
      {H : ℕ → ℕ} {L : List (ℕ → ℕ)}
      (hS : RawEpochChartPrefixes hn W E H S)
      (hLower : ∀ G ∈ L, toLex G < toLex H)
      (hQ : LabelledRawEpochPrefixes hn (strictTransform n S.proj W)
        (geoTransformAlong (original W E) S).E Q L)
      {χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
      (hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T (S.append Q) χ) :
      LabelledRawEpochPrefixes hn W E T (H :: L)

/-- Every actual singular epoch in the labelled tower supplies its raw
original canonical chart prefixes at its own profile. Head extraction
materializes the literal atlas of adopted and restricted epochs as well. -/
theorem labelled_native_raw_epoch_prefixes {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} {K : Set X} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower n W E K T L) : LabelledRawEpochPrefixes hn W E T L := by
  induction L generalizing X Y with
  | nil =>
    obtain ⟨hLen, hW⟩ := finished_of_empty_labels h rfl
    exact .finished hLen hW
  | cons H L ih =>
    obtain ⟨B, Z, S, Q, χ, hPhase, _, hLower, hLater, hIso⟩ := exists_head_phase h H L rfl
    exact .phase (actual_native_phase_raw_chart_prefixes hn h.source_analytic h.source_snc hPhase)
      hLower (ih hLater) hIso

end
end Hironaka.HironakaG8LabelledOriginalCanonicalPrefixes
