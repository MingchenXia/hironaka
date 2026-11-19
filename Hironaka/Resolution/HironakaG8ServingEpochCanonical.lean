import Hironaka.Resolution.HironakaG8FiniteNativeTestServing
import Hironaka.Resolution.HironakaG8SaturatedNativePhase

/-! Intrinsic HS epochs on the actual native serving trace and its physical clips. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ServingEpochCanonical
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaEmbeddedBoundary HironakaStageCenters
  MaxLocusLocal MarkedIdealTowerTransport NormalCrossings NormalCrossingsInvariance
  HironakaG8FiniteNativeTestServing HironakaG8CanonicalNativeServingRank HironakaG8SaturatedNativePhase
  HironakaG8LabelledOriginalCanonicalPrefixes HironakaActualHilbertSamuelLexOrder
  HironakaG8NativePhaseCertificate HironakaHolomorphicJetChartInvariance HomogenizedGlueingTower

private abbrev whole {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

/-- Every further saturated clip of a stored phase has canonical raw
chart prefixes on its actual adopted physical tail. The epoch's HS label
and the ordered accumulated boundary remain the same data. -/
theorem raw_prefixes_on_any_saturated_clip {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X} {H : ℕ → ℕ}
    (hP : NativeTestState W E P) (s : NativeServingStep W E P K H)
    (O : Opens X) (hO : openPreimage P O ≤ s.phaseOpen) :
    let A := CMfd.of (n := n+1) O
    let Q := restrict O P
    let W₀ := (Subtype.val : O → X) ⁻¹' W
    let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
    let L := transport (nestedOpensDiffeo (n := n+1) hO).symm
      (restrict (nestedOpens s.phaseOpen (openPreimage P O)) s.phaseTower)
    let V := strictTransform (n+1) Q.proj W₀
    let F := (geoTransformAlong (whole (X := A) W₀ E₀) Q).E
    ActualNativePhase V F H L.tower ∧
      RawEpochChartPrefixes (Nat.succ_pos n) V F H L.tower := by
  intro A Q W₀ E₀ L V F
  let M := whole W E
  let M₀ := whole (X := A) W₀ E₀
  have hEq : MarkedIdeal.pullback (Subtype.val : O → X) M = M₀ :=
    pullback_val_mk_vanishingIdeal O E W
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hP.analytic,
    hP.snc,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hP.snc⟩
  have hPhase := native_phase_on_saturated_input hP.analytic E hP.snc P hP.tested
    s.phaseOpen s.phaseTower H s.phase O hO
  change ActualNativePhase V (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) M) Q).E
    H L.tower at hPhase
  rw [hEq] at hPhase
  have hM₀ : M₀.IsWellFormed := hEq ▸ MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM O
  have hQ : IsGeoTestTower M₀ Q := hEq ▸ MarkedIdealRestrictOpen.isGeoTestTower_restrict O
    hM.isClosedSubmanifold_N hM.isCoherent P hP.tested
  have hF := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM₀ Q hQ).isSNCDivisor
  have hW₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hP.analytic O
  have hV := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW₀ Q
  exact ⟨hPhase,actual_native_phase_raw_chart_prefixes (Nat.succ_pos n) hV hF hPhase⟩

/-- Raw original canonicality at every chart prefix of the literal tail
that is physically appended by the stored serving step. -/
theorem actual_serving_step_raw_prefixes {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X} {H : ℕ → ℕ}
    (hP : NativeTestState W E P) (s : NativeServingStep W E P K H) :
    RawEpochChartPrefixes (Nat.succ_pos n)
      (strictTransform (n+1) (restrict s.baseOpen P).proj s.nextCarrier)
      (geoTransformAlong (whole (X := s.source) s.nextCarrier s.nextBoundary) (restrict s.baseOpen P)).E
      H s.tail.tower :=
  (raw_prefixes_on_any_saturated_clip hP s s.baseOpen s.saturation).2

/-- A finite original mark-one test, certified by successive intrinsic HS labels.
Each epoch records original canonical prefixes both before clipping and on the
exact tail appended to the evolving physical tower. -/
inductive PhysicalEpochCertificate {n : ℕ} :
    {A B : CMfd.{0} (n+1)} → (W : Set A) → List (Set A) → BlowupTower A B → Set A →
      List (ActualAnalyticLexHilbertSamuelProfile (n+1)) → Prop
  | done {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      (state : NativeTestState W E P)
      (clear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))) :
      PhysicalEpochCertificate W E P K []
  | next {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
      (sourceState : NativeTestState W E P)
      (a : B) (aOn : a ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      (highest : ∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
        toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) x) ≤ toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) a))
      (s : NativeServingStep W E P K (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) a))
      (raw : RawEpochChartPrefixes (Nat.succ_pos n)
        ((Subtype.val : s.phaseOpen → B) ⁻¹' strictTransform (n+1) P.proj W)
        ((geoTransformAlong (whole W E) P).E.map ((Subtype.val : s.phaseOpen → B) ⁻¹' ·))
        (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) a) s.phaseTower)
      (state : NativeTestState s.nextCarrier s.nextBoundary s.tower)
      (rankDrop : ∀ z ∈ s.tower.proj ⁻¹' s.nextTask ∩ singularSet (n := n+1)
          (strictTransform (n+1) s.tower.proj s.nextCarrier),
        realizedProfile (strictTransform (n+1) s.tower.proj s.nextCarrier) z <
          realizedProfile (strictTransform (n+1) P.proj W) a)
      (appended : RawEpochChartPrefixes (Nat.succ_pos n)
        (strictTransform (n+1) (restrict s.baseOpen P).proj s.nextCarrier)
        (geoTransformAlong (whole (X := s.source) s.nextCarrier s.nextBoundary) (restrict s.baseOpen P)).E
        (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) a) s.tail.tower)
      (rest : PhysicalEpochCertificate s.nextCarrier s.nextBoundary s.tower s.nextTask labels) :
      PhysicalEpochCertificate W E P K (realizedProfile (strictTransform (n+1) P.proj W) a :: labels)

/-- The certificate follows the actual stored phase witnesses inductively. The
single initial state is the input of the serving algorithm; all subsequent
states already belong to the corresponding stored physical steps. -/
theorem canonical_by_epochs {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (state : NativeTestState W E P) (h : NativeTestServingTrace W E P K labels) :
    PhysicalEpochCertificate W E P K labels := by
  revert state
  induction h with
  | done state clear => exact fun _ => .done state clear
  | next a ha highest s raw nextState drop rest ih =>
    intro state
    exact .next state a ha highest s raw nextState drop
      (actual_serving_step_raw_prefixes state s) (ih nextState)

/-- Finite compact serving with descending intrinsic labels, certified on the
same raw chart tails actually used to advance the original test. -/
theorem exists_finite_epoch_canonical_serving {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} (P : BlowupTower X Y)
    (state : NativeTestState W E P) (K : Set X) (hK : IsCompact K) :
    ∃ labels, NativeTestServingTrace W E P K labels ∧
      PhysicalEpochCertificate W E P K labels ∧ labels.Pairwise (fun a b => b < a) := by
  obtain ⟨labels,h⟩ := exists_finite_native_test_serving P state K hK
  exact ⟨labels,h,canonical_by_epochs state h,h.strict_labels⟩

/-- Recover the physical native test trace from the epoch certificate.
The replay retains each selected serving step and its exact append. -/
theorem PhysicalEpochCertificate.toTrace {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (h : PhysicalEpochCertificate W E P K labels) : NativeTestServingTrace W E P K labels := by
  induction h with
  | done state clear => exact .done state clear
  | next source a ha highest s raw nextState drop appended rest ih =>
    exact .next a ha highest s raw nextState drop ih

#print axioms PhysicalEpochCertificate.toTrace
#print axioms canonical_by_epochs
#print axioms exists_finite_epoch_canonical_serving

#print axioms raw_prefixes_on_any_saturated_clip
#print axioms actual_serving_step_raw_prefixes

end
end Hironaka.HironakaG8ServingEpochCanonical
