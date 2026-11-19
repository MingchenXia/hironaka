import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaG8SaturatedNativePhase
import Hironaka.Resolution.HironakaG8CompactLexInduction

/-! A labelled proof of a finite singular resolution retains the actual
phase towers, their inputs, their native charts, and their compact task. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LabelledNativeHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaG8NativePhaseCertificate
  HironakaActualVanishingIntrinsicHSTransport HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSeparationChoiceComparison StrictTransformComposition HironakaG11PresTowerState
  HironakaResolutionSpaceLocal HironakaG8SaturatedNativePhase MarkedIdealBiholomorphism
  MarkedIdealTowerTransport MaxLocusLocal NormalCrossings HironakaEmbeddedBoundary
  NormalCrossingsInvariance HironakaG8CompactLexInduction HironakaStageCenters
  HironakaG8FiniteSingularTowerMerge HironakaG8SingularFootprintExtension
  HironakaActualOpenEmbeddingVanishingIdeal HomogenizedGlueingTower

variable {n : ℕ}

private abbrev original {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

/-- A finite actual singular-resolution history remembers one complete
native phase at each strictly descending profile. The task of every
remaining phase is the literal inverse image of the preceding task. -/
inductive LabelledNativeTower (n : ℕ) :
    {X Y : CMfd.{0} n} → Set X → List (Set X) → Set X →
      BlowupTower X Y → List (ℕ → ℕ) → Prop
  | smooth {X : CMfd.{0} n} {W : Set X} {E : List (Set X)} {K : Set X}
      (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
      (hSmooth : IsClosedSubmanifold n W) :
      LabelledNativeTower n W E K (.refl : BlowupTower X X) []
  | phase {X A Y : CMfd.{0} n} {W : Set X} {E : List (Set X)} {K : Set X}
      {S : BlowupTower X A} {T : BlowupTower A Y} {H : ℕ → ℕ} {L : List (ℕ → ℕ)}
      (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
      (hUpper : ∀ x ∈ K ∩ singularSet (n := n) W,
        toLex (hilbertSamuelAt (vanishingIdeal (n := n) W) x) ≤ toLex H)
      (hPhase : ActualNativePhase W E H S)
      (hLower : ∀ h ∈ L, toLex h < toLex H)
      (hLater : LabelledNativeTower n (strictTransform n S.proj W) (geoTransformAlong (original W E) S).E
        (S.proj ⁻¹' K) T L) :
      LabelledNativeTower n W E K (S.append T) (H :: L)
  | restrictOpen {X Y : CMfd.{0} n} {W : Set X} {E : List (Set X)} {K : Set X}
      {T : BlowupTower X Y} {L : List (ℕ → ℕ)} (h : LabelledNativeTower n W E K T L) (O : Opens X) :
      LabelledNativeTower n ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·))
        ((Subtype.val : O → X) ⁻¹' K) (restrict O T) L
  | of_isTowerIso {X X' Y Y' : CMfd.{0} n} {W : Set X} {E : List (Set X)} {K : Set X}
      {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L : List (ℕ → ℕ)}
      (h : LabelledNativeTower n W E K T L)
      {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
      (hIso : IsTowerIso φ T' T χ) :
      LabelledNativeTower n (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (φ ⁻¹' K) T' L

variable {X Y : CMfd.{0} n} {W K : Set X} {E : List (Set X)}
variable {T : BlowupTower X Y} {L : List (ℕ → ℕ)}

theorem LabelledNativeTower.source_analytic (h : LabelledNativeTower n W E K T L) :
    IsComplexAnalyticSubset (n := n) W := by
  induction h with
  | smooth hW _ _ => exact hW
  | phase hW _ _ _ _ _ _ => exact hW
  | restrictOpen _ O ih => exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val ih O
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage φ.contMDiff ih

theorem LabelledNativeTower.source_snc (h : LabelledNativeTower n W E K T L) :
    IsSNCDivisor n E := by
  induction h with
  | smooth _ hE _ => exact hE
  | phase _ hE _ _ _ _ _ => exact hE
  | restrictOpen _ O ih =>
    exact isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val ih
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    exact (isSNCDivisor_map_preimage_iff φ).mpr ih

/-- Read the original full-boundary test and singular positions from the
labelled physical chain. -/
theorem LabelledNativeTower.test_and_singular (h : LabelledNativeTower n W E K T L) :
    IsGeoTestTower (original W E) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  induction h with
  | smooth _ _ _ => exact ⟨trivial,trivial⟩
  | @phase X A Y W E K S T H L hW hE hUpper hPhase hLower hTail ih =>
    exact original_test_and_singular_stages_append hW hE S T hPhase.test hPhase.singular ih.1 ih.2
  | @restrictOpen X Y W E K T L h O ih =>
    refine ⟨?_,singular_stages_restrict W O T ih.2⟩
    have hR := MarkedIdealRestrictOpen.isGeoTestTower_restrict O isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W h.source_analytic) T ih.1
    have hRecord : MarkedIdeal.pullback (Subtype.val : O → X) (original W E) =
        original (X := CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) := pullback_val_mk_vanishingIdeal O E W
    rw [hRecord] at hR
    exact hR
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    refine ⟨?_,?_⟩
    · have hRec : MarkedIdeal.pullback φ (original W E) = original (X := X') (φ ⁻¹' W)
          (E.map (φ ⁻¹' ·)) := by
        change (MarkedIdeal.mk (φ ⁻¹' univ) (E.map (φ ⁻¹' ·))
          (GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) W)) 1 : MarkedIdeal n X') = _
        rw [preimage_univ,pullback_vanishingIdeal_of_biholomorphism]
      have ht := (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ
        (CartanIrreducible.cartanCoherence W h.source_analytic) hIso).mpr ih.1
      rw [hRec] at ht
      exact ht
    · apply singular_stages_of_tower_iso (φ ⁻¹' W) (h.source_analytic.isClosed.preimage φ.continuous)
        φ.symm hIso.symm
      rw [symm_preimage_preimage φ W]
      exact ih.2

theorem LabelledNativeTower.descending (h : LabelledNativeTower n W E K T L) :
    L.Pairwise fun H H' => toLex H' < toLex H := by
  induction h with
  | smooth _ _ _ => exact List.Pairwise.nil
  | phase _ _ _ _ hLower _ ih => exact List.Pairwise.cons hLower ih
  | restrictOpen _ _ ih => exact ih
  | of_isTowerIso _ _ ih => exact ih

/-- The recursive certificate resolves the underlying strict transform on
the entire chosen base, while retaining the compact task used in its choice. -/
theorem LabelledNativeTower.target_smooth (h : LabelledNativeTower n W E K T L) :
    IsClosedSubmanifold n (strictTransform n T.proj W) := by
  induction h with
  | smooth hW _ hSmooth =>
    simpa only [BlowupTower.proj_refl,strictTransform_id hW.isClosed] using hSmooth
  | @phase X A Y W E K S T H L hW hE hBound hPhase hLower hTail ih =>
    rw [BlowupTower.proj_append,strictTransform_comp S.contMDiff_proj T.contMDiff_proj W]
    exact ih
  | @restrictOpen X Y W E K T L h O ih =>
    rw [strictTransform_restricted_tower O T W]
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val ih _
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    rw [strictTransform_preimage_of_square φ χ T'.contMDiff_proj T.contMDiff_proj W
      h.source_analytic.isClosed (fun z => (hIso.proj_comm z).symm)]
    exact (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff χ).mpr ih

/-- Preserve the chronological phase labels when the recursive suffix is
placed on the actual saturated input of the restricted preceding phase. -/
theorem LabelledNativeTower.prepend_with_saturated_base
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    {H : ℕ → ℕ} (hPhase : ActualNativePhase W E H T)
    (hUpper : ∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex H)
    (V : Opens Y) {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hS : IsGeoTestTower (original
      ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)
      ((geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·))) S)
    (hTail : LabelledNativeTower n
      ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)
      ((geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·))
      ((Subtype.val : V → Y) ⁻¹' (T.proj ⁻¹' K)) S L)
    (hLower : ∀ h ∈ L, toLex h < toLex H)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let U := openPreimage T O
    let D := nestedOpens V U
    let e := (nestedOpensDiffeo (n := n) hOV).symm
    let tail := transport e (restrict D S)
    LabelledNativeTower n ((Subtype.val : O → X) ⁻¹' W)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) ((Subtype.val : O → X) ⁻¹' K)
      ((restrict O T).append tail.tower) (H :: L) := by
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let WV := (Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W
  let EV := (geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·)
  let KV := (Subtype.val : V → Y) ⁻¹' (T.proj ⁻¹' K)
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let KO := (Subtype.val : O → X) ⁻¹' K
  let tail := transport e (restrict D S)
  obtain ⟨hCarrier,hBoundary⟩ :=
    saturated_native_input_coordinates hW E hE T hPhase.test V S hS O hOV
  have hEtrace : ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) =
      (geoTransformAlong (original WO EO) (restrict O T)).E := by
    have hRecord : MarkedIdeal.pullback (Subtype.val : O → X) (original W E) =
        original (X := CMfd.of (n := n) O) WO EO := pullback_val_mk_vanishingIdeal O E W
    change ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) =
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) (original W E)) (restrict O T)).E
      at hBoundary
    rw [hRecord] at hBoundary
    exact hBoundary
  have hTask : e ⁻¹' ((Subtype.val : D → V) ⁻¹' KV) = (restrict O T).proj ⁻¹' KO := by
    ext z
    change T.proj z.val ∈ K ↔ ((restrict O T).proj z).val ∈ K
    rw [proj_restrict]
  have hLater := (hTail.restrictOpen D).of_isTowerIso (transport_isTowerIso e (restrict D S))
  change LabelledNativeTower n (e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV))
    ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·))
    (e ⁻¹' ((Subtype.val : D → V) ⁻¹' KV)) tail.tower L at hLater
  rw [hCarrier,hEtrace,hTask] at hLater
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hUpperO : ∀ x ∈ KO ∩ singularSet (n := n) WO, toLex (HS[WO] x) ≤ toLex H := by
    rintro x ⟨hx,hs⟩
    change x ∈ singularSet (n := n) ((Subtype.val : O → X) ⁻¹' W) at hs
    rw [singularSet_preimage_val] at hs
    change toLex (HS[(Subtype.val : O → X) ⁻¹' W] x) ≤ toLex H
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W x)]
    exact hUpper x.val ⟨hx,hs⟩
  have hEO : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  exact .phase hWO hEO hUpperO (hPhase.restrictOpen hW O) hLower hLater

end
end Hironaka.HironakaG8LabelledNativeHistory
