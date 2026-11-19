import Hironaka.Resolution.HironakaG8SaturatedPrefixAppend
import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-! Finite singular smoothing on a neighbourhood of a compact task by actual
relative phases on successive saturated source restrictions. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8RelativeLexInduction

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport MaxLocusLocal NormalCrossings
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8SaturatedPrefixAppend
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualHilbertSamuelLexOrder HironakaActualHilbertSamuelWellFounded
  HironakaActualCompactHSMaximalProfile HironakaActualVanishingIntrinsicHSTransport
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG8DenseBoundaryRestart HironakaG8SingularFootprintExtension
  HironakaActualOpenEmbeddingVanishingIdeal HironakaNormalCrossingsSeparationChoiceComparison

variable {n : ℕ}

private abbrev record {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ, E, vanishingIdeal (n := n) W, 1⟩

local notation "HS[" m ", " A "]" => hilbertSamuelAt (vanishingIdeal (n := m) A)

private def actualProfile {X : CMfd.{0} n} (W : Set X) (x : X) : ActualLexHilbertSamuelProfile n :=
  ⟨toLex (HS[n, W] x), analytic_hilbertSamuel_realizable (wholeChartStalkIdeal
    (vanishingIdeal (n := n) W) x x (mem_chart_source (ComplexModel n) x))⟩

/-- A supplied finite relative phase clears an attained highest singular
profile over the compact task and never increases any order anywhere on its
chosen base open. -/
def HasRelativeSingularPhases (n : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} {W : Set X}, IsComplexAnalyticSubset (n := n) W →
    ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) →
    ∀ (K : Set X), IsCompact K → ∀ a ∈ K ∩ singularSet (n := n) W,
      (∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[n, W] x) ≤ toLex (HS[n, W] a)) →
      ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        let W₀ := (Subtype.val : O → X) ⁻¹' W
        let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
        let W₁ := strictTransform n T.proj W₀
        IsGeoTestTower (record W₀ E₀) T ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W₀)) T ∧
        (∀ z ℓ, HS[n, W₁] z ℓ ≤ HS[n, W₀] (T.proj z) ℓ) ∧
        (∀ z, HS[n, W₀] (T.proj z) = HS[n, W] a → toLex (HS[n, W₁] z) < toLex (HS[n, W] a))

private abbrev NeighbourhoodResolution {X : CMfd.{0} n}
    (W : Set X) (E : List (Set X)) (K : Set X) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
    let W₀ := (Subtype.val : O → X) ⁻¹' W
    let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
    IsGeoTestTower (record W₀ E₀) T ∧
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W₀)) T ∧
    IsClosedSubmanifold n (strictTransform n T.proj W₀)

private theorem smooth_neighbourhood {X : CMfd.{0} n} {W K : Set X} (hW : IsClosed W)
    (E : List (Set X)) (hNo : ¬ (K ∩ singularSet (n := n) W).Nonempty) :
    NeighbourhoodResolution W E K := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW).isOpen_compl⟩
  have hKO : K ⊆ O := fun x hx hs => hNo ⟨x, hx, hs⟩
  have hClosed := hW.preimage (continuous_subtype_val : Continuous (Subtype.val : O → X))
  refine ⟨O, hKO, CMfd.of (n := n) O, .refl, trivial, trivial, ?_⟩
  rw [BlowupTower.proj_refl, HironakaG11PresTowerState.strictTransform_id hClosed]
  refine ⟨hClosed, fun x hx => ?_⟩
  by_contra h
  exact x.property (mem_singularSet_iff.mpr ⟨hx, fun d hd =>
    h ⟨d, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩⟩)

/-- An actual resolution on an open of an open represents an actual resolution
on its literal image open, with the same singular positions and final carrier. -/
private theorem flatten_neighbourhood {X : CMfd.{0} n} {W K : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (E : List (Set X))
    (V : Opens X) (hKV : K ⊆ V)
    (h : NeighbourhoodResolution (X := CMfd.of (n := n) V) ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) ((Subtype.val : V → X) ⁻¹' K)) :
    NeighbourhoodResolution W E K := by
  obtain ⟨U, hKU, Y, T, hT, hStage, hSmooth⟩ := h
  let O : Opens X := ⟨(Subtype.val : V → X) '' (U : Set V),
    V.isOpen.isOpenMap_subtype_val _ U.isOpen⟩
  have hOV : O ≤ V := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hEq (z : V) : z ∈ U ↔ z.val ∈ O := by
    exact ⟨fun hz => ⟨z, hz, rfl⟩, fun ⟨q,hq,hz⟩ => (Subtype.ext hz : q = z) ▸ hq⟩
  let e := (nestedDiffeo (n := n) V U O hEq hOV).symm
  let R := transport e T
  let WU := (Subtype.val : U → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W)
  let EU := (E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : U → V) ⁻¹' ·)
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  have hCarrier : e ⁻¹' WU = WO := rfl
  have hList : EU.map (e ⁻¹' ·) = EO := by
    dsimp only [EU, EO]
    rw [List.map_map, List.map_map]
    rfl
  have hRecord : MarkedIdeal.pullback e (record (X := CMfd.of (n := n) U) WU EU) =
      record (X := CMfd.of (n := n) O) WO EO := by
    change (⟨e ⁻¹' univ, EU.map (e ⁻¹' ·), GermIdeal.pullback (m := n) e
      (vanishingIdeal (n := n) WU), 1⟩ : MarkedIdeal n (CMfd.of (n := n) O)) = _
    rw [preimage_univ, hList, pullback_vanishingIdeal_of_biholomorphism, hCarrier]
  have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V) U
  have hh := transport_isTowerIso e T
  have hTest := (IsTowerIso.isGeoTestTower_iff e HomogenizedGlueingTower.isClosedSubmanifold_univ
    (CartanIrreducible.cartanCoherence WU hWU) hh).mpr hT
  rw [hRecord] at hTest
  have hS : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj WO)) R.tower := by
    rw [← hCarrier]
    apply singular_stages_of_tower_iso _ (hWU.isClosed.preimage e.continuous) e.symm hh.symm
    have hDouble : e.symm ⁻¹' (e ⁻¹' WU) = WU := by
      ext z
      change e (e.symm z) ∈ WU ↔ z ∈ WU
      rw [e.apply_symm_apply]
    rw [hDouble]
    exact hStage
  have hStrict := strictTransform_preimage_of_square e R.back R.tower.contMDiff_proj T.contMDiff_proj
    WU hWU.isClosed (fun z => (proj_transport e T z).symm)
  rw [hCarrier] at hStrict
  refine ⟨O, ?_, R.target, R.tower, hTest, hS, ?_⟩
  · intro x hx
    exact ⟨⟨x, hKV hx⟩, hKU hx, rfl⟩
  · change IsClosedSubmanifold n (strictTransform n R.tower.proj WO)
    rw [hStrict]
    exact (isClosedSubmanifold_preimage_iff R.back).mpr hSmooth

set_option maxHeartbeats 4000000 in
/-- Repeated actual relative clearing yields one finite original full-boundary
singular-centred test on an open containing the compact task. -/
theorem exists_singular_resolution_near_compact_of_relative_phases
    (hPhase : HasRelativeSingularPhases n)
    {X : CMfd.{0} n} {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    NeighbourhoodResolution W E K := by
  have solve : ∀ H : ActualLexHilbertSamuelProfile n,
      ∀ {X : CMfd.{0} n} {W : Set X}, IsComplexAnalyticSubset (n := n) W →
        ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ B ∈ E, B) →
        ∀ (K : Set X), IsCompact K →
          (∀ z ∈ K ∩ singularSet (n := n) W, actualProfile W z ≤ H) → NeighbourhoodResolution W E K := by
    intro H
    induction H using (actual_hilbertSamuel_lex_wellFounded n).wf.induction with
    | h H ih =>
      intro X W hW E hE hDense K hK hBound
      by_cases hNe : (K ∩ singularSet (n := n) W).Nonempty
      · have hKS := hK.inter_right (isClosed_singularSet (n := n) hW.isClosed)
        obtain ⟨a, ha, hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) W)
          (CartanIrreducible.cartanCoherence W hW) _ hKS hNe
        obtain ⟨V, hKV, Y, S, hS, hSStage, hMono, hDrop⟩ := hPhase hW E hE hDense K hK a ha hMax
        let WV := (Subtype.val : V → X) ⁻¹' W
        let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
        let M := record (X := CMfd.of (n := n) V) WV EV
        let KV := (Subtype.val : V → X) ⁻¹' K
        let A := strictTransform n S.proj WV
        let B := (geoTransformAlong M S).E
        let L := S.proj ⁻¹' KV
        have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
        have hVWell : M.IsWellFormed := by
          have hM : (record W E).IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
            CartanIrreducible.cartanCoherence W hW, hE,
            SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
          have hm := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM V
          rw [HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal] at hm
          exact hm
        have hDenseV : WV ⊆ closure (WV \ ⋃ C ∈ EV, C) := by
          dsimp only [WV, EV]
          have hc := V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
            (continuous_subtype_val : Continuous (Subtype.val : V → X)) (W \ ⋃ C ∈ E, C)
          rw [← HironakaEmbeddedBoundary.preimage_biUnion_list, ← preimage_sdiff]
          intro x hx
          exact (Set.ext_iff.mp hc x).mp (hDense hx)
        have hKVcompact : IsCompact KV := by
          rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hKV]
          exact hK
        have hL : IsCompact L := (HironakaLocalPrincipalization.isProperMap_proj S).isCompact_preimage hKVcompact
        have hA : IsComplexAnalyticSubset (n := n) A :=
          HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hWV S
        have hB : IsSNCDivisor n B :=
          (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hVWell S hS).isSNCDivisor
        have hDenseA : A ⊆ closure (A \ ⋃ C ∈ B, C) :=
          strict_transform_dense_off_accumulated_boundary (X := CMfd.of (n := n) V)
            hWV EV hVWell.isSNCDivisor hDenseV S hS hSStage
        have hSingProject := (actual_singular_history_original_regular_protection WV hWV S
          (intrinsic_stage_native_history WV S hSStage)).2.2.2.2.2.1
        have hLower : ∀ z ∈ L ∩ singularSet (n := n) A, actualProfile A z < actualProfile W a := by
          intro z hz
          have hzV : S.proj z ∈ singularSet (n := n) WV := hSingProject hz.2
          have hzX : (S.proj z).val ∈ K ∩ singularSet (n := n) W := by
            rw [HironakaResolutionSpaceLocal.singularSet_preimage_val] at hzV
            exact ⟨hz.1, hzV⟩
          have hRead : HS[n, WV] (S.proj z) = HS[n, W] (S.proj z).val :=
            funext (hilbertSamuelAt_vanishing_actual_open_any V W (S.proj z))
          change toLex (HS[n, A] z) < toLex (HS[n, W] a)
          by_cases hEq : HS[n, WV] (S.proj z) = HS[n, W] a
          · exact hDrop z hEq
          · have hUpper : toLex (HS[n, WV] (S.proj z)) ≤ toLex (HS[n, W] a) := by
              rw [hRead]
              exact hMax _ hzX
            exact (Pi.toLex_monotone (hMono z)).trans_lt (lt_of_le_of_ne hUpper (fun he => hEq (congrArg ofLex he)))
        have hNext : NeighbourhoodResolution A B L := by
          by_cases hNe' : (L ∩ singularSet (n := n) A).Nonempty
          · obtain ⟨b, hb, hMax'⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) A)
              (CartanIrreducible.cartanCoherence A hA) _ (hL.inter_right (isClosed_singularSet (n := n) hA.isClosed)) hNe'
            exact ih (actualProfile A b) ((hLower b hb).trans_le (hBound a ha))
              hA B hB hDenseA L hL hMax'
          · exact smooth_neighbourhood hA.isClosed B hNe'
        obtain ⟨P, hLP, Z, Q, hQ, hQStage, hQSmooth⟩ := hNext
        obtain ⟨U, hKU, hUP, hFinal⟩ := exists_saturated_singular_phase_append hWV EV hVWell.isSNCDivisor
          S hS hSStage KV P hLP Q hQ hQStage
        set D := nestedOpens P (openPreimage S U)
        let e := (nestedOpensDiffeo (n := n) hUP).symm
        let R := transport e (restrict D Q)
        let J := (restrict U S).append R.tower
        obtain ⟨hFinalTest, hFinalStages, _, _, hStrict, _⟩ := hFinal
        apply flatten_neighbourhood hW E V hKV
        refine ⟨U, hKU, R.target, J, hFinalTest, hFinalStages, ?_⟩
        rw [hStrict]
        exact (isClosedSubmanifold_preimage_iff R.back).mpr
          (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hQSmooth (openPreimage Q D))
      · exact smooth_neighbourhood hW.isClosed E hNe
  by_cases hNe : (K ∩ singularSet (n := n) W).Nonempty
  · obtain ⟨a, ha, hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW)
      _ (hK.inter_right (isClosed_singularSet (n := n) hW.isClosed)) hNe
    exact solve (actualProfile W a) hW E hE hDense K hK hMax
  · exact smooth_neighbourhood hW.isClosed E hNe

end
end Hironaka.HironakaG8RelativeLexInduction
