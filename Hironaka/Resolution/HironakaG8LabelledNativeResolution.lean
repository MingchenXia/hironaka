import Hironaka.Resolution.HironakaG8LabelledNativeHistory
import Hironaka.Resolution.HironakaSaturatedTowerAppend
import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaActualCompactHSMaximalProfile

/-! Produce a finite labelled native history around every compact base
task by decreasing the attained entire singular Hilbert--Samuel profile. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LabelledNativeResolution

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport NormalCrossings MaxLocusLocal
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaG8NativePhaseCertificate
  HironakaG8LabelledNativeHistory HironakaSaturatedTowerAppend HironakaResolutionSpaceLocal
  HironakaActualCompactHSMaximalProfile HironakaActualHilbertSamuelLexOrder HironakaActualHilbertSamuelWellFounded
  HironakaActualVanishingIntrinsicHSTransport HironakaG8DenseBoundaryRestart
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaEmbeddedBoundary NormalCrossingsInvariance HomogenizedGlueingTower HironakaHolomorphicJetRankLoci

variable {n : ℕ} {X : CMfd.{0} n}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

private abbrev original {B : CMfd.{0} n} (W : Set B) (E : List (Set B)) : MarkedIdeal n B :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

private def realisedProfile (W : Set X) (x : X) : ActualLexHilbertSamuelProfile n :=
  ⟨toLex (HS[W] x), analytic_hilbertSamuel_realizable (wholeChartStalkIdeal
    (vanishingIdeal (n := n) W) x x (mem_chart_source (ComplexModel n) x))⟩

/-- Genuine stages of one finite history around the compact task. The
predicate on labels records the recursive upper bound when needed. -/
def LabelledNeighbourhood (W : Set X) (E : List (Set X)) (K : Set X) (p : (ℕ → ℕ) → Prop) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y)
    (L : List (ℕ → ℕ)),
    LabelledNativeTower n ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·))
      ((Subtype.val : O → X) ⁻¹' K) T L ∧ ∀ h ∈ L, p h

private theorem labelledNeighbourhood_of_smooth_task {W K : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hNo : ¬ (K ∩ singularSet (n := n) W).Nonempty) (p : (ℕ → ℕ) → Prop) :
    LabelledNeighbourhood W E K p := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hKO : K ⊆ O := fun x hx hxS => hNo ⟨x,hx,hxS⟩
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hEO := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  refine ⟨O,hKO,CMfd.of (n := n) O,.refl,[],.smooth hWO hEO ?_,by simp⟩
  refine ⟨hWO.isClosed,fun x hx => ?_⟩
  by_contra h
  exact x.property (mem_singularSet_iff.mpr ⟨hx,fun d hd =>
    h ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hd⟩⟩)

private theorem labelledNeighbourhood_flatten {W K : Set X} {E : List (Set X)}
    {p : (ℕ → ℕ) → Prop} (V : Opens X) (hKV : K ⊆ V)
    (h : LabelledNeighbourhood (X := CMfd.of (n := n) V) ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) ((Subtype.val : V → X) ⁻¹' K) p) :
    LabelledNeighbourhood W E K p := by
  obtain ⟨U,hKU,Y,T,L,hTrace,hLabels⟩ := h
  let O : Opens X := ⟨(Subtype.val : V → X) '' (U : Set V),V.isOpen.isOpenMap_subtype_val _ U.isOpen⟩
  have hOV : O ≤ V := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have hEq (x : V) : x ∈ U ↔ x.val ∈ O :=
    ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,hx⟩ => (Subtype.ext hx : y = x) ▸ hy⟩
  let e := (nestedDiffeo (n := n) V U O hEq hOV).symm
  let tr := transport e T
  have hEtrace : ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : U → V) ⁻¹' ·)).map
      (e ⁻¹' ·) = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    rw [List.map_map,List.map_map]
    rfl
  have hT := hTrace.of_isTowerIso (transport_isTowerIso e T)
  rw [hEtrace] at hT
  refine ⟨O,?_,tr.target,tr.tower,L,hT,hLabels⟩
  intro x hx
  exact ⟨⟨x,hKV hx⟩,hKU hx,rfl⟩

/-- Finite labelled native singular resolution over the arbitrary
compact base task, with no supplied phase or resolution service. -/
theorem exists_labelled_native_resolution_near_compact (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (K : Set X) (hK : IsCompact K) :
    LabelledNeighbourhood W E K (fun _ => True) := by
  have solve : ∀ b : ActualLexHilbertSamuelProfile n,
      ∀ {X : CMfd.{0} n} {W : Set X}, IsComplexAnalyticSubset (n := n) W →
        ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ B ∈ E, B) →
        ∀ (K : Set X), IsCompact K →
          (∀ x ∈ K ∩ singularSet (n := n) W, realisedProfile W x ≤ b) →
          LabelledNeighbourhood W E K (fun H => toLex H ≤ b.val) := by
    intro b
    induction b using (actual_hilbertSamuel_lex_wellFounded n).wf.induction with
    | h b ih =>
      intro X W hW E hE hDense K hK hBound
      by_cases hNe : (K ∩ singularSet (n := n) W).Nonempty
      · obtain ⟨a,ha,hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) W)
          (CartanIrreducible.cartanCoherence W hW) _ (hK.inter_right (isClosed_singularSet hW.isClosed)) hNe
        obtain ⟨V,hKV,Y,S,hPhase⟩ := exists_actual_native_phase_near_compact hn hW E hE hDense K hK a ha hMax
        let WV := (Subtype.val : V → X) ⁻¹' W
        let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
        let KV := (Subtype.val : V → X) ⁻¹' K
        let A := strictTransform n S.proj WV
        let B := (geoTransformAlong (original WV EV) S).E
        let L := S.proj ⁻¹' KV
        have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
        have hEV : IsSNCDivisor n EV :=
          isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
        have hTrans : IsTransverse n (univ : Set V) EV :=
          SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hEV
        have hVWell : (original (B := CMfd.of (n := n) V) WV EV).IsWellFormed :=
          ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence WV hWV,hEV,hTrans⟩
        have hDenseV : WV ⊆ closure (WV \ ⋃ C ∈ EV, C) := by
          dsimp only [WV,EV]
          have hc := V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
            (continuous_subtype_val : Continuous (Subtype.val : V → X)) (W \ ⋃ C ∈ E, C)
          rw [← preimage_biUnion_list,← preimage_sdiff]
          intro x hx
          exact (Set.ext_iff.mp hc x).mp (hDense hx)
        have hKVcompact : IsCompact KV :=
          (Topology.IsInducing.subtypeVal.isCompact_preimage_iff (fun x hx => ⟨⟨x,hKV hx⟩,rfl⟩)).mpr hK
        have hL := (HironakaLocalPrincipalization.isProperMap_proj S).isCompact_preimage hKVcompact
        have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hWV S
        have hB : IsSNCDivisor n B :=
          (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hVWell S hPhase.test).isSNCDivisor
        have hDenseA := strict_transform_dense_off_accumulated_boundary (X := CMfd.of (n := n) V)
          hWV EV hEV hDenseV S hPhase.test hPhase.singular
        have hMaxV : ∀ x ∈ KV ∩ singularSet (n := n) WV, toLex (HS[WV] x) ≤ toLex (HS[W] a) := by
          rintro x ⟨hx,hS⟩
          change x ∈ singularSet (n := n) ((Subtype.val : V → X) ⁻¹' W) at hS
          rw [singularSet_preimage_val] at hS
          change toLex (HS[(Subtype.val : V → X) ⁻¹' W] x) ≤ toLex (HS[W] a)
          rw [funext (hilbertSamuelAt_vanishing_actual_open_any V W x)]
          exact hMax _ ⟨hx,hS⟩
        have hSingProject := (actual_singular_history_original_regular_protection WV hWV S
          (intrinsic_stage_native_history WV S hPhase.singular)).2.2.2.2.2.1
        have hLower (z : Y) (hz : z ∈ L ∩ singularSet (n := n) A) :
            realisedProfile A z < realisedProfile W a := by
          change toLex (HS[A] z) < toLex (HS[W] a)
          by_cases hzLevel : HS[WV] (S.proj z) = HS[W] a
          · exact hPhase.strictDrop z hzLevel
          · exact (Pi.toLex_monotone (hPhase.nonincrease z)).trans_lt
              (lt_of_le_of_ne (hMaxV _ ⟨hz.1,hSingProject hz.2⟩) (fun he => hzLevel (congrArg ofLex he)))
        have hNext : LabelledNeighbourhood A B L (fun H => toLex H < toLex (HS[W] a)) := by
          by_cases hNe' : (L ∩ singularSet (n := n) A).Nonempty
          · obtain ⟨c,hc,hMax'⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) A)
              (CartanIrreducible.cartanCoherence A hA) _ (hL.inter_right (isClosed_singularSet hA.isClosed)) hNe'
            obtain ⟨P,hLP,Z,Q,labels,hTrace,hLabels⟩ :=
              ih (realisedProfile A c) ((hLower c hc).trans_le (hBound a ha)) hA B hB hDenseA L hL hMax'
            exact ⟨P,hLP,Z,Q,labels,hTrace,fun H hH => (hLabels H hH).trans_lt (hLower c hc)⟩
          · exact labelledNeighbourhood_of_smooth_task hA hB hNe' _
        obtain ⟨P,hLP,Z,Q,labels,hTrace,hLabels⟩ := hNext
        obtain ⟨U,hKU,hUP,_⟩ := exists_saturated_tower_append S KV P hLP Q
        have hRecorded := LabelledNativeTower.prepend_with_saturated_base hWV hEV hPhase hMaxV
          P Q hTrace.test_and_singular.1 hTrace hLabels U hUP
        apply labelledNeighbourhood_flatten V hKV
        refine ⟨U,hKU,_,_,HS[W] a :: labels,hRecorded,?_⟩
        intro H hH
        rcases List.mem_cons.mp hH with rfl | hMem
        · exact hBound a ha
        · exact (hLabels H hMem).le.trans (hBound a ha)
      · exact labelledNeighbourhood_of_smooth_task hW hE hNe _
  by_cases hNe : (K ∩ singularSet (n := n) W).Nonempty
  · obtain ⟨a,ha,hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n) W)
      (CartanIrreducible.cartanCoherence W hW) _ (hK.inter_right (isClosed_singularSet hW.isClosed)) hNe
    obtain ⟨O,hKO,Y,T,L,hTrace,_⟩ := solve (realisedProfile W a) hW E hE hDense K hK hMax
    exact ⟨O,hKO,Y,T,L,hTrace,fun _ _ => trivial⟩
  · exact labelledNeighbourhood_of_smooth_task hW hE hNe _

end
end Hironaka.HironakaG8LabelledNativeResolution
