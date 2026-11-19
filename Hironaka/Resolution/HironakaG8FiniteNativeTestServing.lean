import Hironaka.Resolution.HironakaG8CanonicalNativeServingRank
import Hironaka.Resolution.HironakaG8ActualHighestProfileRestart
import Hironaka.Resolution.HironakaG8SaturatedPrefixAppend
import Hironaka.Resolution.HironakaG8LocalPureFinish

/-! Finite original TEST serving by actual native Hilbert--Samuel phases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteNativeTestServing
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaEmbeddedAnalytic HironakaBaseChange NormalCrossings NormalCrossingsInvariance
  HironakaStageCenters HironakaG8NativePhaseCertificate HironakaG8CanonicalNativeServingRank
  HironakaG8ActualHighestProfileRestart HironakaG8SaturatedPrefixAppend HironakaG8LocalPureFinish
  HironakaG8LabelledOriginalCanonicalPrefixes HironakaActualHilbertSamuelLexOrder
  HironakaHolomorphicJetChartInvariance HironakaActualCompactHSMaximalProfile HironakaLocalPrincipalization

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}
local notation "HS[" U "]" => hilbertSamuelAt (vanishingIdeal (n := n+1) U)
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) : MarkedIdeal (n+1) A :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

/-- The literal mark-one test and intrinsic geometry carried between
serving blocks. The carrier can have arbitrary codimension. -/
structure NativeTestState (W : Set X) (E : List (Set X)) (P : BlowupTower X Y) : Prop where
  analytic : IsComplexAnalyticSubset (n := n+1) W
  snc : IsSNCDivisor (n+1) E
  dense : W ⊆ closure (W \ ⋃ H ∈ E, H)
  tested : IsGeoTestTower (whole W E) P
  singular : StageCentres
    (fun T C => C ⊆ singularSet (n := n+1) (strictTransform (n+1) T.proj W)) P

/-- Produce one actual highest-profile serving block for the current
compact singular fibre, with the same native chart-prefix certificate
and original mark-one TEST on the physically appended clipped history. -/
theorem exists_highest_native_test_serving_step
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} (hP : NativeTestState W E P)
    (K : Set X) (hK : IsCompact K) :
    let U := strictTransform (n+1) P.proj W
    let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
    F.Nonempty →
    ∃ a ∈ F, (∀ x ∈ F, toLex (HS[U] x) ≤ toLex (HS[U] a)) ∧
      ∃ s : NativeServingStep W E P K (HS[U] a),
      RawEpochChartPrefixes (Nat.succ_pos n)
        ((Subtype.val : s.phaseOpen → Y) ⁻¹' U)
        ((geoTransformAlong (whole W E) P).E.map ((Subtype.val : s.phaseOpen → Y) ⁻¹' ·))
        (HS[U] a) s.phaseTower ∧
      NativeTestState s.nextCarrier s.nextBoundary s.tower := by
  dsimp only
  intro hNe
  obtain ⟨a,ha,hMax,_,O,V,hKV,hVO,Z,S,hPhase,hRaw,_⟩ :=
    exists_actual_highest_profile_restart_over_compact_task (Nat.succ_pos n) hP.analytic E
      hP.snc hP.dense P hP.tested hP.singular K hK hNe
  have hKO : P.proj ⁻¹' K ⊆ O := fun y hy => hVO (hKV hy)
  obtain ⟨V',hKV',hV'O,hTest,hStage,_,_,_,_⟩ :=
    exists_saturated_singular_phase_append hP.analytic E hP.snc P hP.tested hP.singular
      K O hKO S hPhase.test hPhase.singular
  let s : NativeServingStep W E P K (HS[strictTransform (n+1) P.proj W] a) :=
    ⟨O,Z,S,hPhase,V',hKV',hV'O⟩
  refine ⟨a,ha,hMax,s,hRaw,?_,?_,?_,?_,?_⟩
  · exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hP.analytic V'
  · exact isSNCDivisor_map_preimage (pullsBackCoordinates_val V') continuous_subtype_val hP.snc
  · exact dense_complement_restrict W E hP.dense V'
  · exact hTest
  · exact hStage


/-- A finite succession of actual native TEST phases on their successive
literal clipped histories. The terminal node clears the compact singular fibre. -/
inductive NativeTestServingTrace :
    {A B : CMfd.{0} (n+1)} → (W : Set A) → List (Set A) → BlowupTower A B → Set A →
      List (ActualAnalyticLexHilbertSamuelProfile (n+1)) → Prop
  | done {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      (state : NativeTestState W E P)
      (clear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))) :
      NativeTestServingTrace W E P K []
  | next {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
      (a : B) (aOn : a ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      (highest : ∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
        toLex (HS[strictTransform (n+1) P.proj W] x) ≤ toLex (HS[strictTransform (n+1) P.proj W] a))
      (s : NativeServingStep W E P K (HS[strictTransform (n+1) P.proj W] a))
      (raw : RawEpochChartPrefixes (Nat.succ_pos n)
        ((Subtype.val : s.phaseOpen → B) ⁻¹' strictTransform (n+1) P.proj W)
        ((geoTransformAlong (whole W E) P).E.map ((Subtype.val : s.phaseOpen → B) ⁻¹' ·))
        (HS[strictTransform (n+1) P.proj W] a) s.phaseTower)
      (state : NativeTestState s.nextCarrier s.nextBoundary s.tower)
      (rankDrop : ∀ z ∈ s.tower.proj ⁻¹' s.nextTask ∩ singularSet (n := n+1)
          (strictTransform (n+1) s.tower.proj s.nextCarrier),
        realizedProfile (strictTransform (n+1) s.tower.proj s.nextCarrier) z <
          realizedProfile (strictTransform (n+1) P.proj W) a)
      (rest : NativeTestServingTrace s.nextCarrier s.nextBoundary s.tower s.nextTask labels) :
      NativeTestServingTrace W E P K (realizedProfile (strictTransform (n+1) P.proj W) a :: labels)

/-- The actual geometric serving law terminates from an arbitrary
original mark-one singular test prefix over a compact task. -/
theorem exists_finite_native_test_serving
    {W : Set X} {E : List (Set X)} (P : BlowupTower X Y)
    (state : NativeTestState W E P) (K : Set X) (hK : IsCompact K) :
    ∃ labels, NativeTestServingTrace W E P K labels := by
  classical
  have solve : ∀ bound : ActualAnalyticLexHilbertSamuelProfile (n+1),
      ∀ {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} (P : BlowupTower A B)
        (_state : NativeTestState W E P) (K : Set A) (_hK : IsCompact K),
        (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
          realizedProfile (strictTransform (n+1) P.proj W) x ≤ bound) →
        ∃ labels, NativeTestServingTrace W E P K labels := by
    intro bound
    induction bound using (actual_analyticHilbertSamuel_lex_wellFounded (n+1)).wf.induction with
    | h bound ih =>
      intro A B W E P hs K hK hBound
      by_cases hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      · exact ⟨[],.done hs hClear⟩
      obtain ⟨a,ha,hMax,s,hRaw,hNext⟩ := exists_highest_native_test_serving_step hs K hK
        (not_disjoint_iff_nonempty_inter.mp hClear)
      have hK' : IsCompact s.nextTask :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (fun x hx => ⟨⟨x,s.covers hx⟩,rfl⟩)).mpr hK
      let U' := strictTransform (n+1) s.tower.proj s.nextCarrier
      let F' := s.tower.proj ⁻¹' s.nextTask ∩ singularSet (n := n+1) U'
      have hDrop (z : s.tail.target) (hz : z ∈ F') :
          realizedProfile U' z < realizedProfile (strictTransform (n+1) P.proj W) a :=
        clipped_singular_native_profile_drop W hs.analytic P s.phaseOpen s.phaseTower
          s.baseOpen s.saturation K _ _ s.phase hMax z hz.1 hz.2
      by_cases hNe' : F'.Nonempty
      · have hU' := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj
          hNext.analytic s.tower
        have hComp' : IsCompact F' := ((isProperMap_proj s.tower).isCompact_preimage hK').inter_right
          (isClosed_singularSet hU'.isClosed)
        obtain ⟨b,hb,hMax'⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n+1) U')
          (CartanIrreducible.cartanCoherence U' hU') F' hComp' hNe'
        obtain ⟨ls,hls⟩ := ih (realizedProfile U' b) ((hDrop b hb).trans_le (hBound a ha))
          s.tower hNext s.nextTask hK' hMax'
        exact ⟨_,.next a ha hMax s hRaw hNext hDrop hls⟩
      · exact ⟨_,.next a ha hMax s hRaw hNext hDrop (.done hNext (by
          by_contra hh
          exact hNe' (not_disjoint_iff_nonempty_inter.mp hh)))⟩
  by_cases hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
  · exact ⟨[],.done state hClear⟩
  let U := strictTransform (n+1) P.proj W
  let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj state.analytic P
  have hComp : IsCompact F := ((isProperMap_proj P).isCompact_preimage hK).inter_right
    (isClosed_singularSet hU.isClosed)
  obtain ⟨a,_,hm⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n+1) U)
    (CartanIrreducible.cartanCoherence U hU) F hComp (not_disjoint_iff_nonempty_inter.mp hClear)
  exact solve (realizedProfile U a) P state K hK hm

/-- The unrestricted geometric initialization is the original mark-one
record on the literal empty physical tower. -/
theorem exists_finite_native_test_serving_from_refl
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (K : Set X) (hK : IsCompact K) :
    ∃ labels, NativeTestServingTrace W E (.refl : BlowupTower X X) K labels :=
  exists_finite_native_test_serving .refl ⟨hW,hE,hDense,trivial,trivial⟩ K hK


/-- Any strict bound on the current singular fibre bounds all subsequent labels. -/
theorem NativeTestServingTrace.labels_lt_of_current_lt
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (h : NativeTestServingTrace W E P K labels)
    {bound : ActualAnalyticLexHilbertSamuelProfile (n+1)}
    (hBound : ∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
      realizedProfile (strictTransform (n+1) P.proj W) x < bound) :
    ∀ lab ∈ labels, lab < bound := by
  induction h with
  | done => simp
  | next a ha highest s raw state drop rest ih =>
    intro lab hLab
    rcases List.mem_cons.mp hLab with rfl | hTail
    · exact hBound a ha
    · exact ih (fun z hz => (drop z hz).trans (hBound a ha)) lab hTail

/-- The service trace records strictly descending realized labels. -/
theorem NativeTestServingTrace.strict_labels
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (h : NativeTestServingTrace W E P K labels) :
    labels.Pairwise (fun a b => b < a) := by
  induction h with
  | done => exact List.Pairwise.nil
  | next a ha highest s raw state drop rest ih =>
    exact List.Pairwise.cons (fun lab hlab => rest.labels_lt_of_current_lt drop lab hlab) ih

open HironakaG8OpenHoloEmbeddingComposition

/-- Read the actual terminal TEST on a single open embedding of the
initial base, with the same compact task and ordered initial boundary. -/
theorem NativeTestServingTrace.endpoint
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (h : NativeTestServingTrace W E P K labels) :
    ∃ (A : CMfd.{0} (n+1)) (j : A → X), IsOpenHoloEmbedding (n+1) j ∧ K ⊆ range j ∧
      ∃ (B : CMfd.{0} (n+1)) (T : BlowupTower A B),
      NativeTestState (j ⁻¹' W) (E.map (j ⁻¹' ·)) T ∧
      Disjoint (T.proj ⁻¹' (j ⁻¹' K)) (singularSet (n := n+1) (strictTransform (n+1) T.proj (j ⁻¹' W))) := by
  induction h with
  | @done A B W E P K state clear =>
    let e : A ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯
        CMfd.of (n := n+1) (⊤ : Opens A) :=
      { toFun := fun y => ⟨y,trivial⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (V := (⊤ : Opens A))
          contMDiff_id (fun _ => trivial)
        contMDiff_invFun := contMDiff_subtype_val }
    refine ⟨A,id,⟨⊤,e,fun _ => rfl⟩,fun x _ => ⟨x,rfl⟩,B,P,?_,?_⟩
    · simpa only [preimage_id,List.map_id'] using state
    · simpa only [preimage_id] using clear
  | @next A B W E P K labels _ _ _ s _ _ _ _ ih =>
    obtain ⟨C,j,hj,hCover,D,T,hState,hClear⟩ := ih
    let i := (Subtype.val : s.baseOpen → A)
    have hi : IsOpenHoloEmbedding (n+1) i := isOpenHoloEmbedding_val s.baseOpen
    refine ⟨C,i ∘ j,isOpenHoloEmbedding_comp (A := A) (B := s.source) (C := C) hi hj,?_,D,T,?_,hClear⟩
    · intro x hx
      let x₀ : s.baseOpen := ⟨x,s.covers hx⟩
      obtain ⟨y,hy⟩ := hCover (show x₀ ∈ s.nextTask from hx)
      exact ⟨y,congrArg i hy⟩
    · have he : s.nextBoundary.map (j ⁻¹' ·) = E.map ((i ∘ j) ⁻¹' ·) := by
        simp only [NativeServingStep.nextBoundary,List.map_map]
        rfl
      rw [he] at hState
      exact hState

end
end Hironaka.HironakaG8FiniteNativeTestServing
