import Hironaka.Resolution.HironakaG8HereditaryDiscreteFiniteService
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8HereditaryDiscreteScheduler
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8HereditaryDiscreteFiniteService HironakaUniformHistoricalSuccessorOriginalRegular NormalCrossings

/-- A geometric class with hereditary discrete singular loci and an original-test bridge. -/
structure DiscreteHistoryClass (n : ℕ) where
  holds : ∀ (A : CMfd.{0} n), Set A → Prop
  discrete : ∀ (A : CMfd.{0} n) (V : Set A), IsComplexAnalyticSubset (n := n) V → holds A V →
    DiscreteTopology (singularSet (n := n) V)
  next : ∀ {A B : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V → holds A V →
    ∀ (T : BlowupTower A B),
      StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj V)) T →
      holds B (strictTransform n T.proj V)
  originalTest : ∀ {A B : CMfd.{0} n} (V : Set A), IsComplexAnalyticSubset (n := n) V → holds A V →
    ∀ (E : List (Set A)), IsSNCDivisor n E → ∀ (T : BlowupTower A B),
      StageCentres (fun Q C => C ⊆ singularSet (n := n) (strictTransform n Q.proj V)) T →
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) V,1⟩ : MarkedIdeal n A) T

/-- The current singular points over any compact base task are finite. -/
theorem current_singular_over_compact_finite {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (K : Set X) (hK : IsCompact K) (T : BlowupTower X Y)
    (hVT : H.holds Y (strictTransform n T.proj W)) :
    (singularSet (n := n) (strictTransform n T.proj W) ∩ T.proj ⁻¹' K).Finite := by
  have _ := hH
  have hV := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  let discreteT : DiscreteTopology (singularSet (n := n) (strictTransform n T.proj W)) :=
    H.discrete Y _ hV hVT
  have hClosed : IsClosed (singularSet (n := n) (strictTransform n T.proj W) ∩ T.proj ⁻¹' K) :=
    (isClosed_singularSet hV.isClosed).inter (hK.isClosed.preimage T.contMDiff_proj.continuous)
  have hCompact := ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hClosed inter_subset_right
  exact hCompact.finite ((isDiscrete_iff_discreteTopology.mpr inferInstance).mono inter_subset_left)

/-- A genuine finite singular-centred tower serves one compact base task. -/
theorem hereditary_compact_task_block {n : ℕ} (hn : 0<n) {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (K : Set X) (hK : IsCompact K) (T : BlowupTower X Y)
    (hVT : H.holds Y (strictTransform n T.proj W)) :
    ∃ (Z : CMfd.{0} n) (S : BlowupTower Y Z),
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj (strictTransform n T.proj W))) S ∧
      Disjoint (singularSet (n := n) (strictTransform n (T.append S).proj W))
        ((T.append S).proj ⁻¹' K) := by
  let V := strictTransform n T.proj W
  let F := singularSet (n := n) V ∩ T.proj ⁻¹' K
  have hV := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  obtain ⟨Z,S,hStage,hOver,hEmpty⟩ := hereditary_discrete_finite_subset_service_core hn V F
    H.holds H.discrete H.next hV hVT
    (current_singular_over_compact_finite W hW H hH K hK T hVT) inter_subset_left
  refine ⟨Z,S,hStage,?_⟩
  have hStrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W
  rw [← BlowupTower.proj_append] at hStrict
  apply disjoint_left.mpr
  intro z hzSing hzK
  have hzSing' : z ∈ singularSet (n := n) (strictTransform n S.proj V) := by
    simpa only [hStrict,V] using hzSing
  have hzK' : T.proj (S.proj z) ∈ K := by
    simpa only [BlowupTower.proj_append,Set.mem_preimage,Function.comp_apply] using hzK
  have hParent := (actual_singular_history_original_regular_protection V hV S
    (intrinsic_stage_native_history V S hStage)).2.2.2.2.2.1
  have hBad : z ∈ singularSet (n := n) (strictTransform n S.proj V) ∩ S.proj ⁻¹' F :=
    ⟨hzSing',hParent hzSing',hzK'⟩
  rw [hEmpty] at hBad
  exact hBad
/-- On a singular-centred prefix choose its finite serving block; otherwise use
an empty continuation. -/
noncomputable def hereditaryNext {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y) : Σ Z : CMfd.{0} n, BlowupTower Y Z :=
  if hT : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T then
    ⟨Classical.choose (hereditary_compact_task_block hn W hW H hH (K j) (hK j) T (H.next W hW hH T hT)),
      Classical.choose (Classical.choose_spec (hereditary_compact_task_block hn W hW H hH (K j) (hK j) T (H.next W hW hH T hT)))⟩
  else ⟨Y,.refl⟩

theorem hereditaryNext_spec {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (strictTransform n T.proj W))) (hereditaryNext hn W hW H hH K hK j T).2 ∧
    Disjoint (singularSet (n := n) (strictTransform n (T.append (hereditaryNext hn W hW H hH K hK j T).2).proj W))
      ((T.append (hereditaryNext hn W hW H hH K hK j T).2).proj ⁻¹' K j) := by
  have hEq : hereditaryNext hn W hW H hH K hK j T =
      ⟨Classical.choose (hereditary_compact_task_block hn W hW H hH (K j) (hK j) T (H.next W hW hH T hT)),
        Classical.choose (Classical.choose_spec (hereditary_compact_task_block hn W hW H hH (K j) (hK j) T (H.next W hW hH T hT)))⟩ := by
    unfold hereditaryNext
    exact dif_pos hT
  rw [hEq]
  exact Classical.choose_spec (Classical.choose_spec (hereditary_compact_task_block hn W hW H hH (K j) (hK j) T (H.next W hW hH T hT)))

theorem hereditaryNext_test {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (j : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T) :
    IsGeoTestTower (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
      (hereditaryNext hn W hW H hH K hK j T).2 := by
  have _ := hTest
  by_cases hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  · have hS := (hereditaryNext_spec hn W hW H hH K hK j T hStage).1
    have hApp := intrinsic_stage_append W T (hereditaryNext hn W hW H hH K hK j T).2 hStage hS
    have hWhole := H.originalTest W hW hH E hE _ hApp
    exact ((isGeoTestTower_append_iff _ T (hereditaryNext hn W hW H hH K hK j T).2).mp hWhole).2
  · have hEq : hereditaryNext hn W hW H hH K hK j T = ⟨Y,.refl⟩ := by
      unfold hereditaryNext
      exact dif_neg hStage
    rw [hEq]
    trivial


/-- Each actual block boundary makes its assigned base window regular. -/
theorem hereditary_scheduled_sequence_regular {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (U : ℕ → Opens X) (hU : ∀ j, (U j : Set X) ⊆ K j)
    (s : ResolutionInvariantSeq.GrowingSeq X)
    (hBoundary : ∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints
      (hereditaryNext hn W hW H hH K hK) j).2.length =
      HironakaExhaustionBlockLocalFiniteness.blockEndpoints (hereditaryNext hn W hW H hH K hK) j) :
    ∀ a, ∃ N, Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
      ((s.stage N).2.proj ⁻¹' (U a : Set X)) := by
  intro a
  let next := hereditaryNext hn W hW H hH K hK
  let B := HironakaExhaustionBlockLocalFiniteness.blockEndpoints next
  have hAt : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (B a).2 :=
    blockEndpoints_intrinsic_singular W next (fun j {Y} T h => (hereditaryNext_spec hn W hW H hH K hK j T h).1) a
  have hServed := (hereditaryNext_spec hn W hW H hH K hK a (B a).2 hAt).2
  have hReg : Disjoint (singularSet (n := n) (strictTransform n (B (a+1)).2.proj W))
      ((B (a+1)).2.proj ⁻¹' (U a : Set X)) :=
    hServed.mono_right (preimage_mono (hU a))
  refine ⟨(B (a+1)).2.length,?_⟩
  rw [hBoundary (a+1)]
  exact hReg

/-- A compact exhaustion produces actual serving blocks and a finite smooth
endpoint or a locally finite singular-centred original-test history. -/
theorem hereditary_intrinsic_singular_service_schedule {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j))
    (U : ℕ → Opens X) (hU : ∀ j, (U j : Set X) ⊆ K j)
    (hcover : ∀ x : X, ∃ j, x ∈ U j) :
    let next := hereditaryNext hn W hW H hH K hK
    (∃ a, (∀ b, a ≤ b → HironakaExhaustionBlockLocalFiniteness.blockEndpoints next b =
          HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a) ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      singularSet (n := n) (strictTransform n (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2.proj W) = ∅) ∨
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j).2.length =
        HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j) ∧
      (∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2) ∧
      LocallyFinite (HironakaLocallyFiniteResolutionSequence.centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U a))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N r)) := by
  apply intrinsic_singular_service_schedule W hW K (hereditaryNext hn W hW H hH K hK)
    (fun j {Y} T hStage => (hereditaryNext_spec hn W hW H hH K hK j T hStage).1)
    (fun j {Y} T hStage => (hereditaryNext_spec hn W hW H hH K hK j T hStage).2)
    (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
    (hereditaryNext_test hn W hW H hH E hE K hK) U hU hcover

/-- Compact exhaustion and its interiors supply all scheduler tasks internally. -/
theorem hereditary_exists_intrinsic_singular_service_schedule {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (H : DiscreteHistoryClass n) (hH : H.holds X W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃ (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j)) (U : ℕ → Opens X),
      (∀ j, (U j : Set X) ⊆ K j) ∧ (∀ x : X, ∃ j, x ∈ U j) ∧
    let next := hereditaryNext hn W hW H hH K hK
    (∃ a, (∀ b, a ≤ b → HironakaExhaustionBlockLocalFiniteness.blockEndpoints next b =
          HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a) ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2 ∧
      singularSet (n := n) (strictTransform n (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next a).2.proj W) = ∅) ∨
    ∃ s : ResolutionInvariantSeq.GrowingSeq X,
      (∀ j, s.stage (HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j).2.length =
        HironakaExhaustionBlockLocalFiniteness.blockEndpoints next j) ∧
      (∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2) ∧
      LocallyFinite (HironakaLocallyFiniteResolutionSequence.centreImage s) ∧
      ∀ a, ∃ N, ∀ r, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U a))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N r)) := by
  let locallyCompactX : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let J := CompactExhaustion.choice X
  let K : ℕ → Set X := fun j => J (j+1)
  let U : ℕ → Opens X := fun j => ⟨interior (K j),isOpen_interior⟩
  have hK : ∀ j, IsCompact (K j) := fun j => J.isCompact (j+1)
  have hU : ∀ j, (U j : Set X) ⊆ K j := fun _ => interior_subset
  have hCover : ∀ x : X, ∃ j, x ∈ U j := by
    intro x
    obtain ⟨j,hj⟩ := J.exists_mem x
    exact ⟨j,J.subset_interior_succ j hj⟩
  exact ⟨K,hK,U,hU,hCover,hereditary_intrinsic_singular_service_schedule hn W hW H hH E hE K hK U hU hCover⟩

end
end Hironaka.HironakaG8HereditaryDiscreteScheduler
