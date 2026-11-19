import Hironaka.Resolution.HironakaG8FiniteNativeTestServing
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaG8CompactLexInduction

/-! Global physical assembly when the finite native blocks extend across
their working opens with compact centre footprint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8GlobalNativeTestAssembly
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  HironakaEmbeddedAnalytic HironakaBaseChange NormalCrossings
  HironakaStageCenters ResolutionInvariantSpec HironakaG8FiniteNativeTestServing
  HironakaG8IntrinsicSingularBlockSchedule HironakaG8SurfaceLimitEndpoint
  HironakaG8SingularFootprintExtension HironakaG8CompactLexInduction HironakaLocalPrincipalization
  HironakaExhaustionBlockLocalFiniteness HironakaCountableTowerPrefixes
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaResolutionSpaceLocal
  HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaActualLimitProtectedOpen
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  BlowupTowerIsomorphism ResolutionInvariantSeq HomogenizedGlueingTower
  RestrictEmptyTower HironakaActualLocallyFiniteHistoryOverlap HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) : MarkedIdeal (n+1) A :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

/-- The extension obligation for the output of finite native serving:
one actual finite test tail on a literal open covering the task, whose
centres have a compact footprint contained in that same open. -/
def HasCompactFootprintTestBlock (W : Set Y) (E : List (Set Y)) (K : Set Y) : Prop :=
  ∃ (U : Opens Y), K ⊆ U ∧ ∃ (F : Set Y), IsCompact F ∧ F ⊆ U ∧
    ∃ (Z : CMfd.{0} (n+1)) (S : BlowupTower (CMfd.of (n := n+1) U) Z),
      NativeTestState ((Subtype.val : U → Y) ⁻¹' W) (E.map ((Subtype.val : U → Y) ⁻¹' ·)) S ∧
      CentresOver ((Subtype.val : U → Y) ⁻¹' F) S ∧
      Disjoint (S.proj ⁻¹' ((Subtype.val : U → Y) ⁻¹' K))
        (singularSet (n := n+1) (strictTransform (n+1) S.proj ((Subtype.val : U → Y) ⁻¹' W)))

/-- An extendable finite TEST tail gives a literal global append,
including all old boundary slots. -/
theorem global_block_of_compact_footprint
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} (hP : NativeTestState W E P)
    (K : Set X)
    (hBlock : HasCompactFootprintTestBlock (strictTransform (n+1) P.proj W)
      (geoTransformAlong (whole W E) P).E (P.proj ⁻¹' K)) :
    ∃ (Z : CMfd.{0} (n+1)) (Q : BlowupTower Y Z),
      IsGeoTestTower (geoTransformAlong (whole W E) P) Q ∧
      StageCentres (fun T C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) T.proj (strictTransform (n+1) P.proj W))) Q ∧
      Disjoint (singularSet (n := n+1) (strictTransform (n+1) (P.append Q).proj W))
        ((P.append Q).proj ⁻¹' K) := by
  let M := whole W E
  let U := strictTransform (n+1) P.proj W
  let B := (geoTransformAlong M P).E
  let A := whole U B
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hP.analytic P
  obtain ⟨O,hKO,F,hF,hFO,Z,S,hState,hOver,hClear⟩ := hBlock
  have hST : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → Y) A) S := by
    rw [HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal O B U]
    exact hState.tested
  obtain ⟨V,Q,hQT,hQS,_,e,he,_,hProj⟩ := exists_compact_footprint_singular_test_extension
    A HomogenizedGlueingTower.isClosedSubmanifold_univ (CartanIrreducible.cartanCoherence U hU)
    U hU.isClosed O F hF hFO S hOver hST hState.singular
  have hWhole := (original_test_and_singular_stages_append hP.analytic hP.snc
    P Q hP.tested hP.singular hQT hQS).1
  refine ⟨V,Q,(isGeoTestTower_append_iff (𝔪 := M) P Q).1 hWhole |>.2,hQS,?_⟩
  have hStrict := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel (n+1)) O ∞) e S.contMDiff_proj
    (restrict O Q).contMDiff_proj ((Subtype.val : O → Y) ⁻¹' U)
    (hU.isClosed.preimage continuous_subtype_val) (fun z => (he.proj_comm z).symm)
  simp only [Diffeomorph.coe_refl,preimage_id] at hStrict
  rw [strictTransform_restricted_tower O Q U] at hStrict
  apply disjoint_left.mpr
  intro y hy hKy
  have hK' : Q.proj y ∈ P.proj ⁻¹' K := by
    simpa only [BlowupTower.proj_append,mem_preimage,Function.comp_apply] using hKy
  let q : openPreimage Q O := ⟨y,hKO hK'⟩
  let z := e.symm q
  have hEq : e z = q := e.apply_symm_apply q
  have hzOn : z ∈ S.proj ⁻¹' ((Subtype.val : O → Y) ⁻¹' (P.proj ⁻¹' K)) := by
    change (S.proj z).val ∈ P.proj ⁻¹' K
    rw [← hProj z,hEq]
    exact hK'
  have hySing : y ∈ singularSet (n := n+1) (strictTransform (n+1) Q.proj U) := by
    rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp P.contMDiff_proj Q.contMDiff_proj] at hy
    exact hy
  have hqSing : q ∈ singularSet (n := n+1)
      ((Subtype.val : openPreimage Q O → V) ⁻¹' strictTransform (n+1) Q.proj U) := by
    rw [singularSet_preimage_val]
    exact hySing
  have hzSing : z ∈ singularSet (n := n+1)
      (strictTransform (n+1) S.proj ((Subtype.val : O → Y) ⁻¹' U)) := by
    rw [hStrict]
    obtain ⟨hmem,hReg⟩ := mem_singularSet_iff.mp hqSing
    apply mem_singularSet_iff.mpr
    refine ⟨?_,fun k hk => hReg k ?_⟩
    · change e z ∈ ((Subtype.val : openPreimage Q O → V) ⁻¹' strictTransform (n+1) Q.proj U)
      rwa [hEq]
    · have heReg := (CodimOnePartCanonical.regularAtDim_preimage_iff e).mp hk
      rwa [hEq] at heReg
  exact disjoint_left.mp hClear hzOn hzSing


/-- A local-to-global hypothesis for the finite native test-serving blocks.
It is required only at actual tested prefixes of the indicated input. -/
def HasNativeFootprintExtensions (W : Set X) (E : List (Set X)) : Prop :=
  ∀ {B : CMfd.{0} (n+1)} {P : BlowupTower X B},
    NativeTestState W E P → ∀ K : Set X, IsCompact K →
      HasCompactFootprintTestBlock (strictTransform (n+1) P.proj W)
        (geoTransformAlong (whole W E) P).E (P.proj ⁻¹' K)

/-- From every tested prefix, a finite actual global tail clears the
next compact task. Each tail is controlled by the original ordered
mark-one record at that prefix and has intrinsic singular centres. -/
def HasGlobalNativeTestTails (W : Set X) (E : List (Set X)) : Prop :=
  ∀ {B : CMfd.{0} (n+1)} {P : BlowupTower X B},
    NativeTestState W E P → ∀ K : Set X, IsCompact K →
      ∃ (Z : CMfd.{0} (n+1)) (Q : BlowupTower B Z),
        IsGeoTestTower (geoTransformAlong (whole W E) P) Q ∧
        StageCentres (fun T C => C ⊆ singularSet (n := n+1)
          (strictTransform (n+1) T.proj (strictTransform (n+1) P.proj W))) Q ∧
        Disjoint (singularSet (n := n+1) (strictTransform (n+1) (P.append Q).proj W))
          ((P.append Q).proj ⁻¹' K)

/-- Globally available singular TEST tails give a finite resolution or a
locally finite proper endpoint. The support of each finite tail may be
noncompact. Once an exhaustion open is clear, later centres miss it. -/
theorem global_native_test_finite_or_proper_limit_of_global_tails
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (serve : HasGlobalNativeTestTails W E) :
    (∃ (Y : CMfd.{0} (n+1)) (T : BlowupTower X Y),
      NativeTestState W E T ∧ IsClosedSubmanifold (n+1) (strictTransform (n+1) T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      IsIsomorphismOver (n+1) T.proj (singularSet (n := n+1) W)ᶜ) ∨
    ∃ (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)),
      (∀ i, NativeTestState W E (s.stage i).2) ∧
      (∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧ ∀ r,
        ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 V) (tailTower s N r))) ∧
      IsClosedSubmanifold (n+1) (limitStrictTransform s hLF W) ∧
      limitStrictTransform s hLF W = strictTransform (n+1) (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      IsIsomorphismOver (n+1) (gluedProjection s hLF) (singularSet (n := n+1) W)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) := by
  classical
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel (n+1)) X
  let J := CompactExhaustion.choice X
  let K : ℕ → Set X := fun j => J (j+1)
  let U : ℕ → Opens X := fun j => ⟨interior (K j),isOpen_interior⟩
  have hK (a) : IsCompact (K a) := J.isCompact (a+1)
  have hU (a) : (U a : Set X) ⊆ K a := interior_subset
  have hCover (x : X) : ∃ a, x ∈ U a := by
    obtain ⟨a,ha⟩ := J.exists_mem x
    exact ⟨a,J.subset_interior_succ a ha⟩
  let M := whole W E
  let pick := fun j {Y : CMfd.{0} (n+1)} (T : BlowupTower X Y) (hT : NativeTestState W E T) =>
    serve hT (K j) (hK j)
  let next : ∀ (j : ℕ) {Y : CMfd.{0} (n+1)}, BlowupTower X Y →
      Σ Z : CMfd.{0} (n+1), BlowupTower Y Z := fun j {Y} T =>
    if hT : NativeTestState W E T then
      ⟨Classical.choose (pick j T hT),Classical.choose (Classical.choose_spec (pick j T hT))⟩
    else ⟨Y,.refl⟩
  have hStep (a : ℕ) {Y : CMfd.{0} (n+1)} (T : BlowupTower X Y) (hT : NativeTestState W E T) :
      IsGeoTestTower (geoTransformAlong M T) (next a T).2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) P.proj (strictTransform (n+1) T.proj W))) (next a T).2 ∧
      Disjoint (singularSet (n := n+1) (strictTransform (n+1) (T.append (next a T).2).proj W))
        ((T.append (next a T).2).proj ⁻¹' K a) := by
    let Good (Q : Σ Z : CMfd.{0} (n+1), BlowupTower Y Z) : Prop :=
      IsGeoTestTower (geoTransformAlong M T) Q.2 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) P.proj (strictTransform (n+1) T.proj W))) Q.2 ∧
      Disjoint (singularSet (n := n+1) (strictTransform (n+1) (T.append Q.2).proj W))
        ((T.append Q.2).proj ⁻¹' K a)
    change Good (next a T)
    have he : next a T = ⟨Classical.choose (pick a T hT),
        Classical.choose (Classical.choose_spec (pick a T hT))⟩ := dif_pos hT
    rw [he]
    exact Classical.choose_spec (Classical.choose_spec (pick a T hT))
  let B := blockEndpoints next
  have hB := blockEndpoints_extend next
  have hStates : ∀ a, NativeTestState W E (B a).2 := by
    intro a
    induction a with
    | zero => exact ⟨hW,hE,hDense,trivial,trivial⟩
    | succ a ih =>
      have h := hStep a (B a).2 ih
      exact ⟨hW,hE,hDense,(isGeoTestTower_append_iff (𝔪 := M) (B a).2 (next a (B a).2).2).2
        ⟨ih.tested,h.1⟩,intrinsic_stage_append W (B a).2 (next a (B a).2).2 ih.singular h.2.1⟩
  have hReg (a b : ℕ) (hab : a+1 ≤ b) :
      Disjoint (singularSet (n := n+1) (strictTransform (n+1) (B b).2.proj W))
        ((B b).2.proj ⁻¹' K a) := by
    induction b, hab using Nat.le_induction with
    | base => exact (hStep a (B a).2 (hStates a)).2.2
    | succ b _ ih =>
      let T := (B b).2
      let S := (next b T).2
      have hWT := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
      have hp := intrinsic_singular_disjoint_persists hWT (T.proj ⁻¹' K a) ih S
        (hStep b T (hStates b)).2.1
      rw [← StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W,
        ← BlowupTower.proj_append] at hp
      change Disjoint (singularSet (n := n+1) (strictTransform (n+1) (T.append S).proj W))
        ((T.append S).proj ⁻¹' K a)
      simpa only [BlowupTower.proj_append,preimage_comp] using hp
  have hStable (a b : ℕ) (hab : a+1 ≤ b) :
      countCentresMeeting (U a : Set X) (B b).2 = countCentresMeeting (U a : Set X) (B (a+1)).2 := by
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hb ih =>
      let T := (B b).2
      let S := (next b T).2
      have h := count_append_eq_of_current_regular_open hW (U a) T S
        ((hReg a b hb).mono_right (preimage_mono (hU a))) (hStep b T (hStates b)).2.1
      change countCentresMeeting (U a : Set X) (T.append S) = _
      rw [h]
      exact ih
  have hCount : ∀ a, ∃ m, ∀ j, countCentresMeeting (U a : Set X) (B j).2 ≤ m := by
    intro a
    refine ⟨countCentresMeeting (U a : Set X) (B (a+1)).2,fun j => ?_⟩
    rcases le_total j (a+1) with hj | hj
    · obtain ⟨S,hS⟩ := HironakaG3RTaskSchedule.blockEndpoints_prefix next j (a+1) hj
      change countCentresMeeting (U a : Set X) (blockEndpoints next j).2 ≤
        countCentresMeeting (U a : Set X) (blockEndpoints next (a+1)).2
      rw [hS,TowerPreimageCompact.countCentresMeeting_append]
      exact Nat.le_add_right _ _
    · exact (hStable a j hj).le
  rcases unbounded_or_eventually_constant B hB with hUnbounded | hFinite
  · let s := sequenceOfBlocks B hB hUnbounded
    have hBound := sequenceOfBlocks_boundary B hB hUnbounded
    have hLF : LocallyFinite (centreImage s) :=
      locallyFinite_sequenceOfBlocks B hB hUnbounded U hCount hCover
    have hTest := isGeoTestTower_sequenceOfBlocks B hB hUnbounded M (fun i => (hStates i).tested)
    have hStage (i : ℕ) : StageCentres (fun P C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) P.proj W)) (s.stage i).2 := by
      obtain ⟨j,hj⟩ := hUnbounded i
      rw [sequenceOfBlocks_stage B hB hUnbounded hj]
      change StageCentres _ (BlowupTowerSplit.head (B j).2 ((B j).2.length-i))
      apply HironakaActualCoreHistoricalLowerGeometry.stage_centres_prefix _ _
        (BlowupTowerSplit.tail (B j).2 ((B j).2.length-i))
      rw [BlowupTowerSplit.head_append_tail]
      exact (hStates j).singular
    have hRegular : ∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧
        Disjoint (singularSet (n := n+1) (strictTransform (n+1) (s.stage N).2.proj W))
          ((s.stage N).2.proj ⁻¹' (V : Set X)) := by
      intro x
      obtain ⟨a,ha⟩ := hCover x
      refine ⟨U a,(B (a+1)).2.length,ha,?_⟩
      rw [hBound (a+1)]
      exact (hReg a (a+1) le_rfl).mono_right (preimage_mono (hU a))
    have hIso := intrinsic_limit_regular_open_iso W hW s hLF hStage
    have hProtected (x : X) : ∃ (V : Opens X) (N : ℕ), x ∈ V ∧ ∀ r,
        ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 V) (tailTower s N r)) := by
      obtain ⟨a,ha⟩ := hCover x
      obtain ⟨N,hN⟩ := sequenceOfBlocks_empty_tails B hB hUnbounded U hCount a
      exact ⟨U a,N,ha,hN⟩
    have hProper := gluedProjection_isProperMap s hLF
    exact Or.inr ⟨s,hLF,fun i => ⟨hW,hE,hDense,hTest i,hStage i⟩,hProtected,
      intrinsic_limit_strictTransform_smooth W hW s hLF hStage hRegular,
      intrinsic_limit_strictTransform_eq_projection W hW s hLF hStage hIso,
      hProper,proper_regular_open_iso_surjective (Y := CMfd.of (n := n+1) (limitManifold s hLF)) W (gluedProjection s hLF) hProper hIso,hIso,gluedProjection_contMDiff s hLF⟩
  · obtain ⟨a,ha⟩ := hFinite
    let T := (B a).2
    have ht := hStates a
    have hEmpty : singularSet (n := n+1) (strictTransform (n+1) T.proj W) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨c,hc⟩ := hCover (T.proj y)
      have hr := hReg c (max a (c+1)) (le_max_right _ _)
      rw [ha _ (le_max_left _ _)] at hr
      exact disjoint_left.mp hr hy (hU c hc)
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T ht.singular)
    exact Or.inl ⟨_,T,ht,hp.2.2.2.2.2.2.mp hEmpty,hp.2.2.1,
      proper_regular_open_iso_surjective W _ hp.2.2.1 hp.2.1,hp.2.1⟩


/-- Protected finite physical blocks assemble into a proper smooth limit
in every positive ambient dimension. The existence of the indicated
compact footprint extensions is the only local-to-global input. -/
theorem global_native_test_finite_or_proper_limit
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (lift : HasNativeFootprintExtensions W E) :
    (∃ (Y : CMfd.{0} (n+1)) (T : BlowupTower X Y),
      NativeTestState W E T ∧ IsClosedSubmanifold (n+1) (strictTransform (n+1) T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      IsIsomorphismOver (n+1) T.proj (singularSet (n := n+1) W)ᶜ) ∨
    ∃ (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)),
      (∀ i, NativeTestState W E (s.stage i).2) ∧
      (∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧ ∀ r,
        ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 V) (tailTower s N r))) ∧
      IsClosedSubmanifold (n+1) (limitStrictTransform s hLF W) ∧
      limitStrictTransform s hLF W = strictTransform (n+1) (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      IsIsomorphismOver (n+1) (gluedProjection s hLF) (singularSet (n := n+1) W)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) := by
  apply global_native_test_finite_or_proper_limit_of_global_tails W hW E hE hDense
  intro B P hP K hK
  exact global_block_of_compact_footprint hP K (lift hP K hK)

open MarkedIdealTowerTransport HironakaActualOpenEmbeddingVanishingIdeal
  HironakaG3CentresOverGenericFactor HironakaG8LocalPureFinish NormalCrossingsInvariance

/-- Finite native TEST serving supplies a compact-footprint block when
the entire original singular locus on its current source is compact. -/
theorem has_compact_footprint_test_block_of_compact_singular
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) (hSingCompact : IsCompact (singularSet (n := n+1) W)) :
    HasCompactFootprintTestBlock W E K := by
  let F := singularSet (n := n+1) W
  obtain ⟨_,trace⟩ := exists_finite_native_test_serving_from_refl W hW E hE hDense (K ∪ F)
    (hK.union hSingCompact)
  obtain ⟨A,j,hj,hCover,B,T,hState,hClear⟩ := trace.endpoint
  have hOverA : CentresOver (j ⁻¹' F) T := by
    let A₀ := j ⁻¹' W
    let G := singularSet (n := n+1) A₀
    let V : Opens A := ⟨Gᶜ,(isClosed_singularSet hState.analytic.isClosed).isOpen_compl⟩
    have hAvoid := intrinsic_singular_history_avoids_regular_open hState.analytic V
      disjoint_compl_right T hState.singular
    have hOver : CentresOver G T := by
      have h := centresOver_compl_of_centresAvoid V T hAvoid
      change CentresOver Gᶜᶜ T at h
      rwa [compl_compl] at h
    have hSub : G ⊆ j ⁻¹' F := by
      intro x hx
      have hm := mem_singularSet_iff.mp hx
      exact mem_singularSet_iff.mpr
        ⟨hm.1, fun k hk => hm.2 k (hj.regularAtDim_preimage hk)⟩
    clear hClear hCover hAvoid V hState
    induction T with
    | refl => trivial
    | step T C π hπ ih => exact ⟨ih hOver.1,hOver.2.trans (preimage_mono hSub)⟩
  obtain ⟨O,e,he⟩ := hj
  let β := e.symm
  let Q := transport (X' := CMfd.of (n := n+1) O) β T
  have hβ (z : O) : j (β z) = z.val := by rw [he,e.apply_symm_apply]
  have hF (D : Set X) : β ⁻¹' (j ⁻¹' D) = (Subtype.val : O → X) ⁻¹' D := by
    ext x
    change j (β x) ∈ D ↔ x.val ∈ D
    rw [hβ]
  have hKO : K ⊆ O := by
    intro x hx
    obtain ⟨a,rfl⟩ := hCover (Or.inl hx)
    rw [he]
    exact (e a).property
  have hFO : F ⊆ O := by
    intro x hx
    obtain ⟨a,rfl⟩ := hCover (Or.inr hx)
    rw [he]
    exact (e a).property
  let U := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M := whole (j ⁻¹' W) (E.map (j ⁻¹' ·))
  let MO := whole (A := CMfd.of (n := n+1) O) U EO
  have hEq : MarkedIdeal.pullback β M = MO := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ
    · change ((E.map (j ⁻¹' ·)).map (β ⁻¹' ·)) = E.map ((Subtype.val : O → X) ⁻¹' ·)
      rw [List.map_map]
      exact List.map_congr_left (fun D _ => hF D)
    · change GermIdeal.pullback (m := n+1) β (vanishingIdeal (n := n+1) (j ⁻¹' W)) = _
      rw [pullback_vanishingIdeal_of_biholomorphism,hF W]
    · rfl
  have hTest : IsGeoTestTower MO Q.tower := by
    rw [← hEq]
    exact (isGeoTestTower_transport_iff (X' := CMfd.of (n := n+1) O) β
      (CartanIrreducible.cartanCoherence _ hState.analytic) T).2 hState.tested
  have hIso := transport_isTowerIso (X' := CMfd.of (n := n+1) O) β T
  have hO := centresOver_of_isTowerIso hIso (j ⁻¹' F) hOverA
  rw [hF F] at hO
  have hStrict := strictTransform_preimage_of_square β Q.back Q.tower.contMDiff_proj T.contMDiff_proj
    (j ⁻¹' W) hState.analytic.isClosed (fun z => (proj_transport (X' := CMfd.of (n := n+1) O) β T z).symm)
  rw [hF W] at hStrict
  have hClosed : IsClosed U := hW.isClosed.preimage continuous_subtype_val
  have hSing : StageCentres (fun P C => C ⊆ singularSet (n := n+1)
      (strictTransform (n+1) P.proj U)) Q.tower := by
    have hh := singular_stages_of_tower_iso (X' := A) (X := CMfd.of (n := n+1) O)
      (T' := T) (T := Q.tower) (χ := Q.back.symm) U hClosed β.symm hIso.symm
    have hb : β.symm ⁻¹' U = j ⁻¹' W := by
      ext x
      change (e x).val ∈ W ↔ j x ∈ W
      rw [← he x]
    rw [hb] at hh
    exact hh hState.singular
  refine ⟨O,hKO,F,hSingCompact,hFO,Q.target,Q.tower,?_,hO,?_⟩
  · exact ⟨AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O,
      isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE,
      dense_complement_restrict W E hDense O,hTest,hSing⟩
  · apply disjoint_left.mpr
    intro z hz hSingZ
    have hzK : T.proj (Q.back z) ∈ j ⁻¹' (K ∪ F) := by
      change j (T.proj (Q.back z)) ∈ K ∪ F
      rw [← proj_transport (X' := CMfd.of (n := n+1) O) β T z,hβ]
      exact Or.inl hz
    apply disjoint_left.mp hClear hzK
    rw [hStrict] at hSingZ
    have hmem := mem_singularSet_iff.mp hSingZ
    exact mem_singularSet_iff.mpr
      ⟨hmem.1,fun k hk => hmem.2 k ((CodimOnePartCanonical.regularAtDim_preimage_iff Q.back).2 hk)⟩


/-- Compact original singular support supplies the footprint obligation
at every actual tested prefix, because regularity outside its proper
inverse image is preserved. -/
theorem HasNativeFootprintExtensions.of_compact_singular
    (W : Set X) (E : List (Set X)) (hCompact : IsCompact (singularSet (n := n+1) W)) :
    HasNativeFootprintExtensions W E := by
  intro Y P hP K hK
  let U := strictTransform (n+1) P.proj W
  let M := whole W E
  let B := (geoTransformAlong M P).E
  have hp := actual_singular_history_original_regular_protection W hP.analytic P
    (intrinsic_stage_native_history W P hP.singular)
  have hU := hp.2.2.2.1
  have hC : IsCompact (singularSet (n := n+1) U) :=
    (hp.2.2.1.isCompact_preimage hCompact).of_isClosed_subset
      (isClosed_singularSet hU.isClosed) hp.2.2.2.2.2.1
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hP.analytic,hP.snc,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hP.snc⟩
  have hB : IsSNCDivisor (n+1) B :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM P hP.tested).isSNCDivisor
  have hD := HironakaG8DenseBoundaryRestart.strict_transform_dense_off_accumulated_boundary
    hP.analytic E hP.snc hP.dense P hP.tested hP.singular
  exact has_compact_footprint_test_block_of_compact_singular U hU B hB hD
    (P.proj ⁻¹' K) (hp.2.2.1.isCompact_preimage hK) hC

/-- The literal global finite singular TEST branch needs no extension
hypothesis when the original singular locus is compact. -/
theorem global_native_test_of_compact_singular
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (singularSet (n := n+1) W)) :
    ∃ (Y : CMfd.{0} (n+1)) (T : BlowupTower X Y), NativeTestState W E T ∧
      IsClosedSubmanifold (n+1) (strictTransform (n+1) T.proj W) ∧
      IsIsomorphismOver (n+1) T.proj (singularSet (n := n+1) W)ᶜ := by
  let K := singularSet (n := n+1) W
  let P : BlowupTower X X := .refl
  have hP : NativeTestState W E P := ⟨hW,hE,hDense,trivial,trivial⟩
  have hBlock := has_compact_footprint_test_block_of_compact_singular W hW E hE hDense K hK hK
  have hReady : HasCompactFootprintTestBlock (strictTransform (n+1) P.proj W)
      (geoTransformAlong (whole W E) P).E (P.proj ⁻¹' K) := by
    simpa only [P,BlowupTower.proj_refl,HironakaG11PresTowerState.strictTransform_id hW.isClosed,
      geoTransformAlong_refl,preimage_id] using hBlock
  obtain ⟨Y,T,hTest,hStage,hClear⟩ := global_block_of_compact_footprint hP K hReady
  simp only [P,geoTransformAlong_refl,BlowupTower.proj_refl,
    HironakaG11PresTowerState.strictTransform_id hW.isClosed,BlowupTower.refl_append] at hTest hStage hClear
  have hp := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hStage)
  have hEmpty : singularSet (n := n+1) (strictTransform (n+1) T.proj W) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact disjoint_left.mp hClear hz (hp.2.2.2.2.2.1 hz)
  exact ⟨Y,T,⟨hW,hE,hDense,hTest,hStage⟩,hp.2.2.2.2.2.2.mp hEmpty,hp.2.1⟩

end
end Hironaka.HironakaG8GlobalNativeTestAssembly
