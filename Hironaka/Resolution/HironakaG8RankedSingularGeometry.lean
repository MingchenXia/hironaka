import Hironaka.Resolution.HironakaG8RankedNestedGlobalTest
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison
import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixLocalHistories

/-! Intrinsic singular geometry under physical empty steps and rank padding. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RankedSingularGeometry

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaG3EmptyAwareHistory
  HironakaG8RankedEmptyPadding HironakaG8RankedTestCompression HironakaSharpActualCurveEmptyPadding
  HironakaNormalCrossingsSeparationChoiceComparison MarkedIdealTowerTransport
  HironakaG8SingularFootprintExtension

universe u
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem singular_stageCentres_append_empty_iff
    {T : BlowupTower X Y} (W : Set X) (k : ℕ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (T.append (identityEmptyTail Y k)) ↔
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  induction k with
  | zero => rfl
  | succ k ih => exact (and_iff_left (empty_subset _)).trans ih

/-- Every exact rank-padded stage remains intrinsic singular-centred. -/
theorem singular_stageCentres_ranked_through_iff
    {X Y : CMfd.{0} n} {T : BlowupTower X Y} {i : ℕ} (D : RankedTower X T i)
    (W : Set X) (k : ℕ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (D.through k) ↔
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  change StageCentres _ (D.pad.append (identityEmptyTail Y (k-i))) ↔ _
  rw [singular_stageCentres_append_empty_iff]
  induction D with
  | refl => rfl
  | @step Y Z T i j D hij C π hπ ih =>
    have hProj : (D.pad.append (identityEmptyTail Y (j-i))).proj = T.proj := D.through_proj j
    change (_ ∧ C ⊆ singularSet (n := n)
      (strictTransform n (D.pad.append (identityEmptyTail Y (j-i))).proj W)) ↔
      (_ ∧ C ⊆ singularSet (n := n) (strictTransform n T.proj W))
    rw [hProj,singular_stageCentres_append_empty_iff,ih]

/-- Applying physical compression and padding keeps the exact intrinsic
singular-centre criterion at every clock. -/
theorem singular_stageCentres_ranked_compression_iff
    {X Y : CMfd.{0} n} {T : BlowupTower X Y} (M : MarkedIdeals.MarkedIdeal n X)
    {rank : {i // HironakaG8CofinalOccupiedAncestry.Occupied T i} → ℕ}
    (d : RankedTestCompression M T rank) {W : Set X} (hW : IsClosed W) (k : ℕ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (d.decoration.through k) ↔
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  rw [singular_stageCentres_ranked_through_iff]
  constructor
  · have h := singular_stages_of_emptyAware W hW
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) d.comparison
    simpa only [Diffeomorph.coe_refl,preimage_id] using h
  · have h := singular_stages_of_emptyAware W hW
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).symm (G3UniverseEmptyAwareCore.symm d.comparison)
    simpa only [Diffeomorph.symm_refl,Diffeomorph.coe_refl,preimage_id] using h

/-- The original local endpoint smoothness holds for the exact ranked
history through every clock, since padding preserves its projection. -/
theorem isClosedSubmanifold_ranked_through
    {X Y : CMfd.{0} n} {T : BlowupTower X Y}
    (M : MarkedIdeals.MarkedIdeal n X)
    {rank : {k // HironakaG8CofinalOccupiedAncestry.Occupied T k} → ℕ}
    (d : RankedTestCompression M T rank) {W : Set X} (hW : IsClosed W)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W)) (k : ℕ) :
    IsClosedSubmanifold n (strictTransform n (d.decoration.through k).proj W) := by
  rw [d.decoration.through_proj]
  have hEq := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) d.endpoint
    d.tower.contMDiff_proj T.contMDiff_proj W hW (emptyAware_proj_comm d.comparison)
  rw [Diffeomorph.coe_refl,preimage_id] at hEq
  rw [hEq]
  exact (isClosedSubmanifold_preimage_iff d.endpoint).mpr hSmooth


open TopologicalSpace
open BlowupTowerSplit BlowupTowerIsomorphism ResolutionInvariantSeq
open HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveOriginalGrowingHistory HironakaSharpActualCurveGlobalPrefixLocalHistories
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalPrefixTowers
  HironakaLocallyFiniteResolutionSequence HironakaG8FiniteSingularTowerMerge
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaResolutionSpaceLocal
  HironakaG8SurfaceLimitEndpoint HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

private theorem stageCentres_prefix {X Y Z : CMfd.{0} n}
    (P : ∀ {V : CMfd.{0} n}, BlowupTower X V → Set V → Prop)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (h : StageCentres (fun A C => P A C) (T.append R)) :
    StageCentres (fun A C => P A C) T := by
  induction R with
  | refl => exact h
  | step _ _ _ _ ih => exact ih h.1

theorem singular_stageCentres_uniformPrefix
    {X Y : CMfd.{0} n} (T : BlowupTower X Y) (W : Set X) (k : ℕ)
    (h : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (uniformPrefix T k).2 := by
  let S := T.append (identityEmptyTail Y k)
  have hS := (singular_stageCentres_append_empty_iff W k).mpr h
  apply stageCentres_prefix _ (head S T.length) (tail S T.length)
  rw [head_append_tail]
  exact hS

/-- A literal globally glued prefix has singular positions whenever its
actual restricted chart histories do. -/
theorem singular_stageCentres_uniformGrowingSeq_indexed
    {X : CMfd.{0} n} {I : Type} (A : ActualEndpointHistories X I)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X) (hW : IsClosed W)
    (hLocal : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W)))
      ((A.prefixTower i).append (A.tail i))) :
    ∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      ((uniformGrowingSeq A hc).stage k).2 := by
  intro k
  cases k with
  | zero => trivial
  | succ k =>
    apply singular_stages_of_open_cover W A.openSet hc
    intro i
    have hi := singular_stageCentres_uniformPrefix _ _ (k+1) (hLocal i)
    have hDesc := singular_stages_of_tower_iso _ (hW.preimage continuous_subtype_val) _
      (localOriginalPrefix_isTowerIso A hc k i)
    apply hDesc
    simpa only [Diffeomorph.coe_refl,preimage_id] using hi


/-- A locally finished atlas gives a neighbourhood and an actual global
prefix on which all strict-transform points are regular. -/
theorem eventual_regular_uniformGrowingSeq_indexed
    {X : CMfd.{0} n} {I : Type} (A : ActualEndpointHistories X I)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X) (hW : IsClosed W)
    (hLocal : ∀ i, IsClosedSubmanifold n
      (strictTransform n ((A.prefixTower i).append (A.tail i)).proj
        ((Subtype.val : A.openSet i → X) ⁻¹' W))) :
    ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n ((uniformGrowingSeq A hc).stage N).2.proj W))
        (((uniformGrowingSeq A hc).stage N).2.proj ⁻¹' (U : Set X)) := by
  intro x
  obtain ⟨i,hi⟩ := hc x
  let T := (A.prefixTower i).append (A.tail i)
  let N := T.length
  let U := A.openSet i
  let B := uniformOriginalPositiveTower A hc N
  let P := (uniformPrefix T (N+1)).2
  let WU := (Subtype.val : U → X) ⁻¹' W
  have hP : IsClosedSubmanifold n (strictTransform n P.proj WU) := by
    let Data (pair : Σ Y : CMfd.{0} n, BlowupTower (CMfd.of (n := n) U) Y) :=
      IsClosedSubmanifold n (strictTransform n pair.2.proj WU)
    change Data (uniformPrefix T (N+1))
    rw [uniformPrefix_of_length_le T (N+1) (Nat.le_succ T.length)]
    change IsClosedSubmanifold n (strictTransform n
      (T.append (identityEmptyTail _ (N+1-T.length))).proj WU)
    rw [BlowupTower.proj_append,identityEmptyTail_proj,Function.comp_id]
    exact hLocal i
  let e := localOriginalPrefixBiholomorphism A hc N i
  have hIso := localOriginalPrefix_isTowerIso A hc N i
  have hStrict := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) e
    P.contMDiff_proj (restrict U B).contMDiff_proj WU (hW.preimage continuous_subtype_val)
    (fun z => (hIso.proj_comm z).symm)
  rw [Diffeomorph.coe_refl,preimage_id] at hStrict
  have hR : IsClosedSubmanifold n (strictTransform n (restrict U B).proj WU) :=
    (isClosedSubmanifold_preimage_iff e).mp (hStrict ▸ hP)
  refine ⟨U,N+1,hi,Set.disjoint_left.mpr ?_⟩
  intro z hz hzU
  let y : openPreimage B U := ⟨z,hzU⟩
  have hy : y ∈ singularSet (n := n) (strictTransform n (restrict U B).proj WU) := by
    rw [strictTransform_restricted_tower U B W, singularSet_preimage_val]
    exact hz
  obtain ⟨hyW,hySing⟩ := mem_singularSet_iff.mp hy
  obtain ⟨d,hd⟩ := hR.2 y hyW
  exact hySing d hd

/-- The matched growing sequence carries exact singular centres and its own
direct strict transform has a proper, smooth physical endpoint. -/
theorem intrinsic_uniformGrowingSeq_endpoint_indexed
    {X : CMfd.{0} n} {I : Type} (A : ActualEndpointHistories X I)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hLF : LocallyFinite (centreImage (uniformGrowingSeq A hc)))
    (hLocalSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W)))
      ((A.prefixTower i).append (A.tail i)))
    (hLocalSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n ((A.prefixTower i).append (A.tail i)).proj
        ((Subtype.val : A.openSet i → X) ⁻¹' W))) :
    let s := uniformGrowingSeq A hc
    (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (s.stage k).2) ∧
    IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
    limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
    IsProperMap (gluedProjection s hLF) ∧
    IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  dsimp only
  let s := uniformGrowingSeq A hc
  have hStage := singular_stageCentres_uniformGrowingSeq_indexed A hc W hW.isClosed hLocalSing
  have hReg := eventual_regular_uniformGrowingSeq_indexed A hc W hW.isClosed hLocalSmooth
  have hIso := intrinsic_limit_regular_open_iso W hW s hLF hStage
  have hDirect := intrinsic_limit_strictTransform_eq_projection W hW s hLF hStage hIso
  have hSmooth := intrinsic_limit_strictTransform_smooth W hW s hLF hStage hReg
  exact ⟨hStage,hDirect ▸ hSmooth,hDirect,gluedProjection_isProperMap s hLF,hIso⟩


/-- The natural-index specialization of the indexed atlas theorem. -/
theorem singular_stageCentres_uniformGrowingSeq
    {X : CMfd.{0} n} (A : ActualEndpointHistories X ℕ)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X) (hW : IsClosed W)
    (hLocal : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W)))
      ((A.prefixTower i).append (A.tail i))) :
    ∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      ((uniformGrowingSeq A hc).stage k).2 :=
  singular_stageCentres_uniformGrowingSeq_indexed A hc W hW hLocal

/-- The natural-index specialization of the indexed atlas theorem. -/
theorem eventual_regular_uniformGrowingSeq
    {X : CMfd.{0} n} (A : ActualEndpointHistories X ℕ)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X) (hW : IsClosed W)
    (hLocal : ∀ i, IsClosedSubmanifold n
      (strictTransform n ((A.prefixTower i).append (A.tail i)).proj
        ((Subtype.val : A.openSet i → X) ⁻¹' W))) :
    ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n ((uniformGrowingSeq A hc).stage N).2.proj W))
        (((uniformGrowingSeq A hc).stage N).2.proj ⁻¹' (U : Set X)) :=
  eventual_regular_uniformGrowingSeq_indexed A hc W hW hLocal

/-- The natural-index specialization of the indexed atlas theorem. -/
theorem intrinsic_uniformGrowingSeq_endpoint
    {X : CMfd.{0} n} (A : ActualEndpointHistories X ℕ)
    (hc : ∀ x : X, ∃ i, x ∈ A.openSet i) (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hLF : LocallyFinite (centreImage (uniformGrowingSeq A hc)))
    (hLocalSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W)))
      ((A.prefixTower i).append (A.tail i)))
    (hLocalSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n ((A.prefixTower i).append (A.tail i)).proj
        ((Subtype.val : A.openSet i → X) ⁻¹' W))) :
    let s := uniformGrowingSeq A hc
    (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
      (s.stage k).2) ∧
    IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
    limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
    IsProperMap (gluedProjection s hLF) ∧
    IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ :=
  intrinsic_uniformGrowingSeq_endpoint_indexed A hc W hW hLF hLocalSing hLocalSmooth

open MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealBiholomorphism.MarkedIdeal HironakaG8RankedNestedGlobalTest
  HironakaG8RankedGlobalTest HironakaG8CofinalOccupiedAncestry

/-- Rank-sorted local original TEST histories with matched restrictions
produce one proper smooth limit with intrinsic singular positions. -/
theorem intrinsic_endpoint_of_matched_sorted_charts
    {X : CMfd.{0} n} {U : ℕ → Opens X} {Y : ℕ → CMfd.{0} n}
    (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    {ι : Type*} (event : ∀ i, {k // Occupied (T i) k} → ι)
    (rank : ι → ℕ) (hSorted : ∀ i, StrictMono (rank ∘ event i))
    (hMono : Monotone U) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hMatched : ∀ i j, i ≤ j →
      NestedRankComparison (O := U i ⊓ U j) (T i) (T j) (rank ∘ event i) (rank ∘ event j))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i))
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hLocalSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (T i))
    (hLocalSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (T i).proj ((Subtype.val : U i → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  classical
  let d (i : ℕ) := Classical.choice (exists_ranked_test_compression _
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (U i))
    (T i) (hTest i) (rank ∘ event i) (hSorted i))
  have hComparisons := strict_pairwise_of_nested U d hMono hMatched
  let A := actualEndpointHistories U (fun i => (d i).decoration.pad) hComparisons
  obtain ⟨hLF,hGlobalTest⟩ := ranked_test_compressions_globalize M hM U hCover d hComparisons
  have hClosed (i : ℕ) : IsClosed ((Subtype.val : U i → X) ⁻¹' W) :=
    hW.isClosed.preimage continuous_subtype_val
  have hSing (i : ℕ) : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (d i).decoration.pad := by
    have h := (singular_stageCentres_ranked_compression_iff _ (d i) (hClosed i) (d i).clock).mpr
      (hLocalSing i)
    simpa only [RankedTower.through,Nat.sub_self,identityEmptyTail,BlowupTower.append_refl] using h
  have hSmooth (i : ℕ) : IsClosedSubmanifold n (strictTransform n (d i).decoration.pad.proj
      ((Subtype.val : U i → X) ⁻¹' W)) := by
    have h := isClosedSubmanifold_ranked_through _ (d i) (hClosed i) (hLocalSmooth i) (d i).clock
    simpa only [RankedTower.through,Nat.sub_self,identityEmptyTail,BlowupTower.append_refl] using h
  refine ⟨uniformGrowingSeq A hCover,hLF,hGlobalTest,?_⟩
  apply intrinsic_uniformGrowingSeq_endpoint A hCover W hW hLF
  · intro i
    change StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W)))
      ((BlowupTower.refl : BlowupTower (CMfd.of (n := n) (U i))
        (CMfd.of (n := n) (U i))).append (d i).decoration.pad)
    rw [BlowupTower.refl_append]
    exact hSing i
  · intro i
    change IsClosedSubmanifold n (strictTransform n ((BlowupTower.refl : BlowupTower
      (CMfd.of (n := n) (U i)) (CMfd.of (n := n) (U i))).append (d i).decoration.pad).proj
      ((Subtype.val : U i → X) ⁻¹' W))
    simpa only [BlowupTower.refl_append] using hSmooth i

end Hironaka.HironakaG8RankedSingularGeometry
