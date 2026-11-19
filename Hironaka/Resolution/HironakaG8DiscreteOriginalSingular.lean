import Hironaka.Resolution.HironakaG8GlobalNativeTestAssembly
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8DiscreteOriginalSingular
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaBaseChange NormalCrossings NormalCrossingsInvariance
  HironakaStageCenters HironakaG8FiniteNativeTestServing
  HironakaG8IntrinsicSingularBlockSchedule HironakaG8SurfaceLimitEndpoint
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaLocalPrincipalization
  HironakaG8GlobalNativeTestAssembly HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaLocallyFiniteResolutionSequence
  ResolutionInvariantSeq HomogenizedGlueingTower HironakaG8LocalPureFinish
  HironakaActualOpenEmbeddingVanishingIdeal HironakaG3CentresOverGenericFactor
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaActualLimitProtectedOpen HironakaResolutionSpaceLocal
  RestrictEmptyTower HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X : CMfd.{0} (n+1)}

private abbrev original {Y : CMfd.{0} (n+1)} (W : Set Y) (E : List (Set Y)) :
    MarkedIdeal (n+1) Y := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

/-- Each compact task meets the singular support inside an isolated compact
piece. The other singular points form a closed subset of the base. -/
def HasCompactIsolation {A : Type*} [TopologicalSpace A] (F : Set A) : Prop :=
  ∀ K : Set A, IsCompact K →
    ∃ D : Set A, IsCompact D ∧ F ∩ K ⊆ D ∧ D ⊆ F ∧ IsClosed (F \ D)

/-- A locally finite family of pairwise disjoint compact pieces can be
isolated around any compact task by selecting the finitely many pieces
that meet it. -/
theorem hasCompactIsolation_iUnion {A I : Type*} [TopologicalSpace A] [T2Space A]
    (S : I → Set A) (hCompact : ∀ i, IsCompact (S i)) (hLF : LocallyFinite S)
    (hDisj : Pairwise fun i j => Disjoint (S i) (S j)) :
    HasCompactIsolation (⋃ i, S i) := by
  intro K hK
  let M := {i | (S i ∩ K).Nonempty}
  let D := ⋃ i ∈ M, S i
  have hM : M.Finite := hLF.finite_nonempty_inter_compact hK
  refine ⟨D,hM.isCompact_biUnion (fun i _ => hCompact i),?_,?_,?_⟩
  · rintro x ⟨hx,hxK⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨i,⟨x,hi,hxK⟩,hi⟩
  · intro x hx
    obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨i,hi⟩
  · have hEq : (⋃ i, S i) \ D = ⋃ i : {i // i ∉ M}, S i := by
      ext x
      constructor
      · rintro ⟨hx,hOut⟩
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        have hNot : i ∉ M := fun hIn => hOut (mem_iUnion₂.mpr ⟨i,hIn,hi⟩)
        exact mem_iUnion.mpr ⟨⟨i,hNot⟩,hi⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        refine ⟨mem_iUnion.mpr ⟨i.val,hi⟩,?_⟩
        intro hIn
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hIn
        have hne : i.val ≠ j := fun he => i.property (he.symm ▸ hj)
        exact disjoint_left.mp (hDisj hne) hi hxj
    rw [hEq]
    exact (hLF.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun i => (hCompact i.val).isClosed)

/-- Properness turns the pullback of the isolated compact piece into a
compact footprint at each actual tested prefix. -/
theorem native_footprints_of_compactly_isolated_original_singular
    (W : Set X) (E : List (Set X)) (hIsolate : HasCompactIsolation (singularSet (n := n+1) W)) :
    HasNativeFootprintExtensions W E := by
  intro Y P hP K hK
  let F := singularSet (n := n+1) W
  obtain ⟨D,hD,hKD,_,hOther⟩ := hIsolate K hK
  let V := strictTransform (n+1) P.proj W
  let B := (geoTransformAlong (original W E) P).E
  let O : Opens Y := ⟨(P.proj ⁻¹' (F \ D))ᶜ,
    (hOther.preimage P.contMDiff_proj.continuous).isOpen_compl⟩
  let i : O → Y := Subtype.val
  let A := CMfd.of (n := n+1) O
  let U := i ⁻¹' V
  let C := B.map (i ⁻¹' ·)
  let G := P.proj ⁻¹' D
  have hKO : P.proj ⁻¹' K ⊆ O := by
    intro y hy hBad
    exact hBad.2 (hKD ⟨hBad.1,hy⟩)
  have hGO : G ⊆ O := fun _ hy hBad => hBad.2 hy
  have hPC : IsCompact G := (isProperMap_proj P).isCompact_preimage hD
  have hp := actual_singular_history_original_regular_protection W hP.analytic P
    (intrinsic_stage_native_history W P hP.singular)
  have hV := hp.2.2.2.1
  have hM : (original W E).IsWellFormed := ⟨isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hP.analytic,hP.snc,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hP.snc⟩
  have hB : IsSNCDivisor (n+1) B :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM P hP.tested).isSNCDivisor
  have hDense := HironakaG8DenseBoundaryRestart.strict_transform_dense_off_accumulated_boundary
    hP.analytic E hP.snc hP.dense P hP.tested hP.singular
  have hU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hV O
  have hC := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hB
  have hSub : singularSet (n := n+1) U ⊆ i ⁻¹' G := by
    intro x hx
    have hm := mem_singularSet_iff.mp hx
    have hxy : i x ∈ singularSet (n := n+1) V := mem_singularSet_iff.mpr
      ⟨hm.1,fun k hk => hm.2 k ((isOpenHoloEmbedding_val O).regularAtDim_preimage hk)⟩
    have hIn : P.proj (i x) ∈ F := hp.2.2.2.2.2.1 hxy
    by_contra hn
    exact x.property ⟨hIn,hn⟩
  have hCG : IsCompact (i ⁻¹' G) :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun y hy => ⟨⟨y,hGO hy⟩,rfl⟩)).mpr hPC
  have hCompact : IsCompact (singularSet (n := n+1) U) :=
    hCG.of_isClosed_subset (isClosed_singularSet hU.isClosed) hSub
  obtain ⟨Z,T,hT,hSmooth,hIso⟩ := global_native_test_of_compact_singular (X := A) U hU C hC
    (dense_complement_restrict V B hDense O) hCompact
  let R : Opens A := ⟨(singularSet (n := n+1) U)ᶜ,
    (isClosed_singularSet hU.isClosed).isOpen_compl⟩
  have hAvoid := intrinsic_singular_history_avoids_regular_open hU R
    disjoint_compl_right T hT.singular
  have hOver : CentresOver (singularSet (n := n+1) U) T := by
    have h := centresOver_compl_of_centresAvoid R T hAvoid
    change CentresOver (singularSet (n := n+1) U)ᶜᶜ T at h
    rwa [compl_compl] at h
  have hOverG : CentresOver (i ⁻¹' G) T := by
    clear hAvoid hT hSmooth hIso
    induction T with
    | refl => trivial
    | step T L π hπ ih => exact ⟨ih hOver.1,hOver.2.trans (preimage_mono hSub)⟩
  have hGood := actual_singular_history_original_regular_protection U hU T
    (intrinsic_stage_native_history U T hT.singular)
  have hEmpty := hGood.2.2.2.2.2.2.mpr hSmooth
  refine ⟨O,hKO,G,hPC,hGO,Z,T,hT,hOverG,?_⟩
  rw [hEmpty]
  exact disjoint_empty _

/-- The discrete case retains its original footprint extension signature. -/
theorem native_footprints_of_discrete_original_singular
    (W : Set X) (E : List (Set X)) (hDiscrete : IsDiscrete (singularSet (n := n+1) W)) :
    HasNativeFootprintExtensions W E := by
  intro Y P hP K hK
  have hF : IsClosed (singularSet (n := n+1) W) := isClosed_singularSet hP.analytic.isClosed
  apply native_footprints_of_compactly_isolated_original_singular W E _ hP K hK
  intro L hL
  refine ⟨_,hL.of_isClosed_subset (hF.inter hL.isClosed) inter_subset_right,
    Subset.rfl,inter_subset_left,?_⟩
  exact isClosed_of_subset_discrete_closed sdiff_subset hDiscrete hF

/-- Compactly isolated original singular support admits an original mark-one
global finite or growing TEST resolution in positive ambient dimension. -/
theorem compactly_isolated_original_singular_finite_or_proper_limit
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hIsolate : HasCompactIsolation (singularSet (n := n+1) W)) :
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
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) :=
  global_native_test_finite_or_proper_limit W hW E hE hDense
    (native_footprints_of_compactly_isolated_original_singular W E hIsolate)

/-- Locally finite disjoint compact pieces of original singular support
give a finite singular-centred TEST or a proper smooth growing limit. -/
theorem compact_pieces_original_singular_finite_or_proper_limit
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {I : Type*} (S : I → Set X) (hCompact : ∀ i, IsCompact (S i)) (hLF : LocallyFinite S)
    (hDisj : Pairwise fun i j => Disjoint (S i) (S j))
    (hUnion : singularSet (n := n+1) W = ⋃ i, S i) :
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
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) :=
  compactly_isolated_original_singular_finite_or_proper_limit W hW E hE hDense
    (hUnion.symm ▸ hasCompactIsolation_iUnion S hCompact hLF hDisj)

/-- A closed discrete original singular locus suffices for a finite original
TEST or a locally finite growing original TEST, with genuine physical limit. -/
theorem discrete_original_singular_finite_or_proper_limit
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hDiscrete : IsDiscrete (singularSet (n := n+1) W)) :
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
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (gluedProjection s hLF) :=
  global_native_test_finite_or_proper_limit W hW E hE hDense
    (native_footprints_of_discrete_original_singular W E hDiscrete)

#print axioms hasCompactIsolation_iUnion
#print axioms native_footprints_of_compactly_isolated_original_singular
#print axioms compactly_isolated_original_singular_finite_or_proper_limit
#print axioms compact_pieces_original_singular_finite_or_proper_limit
#print axioms native_footprints_of_discrete_original_singular
#print axioms discrete_original_singular_finite_or_proper_limit
end
end Hironaka.HironakaG8DiscreteOriginalSingular
