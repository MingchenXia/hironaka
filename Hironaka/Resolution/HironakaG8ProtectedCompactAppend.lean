import Hironaka.Resolution.HironakaG8FiniteNativeTestServing

/-! Append a compact task while keeping the previous regular trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ProtectedCompactAppend

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism HironakaEmbeddedAnalytic HironakaStageCenters
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport BlowupRestrictOpen
  HironakaG8NativeRelativePhase HironakaG8SaturatedPrefixAppend HironakaG8DenseBoundaryRestart
  HironakaG8FiniteNativeTestServing HironakaLocalPrincipalization HironakaSaturatedTowerAppend
  HironakaG8IntrinsicSingularBlockSchedule HironakaNormalCrossingsOpenRestrictionSeparation
  MaxLocusLocal HironakaResolutionSpaceLocal RestrictEmptyTower

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) : MarkedIdeal (n+1) A :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

private theorem singular_suffix_of_append (W : Set X) (P : BlowupTower X Y) :
    ∀ {Z : CMfd.{0} (n+1)} (Q : BlowupTower Y Z),
      StageCentres (fun T C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) T.proj W)) (P.append Q) →
      StageCentres (fun T C => C ⊆ singularSet (n := n+1)
        (strictTransform (n+1) T.proj (strictTransform (n+1) P.proj W))) Q
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    refine ⟨singular_suffix_of_append W P T h.1,?_⟩
    have hc := h.2
    change C ⊆ singularSet (n := n+1) (strictTransform (n+1) (P.append T).proj W) at hc
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp
      P.contMDiff_proj T.contMDiff_proj] at hc
    exact hc

set_option maxHeartbeats 600000 in
/-- A compact task can be resolved by restricting a supplied physical
prefix and then appending a finite continuation. Any already regular
region is unchanged by the new stages wherever the new base retains it. -/
theorem exists_compact_append_preserving_regular_trace
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y}
    (hP : NativeTestState W E P)
    (K : Set X) (hK : IsCompact K) (R : Opens X)
    (hReg : Disjoint (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      (P.proj ⁻¹' (R : Set X))) :
    ∃ (O : Opens X), K ⊆ O ∧
      ∃ (Z : CMfd.{0} (n+1)) (Q : BlowupTower (CMfd.of (n := n+1) (openPreimage P O)) Z),
        let P₀ := restrict O P
        let W₀ := (Subtype.val : O → X) ⁻¹' W
        let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
        NativeTestState W₀ E₀ (P₀.append Q) ∧
        IsClosedSubmanifold (n+1) (strictTransform (n+1) (P₀.append Q).proj W₀) ∧
        ResolutionInvariantExt.IsEmptyTower
          (restrict (nestedOpens (openPreimage P O) (openPreimage P R)) Q) := by
  let A := strictTransform (n+1) P.proj W
  let B := (geoTransformAlong (whole W E) P).E
  have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hP.analytic P
  have hWF : (whole W E).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hP.analytic,
      hP.snc, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hP.snc⟩
  have hB := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF P hP.tested).isSNCDivisor
  have hDense := strict_transform_dense_off_accumulated_boundary hP.analytic E hP.snc hP.dense P
    hP.tested hP.singular
  obtain ⟨V,hKV,Z,S,hST,hSG,hSmooth⟩ := exists_native_singular_resolution_near_compact
    (Nat.succ_pos n) hA B hB hDense (P.proj ⁻¹' K) ((isProperMap_proj P).isCompact_preimage hK)
  obtain ⟨O,hKO,hOV,hTest,hSing,_,_,hStrict,_⟩ :=
    exists_saturated_singular_phase_append hP.analytic E hP.snc P hP.tested hP.singular K V hKV S hST hSG
  let U := openPreimage P O
  let L := restrict O P
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n+1) hOV).symm
  let tail := transport e (restrict D S)
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  have hW₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hP.analytic O
  have hE₀ := NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val O) continuous_subtype_val hP.snc
  refine ⟨O,hKO,tail.target,tail.tower,⟨hW₀,hE₀,HironakaG8LocalPureFinish.dense_complement_restrict W E hP.dense O,
    hTest,hSing⟩,?_,?_⟩
  · change IsClosedSubmanifold (n+1) (strictTransform (n+1) (L.append tail.tower).proj W₀)
    rw [hStrict]
    exact (isClosedSubmanifold_preimage_iff tail.back).mpr
      (isClosedSubmanifold_preimage_val hSmooth (openPreimage S D))
  · have hA₀ := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW₀ L
    have hStrict₀ := strictTransform_restricted_tower O P W
    have hNo : Disjoint (singularSet (n := n+1) (strictTransform (n+1) L.proj W₀))
        (nestedOpens U (openPreimage P R) : Set U) := by
      rw [hStrict₀, singularSet_preimage_val]
      exact disjoint_left.mpr (fun y hy hyR => disjoint_left.mp hReg hy hyR)
    apply (isEmptyTower_restrict_iff _ tail.tower).mpr
    apply intrinsic_singular_history_avoids_regular_open hA₀ _ hNo tail.tower
    change StageCentres (fun T C => C ⊆ singularSet (n := n+1)
      (strictTransform (n+1) T.proj (strictTransform (n+1) L.proj W₀))) tail.tower
    have hSuffix := singular_suffix_of_append (X := CMfd.of (n := n+1) O)
      (Y := CMfd.of (n := n+1) U) W₀ L (Z := tail.target) tail.tower
    apply hSuffix
    exact hSing

/-- The new working base retains an entire precompact completed open
while serving an additional compact set. The physical suffix remains
empty over that old open. -/
theorem exists_compact_append_containing_regular_open
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y}
    (hP : NativeTestState W E P)
    (K : Set X) (hK : IsCompact K) (R : Opens X)
    (hR : IsCompact (closure (R : Set X)))
    (hReg : Disjoint (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      (P.proj ⁻¹' (R : Set X))) :
    ∃ (O : Opens X), K ⊆ O ∧ R ≤ O ∧
      ∃ (Z : CMfd.{0} (n+1)) (Q : BlowupTower (CMfd.of (n := n+1) (openPreimage P O)) Z),
        let P₀ := restrict O P
        let W₀ := (Subtype.val : O → X) ⁻¹' W
        let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
        NativeTestState W₀ E₀ (P₀.append Q) ∧
        IsClosedSubmanifold (n+1) (strictTransform (n+1) (P₀.append Q).proj W₀) ∧
        ResolutionInvariantExt.IsEmptyTower
          (restrict (nestedOpens (openPreimage P O) (openPreimage P R)) Q) := by
  obtain ⟨O,hCover,Z,Q,hState,hSmooth,hEmpty⟩ :=
    exists_compact_append_preserving_regular_trace hP (K ∪ closure (R : Set X))
      (hK.union hR) R hReg
  exact ⟨O,subset_union_left.trans hCover,
    fun _ hx => hCover (Or.inr (subset_closure hx)),Z,Q,hState,hSmooth,hEmpty⟩

end Hironaka.HironakaG8ProtectedCompactAppend
