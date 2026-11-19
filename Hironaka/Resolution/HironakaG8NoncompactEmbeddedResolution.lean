import Hironaka.Resolution.HironakaG8LabelledEmbeddedAtlas
import Hironaka.Resolution.HironakaG8LocalMixedSmoothCleanup
import Hironaka.Resolution.HironakaG8OrderedSmoothSuffix
import Hironaka.Resolution.HironakaG3IdentityHistoryAtlas

/-! The general proper embedded-resolution atlas with literal finite
histories on every compact-enclosed open. -/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NoncompactEmbeddedResolution

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  RestrictEmptyTower MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts HironakaG3RTowerClass HironakaG3GenericBornChartOverlap
  HironakaG8SurfaceLimitEndpoint HironakaG8UniverseDenseBoundary HironakaG8LabelledEmbeddedTape
  HironakaG8LabelledNativeHistory HironakaG8IsolatedCompactSingularAtlas HironakaG8LocalMixedPhaseAssembly
  G3UniversePhysicalClassComparisons HironakaG3BiholomorphicFirstMeeting HironakaOriginalTerminalOverlapComparison
  MaxLocusLocal HironakaG8LocalMixedEmbeddedResolution
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3REmbeddedGlobalSNC HironakaG8CompleteEmbeddedAtlas
  HironakaG8LabelledEmbeddedAtlas HironakaG8LocalMixedSmoothCleanup HironakaG8OrderedSmoothSuffix
  HironakaG8CompleteEmbeddedAtlasBoundary HironakaG3IdentityHistoryAtlas

/-- The compatible complete histories use the same increasing smooth
dimension order on every window. -/
abbrev noncompactEmbeddedClass {n : ℕ} {X : CMfd.{0} n} (W : Set X) : LocalTowerClass X :=
  labelledEmbeddedClass (ascending_smooth_tail_certificate n) W

private theorem zero_rank_identity {X : CMfd.{0} 0} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 0) W) : AscendingSmoothSuffix W [] (BlowupTower.refl (X := X)) := by
  have hSmooth := low_ambient_dimension_analytic_smooth (by decide : 0 ≤ 1) W hW
  have hPart : dimensionPart (n := 0) W 0 = W := by
    refine subset_antisymm (dimensionPart_subset hW.isClosed 0) ?_
    intro x hx
    obtain ⟨d,hd⟩ := hSmooth.2 x hx
    have he : d = 0 := Nat.eq_zero_of_le_zero hd.1
    subst d
    exact subset_closure hd
  have hRem : IsClosed (W \ dimensionPart (n := 0) W 0) := by
    rw [hPart,sdiff_self]
    exact isClosed_empty
  change OrderedSmoothSuffix (List.finRange 1) W [] (BlowupTower.refl (X := X))
  have hRanks : List.finRange 1 = ([0] : List (Fin 1)) := by decide
  rw [hRanks]
  exact .cons isSNCDivisor_nil hRem (.ambient rfl) (.nil _ _) (IsTowerIso.refl_self _)

private theorem zero_dimensional_chart {X : CMfd.{0} 0} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 0) W) (U : Opens X) :
    noncompactEmbeddedClass W U (CMfd.of (n := 0) U) .refl := by
  let A := CMfd.of (n := 0) U
  let WU := (Subtype.val : U → X) ⁻¹' W
  have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U
  have hSmooth := low_ambient_dimension_analytic_smooth (X := CMfd.of (n := 0) U) (by decide : 0 ≤ 1) WU hWU
  have hDense : WU ⊆ closure (WU \ ⋃ H ∈ ([] : List (Set U)), H) := by
    simpa using (subset_closure : WU ⊆ closure WU)
  have hGeometry := zero_dimensional_dense_boundary_resolution (X := A) (W := WU) hWU [] isSNCDivisor_nil hDense
  have hLabel : LabelledNativeTower 0 WU [] univ (.refl : BlowupTower A A) [] := .smooth hWU isSNCDivisor_nil hSmooth
  have hSuffix : (ascending_smooth_tail_certificate 0).holds
      (strictTransform 0 (BlowupTower.refl (X := A)).proj WU) [] (BlowupTower.refl (X := A)) := by
    rw [BlowupTower.proj_refl,HironakaG11PresTowerState.strictTransform_id hWU.isClosed]
    exact zero_rank_identity hWU
  exact ⟨hGeometry,⟨A,A,.refl,.refl,_,[],hLabel,hSuffix,IsTowerIso.refl_self _⟩⟩

private def zero_dimensional_identity_chart {X : CMfd.{0} 0} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 0) W) (U : Opens X) :
    TowerChart (noncompactEmbeddedClass W) X (id : X → X) :=
  let c := identity_history_chart U
  ⟨c.U,c.Y,c.T,zero_dimensional_chart hW U,c.V,c.V_eq,c.φ,c.proj_φ⟩

private theorem zero_dimensional_class_physical {X : CMfd.{0} 0} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := 0) W) : HasPhysicalComparisons (noncompactEmbeddedClass W) := by
  have hEmpty (U : Opens X) {Y : CMfd.{0} 0} (T : BlowupTower (CMfd.of (n := 0) U) Y)
      (hT : noncompactEmbeddedClass W U Y T) (O : Opens U) :
      ResolutionInvariantExt.IsEmptyTower (restrict O T) := by
    let WU := (Subtype.val : U → X) ⁻¹' W
    have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U
    have hSmooth := low_ambient_dimension_analytic_smooth (X := CMfd.of (n := 0) U) (by decide : 0 ≤ 1) WU hWU
    have hNone : singularSet (n := 0) WU = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
      obtain ⟨hx,hSing⟩ := mem_singularSet_iff.mp hx
      obtain ⟨d,hd⟩ := hSmooth.2 x hx
      exact hSing d hd
    have hComplete := labelled_embedded_class_complete U Y T hT
    have hOver := (embedded_positions_centres_over hWU.isClosed T hComplete.positions).1
    exact isEmptyTower_restrict_of_centresOver O (by rw [hNone]; exact disjoint_empty _) T hOver
  intro U V Y Z T S hT hS
  exact emptyAware_of_empty_towers
    (overlapBaseEquiv (n := 0) (show U ⊓ V ≤ U from inf_le_left) (show U ⊓ V ≤ V from inf_le_right))
    (restrict (nestedOpens U (U ⊓ V)) T) (restrict (nestedOpens V (U ⊓ V)) S)
    (hEmpty U T hT _) (hEmpty V S hS _)

/-- Any two actual complete histories compare over their common
saturated open, matching their nonempty centres and boundary slots. -/
theorem noncompact_embedded_class_physical {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) : HasPhysicalComparisons (noncompactEmbeddedClass W) := by
  cases n with
  | zero => exact zero_dimensional_class_physical hW
  | succ m =>
    apply labelled_embedded_class_physical (Nat.succ_pos m) _ hW
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange (m + 2)) hB hT' hT

/-- On a prescribed compact-enclosed open the actual finite chart
belongs to the same complete compatible tower class. -/
theorem noncompact_embedded_class_compact_windows {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (U : Opens X) (K : Set X)
    (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), noncompactEmbeddedClass W U Y T := by
  cases n with
  | zero => exact ⟨CMfd.of (n := 0) U,.refl,zero_dimensional_chart hW U⟩
  | succ m =>
    apply labelled_embedded_class_compact_windows (C := ascending_smooth_tail_certificate (m + 1)) _ hW U K hK hUK
    intro A A₀ hSmooth E hE hDense L hL
    exact local_mixed_smooth_boundary_cleanup_ordered hSmooth E hE hDense L hL

/-- A possibly noncompact analytic carrier has one proper ambient
embedded resolution, with a finite physical tower on each prescribed
compact-enclosed base open and locally finite normal-crossing boundary. -/
theorem exists_locally_finite_embedded_resolution_atlas {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      CompleteEmbeddedAtlas W (noncompactEmbeddedClass W) P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (noncompactEmbeddedClass W) Z P, c.U = U) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (noncompactEmbeddedClass W) Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
        (⋃ j, B j) = P ⁻¹' singularSet (n := n) W ∧
        HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  cases n with
  | zero =>
    have hG : IsGluedFrom (noncompactEmbeddedClass W) X (id : X → X) :=
      ⟨contMDiff_id,isProperMap_id,surjective_id,fun _ => ⟨zero_dimensional_identity_chart hW ⊤,trivial⟩⟩
    have h := complete_embedded_atlas_readback hW hG labelled_embedded_class_complete
    exact ⟨X,id,h,(fun U _ _ _ => ⟨zero_dimensional_identity_chart hW U,rfl⟩),
      complete_embedded_atlas_indexed_boundary h (noncompact_embedded_class_physical hW)
        (noncompact_embedded_class_compact_windows hW)⟩
  | succ m =>
    exact exists_labelled_complete_embedded_atlas_of_windows hW
      (noncompact_embedded_class_physical hW) (noncompact_embedded_class_compact_windows hW)

end
end Hironaka.HironakaG8NoncompactEmbeddedResolution
