import Hironaka.Resolution.HironakaG8SpatialGeometricWord
import Hironaka.Resolution.HironakaG8GeometricNestedWordLift

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8JointSpatialReordering

open BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealRestrictOpen HironakaG8EmptyAwareTestTransport HironakaG8OccupiedSlotComparison
  HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord
  HironakaG8SpatialGeometricWord HironakaG8GeometricNestedWordLift HironakaG8FiniteSpatialOrdering

variable {n : ℕ} {X : CMfd.{0} n}

/-- Realize the larger spatial target and its filtered smaller order in
one nested pair of actual original TEST towers. -/
theorem jointly_realize_nested_spatial_target
    (U : Opens X) (L : TowerAt X) (S : TowerAt (CMfd.of (n := n) U))
    (hNested : LiteralNestedTower U L S)
    (target : List ℕ) (hPerm : (List.range L.2.length).Perm target)
    (hOcc : OccupiedFootprints L)
    (hPreserve : ∀ i j : ℕ, i < j → j < L.2.length →
      (slotFootprint L.2 i ∩ slotFootprint L.2 j).Nonempty → target.idxOf i < target.idxOf j)
    (W : Set X) (N : MarkedIdeal n X) (hN : N.IsWellFormed) (hWhole : N.N = univ)
    (hTest : IsGeoTestTower N L.2) (hStage : IntrinsicStage W L) :
    ∃ (w v : List ℕ) (R : TowerAt X) (T : TowerAt (CMfd.of (n := n) U)),
      v.length ≤ w.length ∧
      RealizedWord (GeometricIndexedMove W N) w L R ∧
      RealizedWord (PhysicalSmallerMove U N) v S T ∧
      SwapWord Disjoint v (footprintsIn S) (footprintsIn T) ∧
      IsGeoTestTower N R.2 ∧ IntrinsicStage W R ∧ OccupiedFootprints R ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) N) T.2 ∧
      LiteralNestedTower U R T ∧
      (∀ j i, target[j]? = some i → slotFootprint R.2 j = slotFootprint L.2 i) ∧
      footprints R = target.map (slotFootprint L.2) ∧
      footprintsIn T =
        (target.map (fun i => slotFootprint L.2 i ∩ (U : Set X))).filter visibleTrace ∧
      (∃ e : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R.1,
        R.2.proj ∘ e = L.2.proj) ∧
      ∃ f : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1,
        T.2.proj ∘ f = S.2.proj := by
  let N' := MarkedIdeal.pullback (Subtype.val : U → X) N
  have hN' : N'.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U
  have hRestrict := isGeoTestTower_restrict (U := U)
    hN.isClosedSubmanifold_N hN.isCoherent L.2 hTest
  have hSmallTest : IsGeoTestTower N' S.2 := by
    obtain ⟨_,_,hCmp⟩ := hNested
    let idU := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞
    have hIff := isGeoTestTower_iff_of_emptyAware N' hN' idU hCmp
    have hId : MarkedIdeal.pullback idU N' = N' :=
      ContactCanonicalAlong.pullback_id N' hN'.isCoherent
    rw [hId] at hIff
    exact hIff.mpr hRestrict
  obtain ⟨w,R,_,hWord,hRT,hRStage,hROcc,hListed,hTarget,hRProj⟩ :=
    realize_spatial_target_geometrically L target hPerm hOcc hPreserve W N hN hWhole hTest hStage
  obtain ⟨v,T,hLen,hSmaller,hTrace,hComp,hRead,hTT,hTProj⟩ :=
    lift_geometric_word_to_smaller_test U W N hN hWord hNested hSmallTest
  refine ⟨w,v,R,T,hLen,hWord,hSmaller,hTrace,hRT,hRStage,hROcc,hTT,hComp,
    hListed,hTarget,?_,hRProj,hTProj⟩
  change footprintsIn T =
    (target.map ((fun A : Set X => A ∩ (U : Set X)) ∘ slotFootprint L.2)).filter visibleTrace
  simpa only [footprintTraces,hTarget,List.map_map] using hRead

end Hironaka.HironakaG8JointSpatialReordering
