import Hironaka.Resolution.HironakaG8CofinalSortedWordGeometry
import Hironaka.Resolution.HironakaG8RankSortedRawChart

/-! A common spatial rank gives the intrinsic global endpoint on a finished cofinal TEST atlas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalSpatialRankEndpoint

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG3RTowerClass MaxLocusLocal G3UniversePhysicalClassComparisons
  HironakaG8PhysicalChartOccupiedLifts HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8SpatialCofinalPrecedence HironakaG8RankSortedRawChart HironakaG8CofinalSortedWordGeometry
  HironakaG8GeometricIndexedWord HironakaG8NestedVisibleWordLift HironakaG3EmptyAwareHistory
  HironakaStageCenters HironakaEmbeddedAnalytic MarkedIdealTowerTransport
  HironakaNormalCrossingsSeparationChoiceComparison
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The charts realizing a common spatial order retain their actual
compressions, sorting words and original singular TEST certificates. -/
structure CofinalKeyedSingularWords (E : CofinalEvents c ι)
    {κ : Type*} [LinearOrder κ] (rank : ι → κ) (M : MarkedIdeal n X) (W : Set X) where
  order : ∀ i, List {k // Occupied (c i).T k}
  nodup : ∀ i, (order i).Nodup
  complete : ∀ i p, p ∈ order i
  sorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q))
  A : ℕ → CMfd.{0} n
  B : ℕ → CMfd.{0} n
  Q : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i)
  R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (B i)
  a : ∀ i, A i ≃ₘ⟮𝓘c,𝓘c⟯ (c i).Y
  comparison : ∀ i, EmptyAwareTowerIso
    (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (c i).U) ∞) (Q i) (c i).T (a i)
  word : ℕ → List ℕ
  wordGeometry : ∀ i, RealizedWord
    (GeometricIndexedMove ((Subtype.val : (c i).U → X) ⁻¹' W)
      (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M))
    (word i) ⟨A i,Q i⟩ ⟨B i,R i⟩
  readback : ∀ i k p, (order i)[k]? = some p →
    slotFootprint (R i) k = slotFootprint (c i).T p.val
  length_eq_order : ∀ i, (R i).length = (order i).length
  occupied : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length
  test : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (R i)
  singular : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
    (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (R i)
  smooth : ∀ i, IsClosedSubmanifold n
    (strictTransform n (R i).proj ((Subtype.val : (c i).U → X) ⁻¹' W))

/-- Realize any common key strictly respecting spatial precedence. -/
theorem exists_cofinal_keyed_singular_words {κ : Type*} [LinearOrder κ]
    (E : CofinalEvents c ι) (fallback : κ) (rank : ι → κ) (hRank : Injective rank)
    (hSpatial : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsClosed W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    Nonempty (CofinalKeyedSingularWords E rank M W) := by
  classical
  let M' (i : ℕ) := MarkedIdeal.pullback (Subtype.val : (c i).U → X) M
  let W' (i : ℕ) := (Subtype.val : (c i).U → X) ⁻¹' W
  have hM' (i : ℕ) : (M' i).IsWellFormed :=
    MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U
  have hN' (i : ℕ) : (M' i).N = univ := by
    change (Subtype.val : (c i).U → X) ⁻¹' M.N = univ
    rw [hN,preimage_univ]
  have hW' (i : ℕ) : IsClosed (W' i) := hW.preimage continuous_subtype_val
  have hOrder (i : ℕ) (p q : {k // Occupied (c i).T k}) (hpq : p.val < q.val)
      (hMeet : (slotFootprint (c i).T p.val ∩ slotFootprint (c i).T q.val).Nonempty) :
      rank (E.event i p) < rank (E.event i q) := by
    obtain ⟨x,hxp,hxq⟩ := hMeet
    exact hSpatial ⟨i,p,q,rfl,rfl,hpq,x.val,mem_image_of_mem _ hxp,mem_image_of_mem _ hxq⟩
  have hProducer (i : ℕ) := exists_key_sorted_raw_singular_test_geometry fallback (c i).T
    (rank ∘ E.event i) (hRank.comp (E.injective i)) (hOrder i)
    (W' i) (hW' i) (M' i) (hM' i) (hN' i) (hTest i) (hSing i)
  choose order hNodup hComplete hSorted A Q a hCmp _hQtest _hQocc _hQsing hQproj
    _hQfoot word B R e hWord hRtest hRproj hRsing hRfoot hRead hOcc using hProducer
  have hRSmooth (i : ℕ) : IsClosedSubmanifold n (strictTransform n (R i).proj (W' i)) := by
    let g := (a i).symm.trans (e i)
    have hg (z : (c i).Y) : (R i).proj (g z) = (c i).T.proj z := by
      calc
        (R i).proj (g z) = (Q i).proj ((a i).symm z) := congrFun (hRproj i) _
        _ = (c i).T.proj ((a i) ((a i).symm z)) := (hQproj i _).symm
        _ = (c i).T.proj z := congrArg (c i).T.proj ((a i).apply_symm_apply z)
    have hStrict := strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (c i).U) ∞) g
      (c i).T.contMDiff_proj (R i).contMDiff_proj (W' i) (hW' i) hg
    rw [Diffeomorph.coe_refl,preimage_id] at hStrict
    exact (isClosedSubmanifold_preimage_iff g).mp (hStrict ▸ hSmooth i)
  exact ⟨{
    order := order
    nodup := hNodup
    complete := hComplete
    sorted := hSorted
    A := A
    B := B
    Q := Q
    R := R
    a := a
    comparison := hCmp
    word := word
    wordGeometry := hWord
    readback := hRead
    length_eq_order := fun i => by
      simpa only [footprints,List.length_map,List.length_range] using congrArg List.length (hRfoot i)
    occupied := hOcc
    test := hRtest
    singular := hRsing
    smooth := hRSmooth }⟩

/-- A common injective rank increasing on actual spatial precedence
automatically supplies geometric words and exact matched sorted charts. -/
theorem intrinsic_endpoint_of_cofinal_spatial_rank
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (hRank : Injective rank)
    (hSpatial : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  obtain ⟨D⟩ := exists_cofinal_keyed_singular_words E 0 rank hRank hSpatial
    M hM hN hTest W hW.isClosed hSing hSmooth
  exact intrinsic_endpoint_of_cofinal_sorted_words hCover E cmp hMono hLift rank hRank
    D.order D.complete D.sorted D.Q D.R D.a D.comparison _
    (fun i => MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
    (fun i => MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
    D.word D.wordGeometry D.readback D.occupied M hM D.test W hW D.singular D.smooth

end Hironaka.HironakaG8CofinalSpatialRankEndpoint
