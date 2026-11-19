import Hironaka.Resolution.HironakaG8CofinalSpatialRankEndpoint
import Hironaka.Resolution.HironakaG8WeakSpatialRankByEpoch
import Mathlib.Data.Prod.Lex

/-! A weak rank determines common finite physical sorting words, retaining ties. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8WeakRankCofinalWords

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaG3RTowerClass
  G3UniversePhysicalClassComparisons HironakaG8CofinalOccupiedAncestry
  HironakaG8PhysicalChartOccupiedLifts HironakaG8SpatialCofinalPrecedence
  HironakaG8InjectiveFiniteAncestryRank HironakaG8WeakSpatialRankByEpoch
  HironakaG8OccupiedSlotComparison HironakaG8CofinalSpatialRankEndpoint
  HironakaG8CofinalSortedWordGeometry HironakaG8ConsecutiveNestedReorderings

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- A common secondary tag resolves ties inside finite chart lists
without requiring the lexicographic key to fit into natural slots. -/
theorem exists_lex_key_of_weak_spatial_rank (E : CofinalEvents c ι)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (rank : ι → ℕ) (hRank : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b) :
    ∃ tag : ι → ℕ, Injective tag ∧
      Injective (fun a => (toLex (rank a,tag a) : ℕ ×ₗ ℕ)) ∧
      ∀ ⦃a b⦄, SpatialBefore E a b → (toLex (rank a,tag a) : ℕ ×ₗ ℕ) < toLex (rank b,tag b) := by
  let _ : Countable ι := cofinal_events_countable E hOccurs
  obtain ⟨tag,hTag⟩ := Countable.exists_injective_nat ι
  refine ⟨tag,hTag,?_,?_⟩
  · intro a b h
    exact hTag (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)
  · intro a b hab
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hRank hab))

/-- A weak rank gives independently realized finite TEST words with
exact nested comparisons across their whole cofinal family. The primary
rank is nondecreasing on each chart and equal-rank slots are disjoint. -/
theorem exists_cofinal_weak_rank_word_geometry
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (rank : ι → ℕ) (hRank : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsClosed W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ (tag : ι → ℕ)
      (D : CofinalKeyedSingularWords E (fun a => (toLex (rank a,tag a) : ℕ ×ₗ ℕ)) M W),
      Injective tag ∧
      (∀ i j, i ≤ j → NestedGeometry (D.R i) (D.R j)) ∧
      (∀ i, (D.order i).Pairwise (fun p q => rank (E.event i p) ≤ rank (E.event i q))) ∧
      ∀ i j k p q, j ≠ k → (D.order i)[j]? = some p → (D.order i)[k]? = some q →
        rank (E.event i p) = rank (E.event i q) →
        Disjoint (slotFootprint (D.R i) j) (slotFootprint (D.R i) k) := by
  obtain ⟨tag,hTag,hKey,hSpatial⟩ := exists_lex_key_of_weak_spatial_rank E hOccurs rank hRank
  let key (a : ι) : ℕ ×ₗ ℕ := toLex (rank a,tag a)
  obtain ⟨D⟩ := exists_cofinal_keyed_singular_words E (toLex (0,0)) key hKey hSpatial
    M hM hN hTest W hW hSing hSmooth
  refine ⟨tag,D,hTag,?_,?_,?_⟩
  · exact nested_geometry_of_cofinal_keyed_words E cmp hMono hLift key hKey
      D.order D.complete D.sorted D.Q D.R D.a D.comparison _
      (fun i => MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
      (fun i => MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
      D.word D.wordGeometry D.readback D.occupied
  · intro i
    exact (D.sorted i).imp (fun h => Prod.Lex.monotone_fst_ofLex (le_of_lt h))
  · intro i j k p q hjk hp hq hEq
    obtain ⟨hj,hjp⟩ := List.getElem?_eq_some_iff.mp hp
    obtain ⟨hk,hkq⟩ := List.getElem?_eq_some_iff.mp hq
    have hNe : E.event i p ≠ E.event i q := by
      intro h
      have hGet : (D.order i).get ⟨j,hj⟩ = (D.order i).get ⟨k,hk⟩ :=
        hjp.trans ((E.injective i h).trans hkq.symm)
      exact hjk (congrArg Fin.val ((D.nodup i).injective_get hGet))
    have hDisj := disjoint_cofinalEventFootprints_of_weak_rank_eq E cmp hMono hLift
      hOccurs rank hRank hNe hEq
    rw [D.readback i j p hp,D.readback i k q hq]
    exact Set.disjoint_left.mpr (fun x hx hy => Set.disjoint_left.mp hDisj
      ⟨i,p,rfl,mem_image_of_mem _ hx⟩ ⟨i,q,rfl,mem_image_of_mem _ hy⟩)

end Hironaka.HironakaG8WeakRankCofinalWords
