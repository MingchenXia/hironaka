import Hironaka.Resolution.HironakaG8AnalyticSpineCover
import Hironaka.Resolution.HironakaG8CombNativeFirstHits
import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CombAnalyticFootprintObstruction

open BlowupTowers HironakaG3RTowerClass
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8PhysicalChartOccupiedLifts G3UniversePhysicalClassComparisons
  HironakaG8SpatialCofinalPrecedence HironakaG8AnalyticSpineCover
  HironakaG8CombNativeFirstHits HironakaG8VariableCombArrangement
  HironakaG8CombExactLocalArrangement HironakaG8NoncompactInitialBoundaryAtlas
  HironakaG8CorrectedOrderedEndpoint HironakaG8LabelledNativeHistory HironakaG8LabelledEmbeddedAtlas

variable {Z : CMfd.{0} 3} {P : Z → combManifold}
  {c : ℕ → CombChart (P := P)} {ι : Type*}

private theorem firstHit_unique {i : ℕ} {x : (c i).U} {a b : ℕ}
    (ha : firstHit (c i) x a) (hb : firstHit (c i) x b) :
    a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (hb.2 _ h ha.1).elim
  · exact h
  · exact (ha.2 _ h hb.1).elim

/-- A single cofinal footprint containing all the teeth is already an
obstruction. A first hit at a tooth is no later than that footprint,
and those first hits are pairwise distinct in every common chart. -/
theorem no_spatial_rank_of_footprint_containing_teeth
    (E : CofinalEvents c ι)
    (cmp : HasPhysicalComparisons (orderedInitialBoundaryClass (X := combManifold) comb []))
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ K : Set combManifold, IsCompact K → ∃ i, K ⊆ ((c i).U : Set combManifold))
    (hEpochs : ∀ i, InitialBoundaryChartEpochs (c i))
    (b : ι) (hSpine : ∀ k : ℕ, anchor k ∈ cofinalEventFootprint E b) :
    ¬ ∃ rank : ι → ℕ, Injective rank ∧
      ∀ ⦃u v⦄, SpatialBefore E u v → rank u < rank v := by
  classical
  rintro ⟨rank,hRankInj,hRank⟩
  let m := rank b+2
  let K : Set combManifold := range (fun k : Fin m => anchor k.val)
  obtain ⟨j,hj⟩ := hCover K (Set.finite_range _).isCompact
  let x (k : Fin m) : (c j).U := ⟨anchor k.val,hj ⟨k,rfl⟩⟩
  let k₀ : Fin m := ⟨0,by dsimp [m]; omega⟩
  let k₁ : Fin m := ⟨1,by dsimp [m]; omega⟩
  have hHits (k : Fin m) : ∃ q, firstHit (c j) (x k) q := by
    by_cases hk : k.val = 0
    · have he : k = k₀ := Fin.ext hk
      subst k
      obtain ⟨a,q,_,_,hq⟩ := comb_ordered_native_first_hits (c j) (hEpochs j)
        (by decide : 0 < 1) (x k₀).property (x k₁).property
      exact ⟨q,hq⟩
    · obtain ⟨q,_,_,hq,_⟩ := comb_ordered_native_first_hits (c j) (hEpochs j)
        (Nat.pos_of_ne_zero hk) (x k₀).property (x k).property
      exact ⟨q,hq⟩
  choose q hq using hHits
  let p (k : Fin m) : {r // Occupied (c j).T r} :=
    ⟨q k,(slotFootprint_nonempty_iff (c j).T (q k)).mp ⟨x k,(hq k).1⟩⟩
  have hStrict (k l : Fin m) (hkl : k < l) : q l < q k := by
    obtain ⟨a,b',hab,ha,hb⟩ := comb_ordered_native_first_hits (c j) (hEpochs j)
      (show k.val < l.val from hkl) (x k).property (x l).property
    have ha' := firstHit_unique (c := c) ha (hq l)
    have hb' := firstHit_unique (c := c) hb (hq k)
    rwa [ha',hb'] at hab
  have hPInj : Injective p := by
    intro k l h
    have hEq : q k = q l := congrArg Subtype.val h
    rcases lt_trichotomy k l with hh | hh | hh
    · exact (Nat.ne_of_lt (hStrict k l hh) hEq.symm).elim
    · exact hh
    · exact (Nat.ne_of_lt (hStrict l k hh) hEq).elim
  have hBound (k : Fin m) : rank (E.event j (p k)) ≤ rank b := by
    obtain ⟨r,hr,hxr⟩ :=
      (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift j b (x k).property).mp
        (hSpine k.val)
    have hAt : x k ∈ slotFootprint (c j).T r.val := by
      obtain ⟨y,hy,he⟩ := hxr
      have hh : y = x k := Subtype.ext he
      rwa [hh] at hy
    have hLe : q k ≤ r.val := by
      by_contra! hh
      exact (hq k).2 _ hh hAt
    rcases lt_or_eq_of_le hLe with hLt | hEq
    · apply Nat.le_of_lt
      apply hRank
      refine ⟨j,p k,r,rfl,hr,hLt,(x k).val,?_,hxr⟩
      exact ⟨x k,(hq k).1,rfl⟩
    · have hPr : p k = r := Subtype.ext hEq
      exact (congrArg rank ((congrArg (E.event j) hPr).trans hr)).le
  let f (k : Fin m) : Fin (rank b+1) := ⟨rank (E.event j (p k)),Nat.lt_succ_of_le (hBound k)⟩
  have hf : Injective f := fun _ _ h =>
    hPInj (E.injective j (hRankInj (congrArg Fin.val h)))
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,m] at hh
  omega

/-- For the actual comb, analytic cofinal footprints covering a nonempty
open patch of the spine rule out an injective spatial rank. -/
theorem no_spatial_rank_of_analytic_spine_cover
    (E : CofinalEvents c ι)
    (cmp : HasPhysicalComparisons (orderedInitialBoundaryClass (X := combManifold) comb []))
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ K : Set combManifold, IsCompact K → ∃ i, K ⊆ ((c i).U : Set combManifold))
    (hEpochs : ∀ i, InitialBoundaryChartEpochs (c i))
    (hOccurs : ∀ b, ∃ i p, E.event i p = b)
    (hAnalytic : ∀ b, IsComplexAnalyticSubset (n := 3) (cofinalEventFootprint E b))
    (O : Set (ComplexModel 1)) (hOpen : IsOpen O) (hne : O.Nonempty)
    (hSpine : ∀ z ∈ O, spineParameter z ∈ ⋃ b, cofinalEventFootprint E b) :
    ¬ ∃ rank : ι → ℕ, Injective rank ∧
      ∀ ⦃u v⦄, SpatialBefore E u v → rank u < rank v := by
  let f : (Σ i : ℕ, {k // Occupied (c i).T k}) → ι := fun a => E.event a.1 a.2
  have hf : Surjective f := by
    intro b
    obtain ⟨i,p,hp⟩ := hOccurs b
    exact ⟨⟨i,p⟩,hp⟩
  let _ : Countable ι := hf.countable
  obtain ⟨b,hb⟩ := exists_footprint_containing_anchors (cofinalEventFootprint E)
    hAnalytic O hOpen hne hSpine
  exact no_spatial_rank_of_footprint_containing_teeth E cmp hMono hLift hCover hEpochs b hb

end Hironaka.HironakaG8CombAnalyticFootprintObstruction

#print axioms Hironaka.HironakaG8CombAnalyticFootprintObstruction.no_spatial_rank_of_analytic_spine_cover
