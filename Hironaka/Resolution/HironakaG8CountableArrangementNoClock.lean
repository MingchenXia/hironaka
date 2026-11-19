import Hironaka.Resolution.HironakaG8CountablePlaneArrangement
import Hironaka.Resolution.HironakaG8CofinalPhysicalCharts
import Hironaka.Resolution.HironakaG8FinalOrderedEndpoint
import Hironaka.Resolution.HironakaG8CofinalEventLimit
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8CorrectedOrderedEndpoint
import Hironaka.Resolution.HironakaG8PhysicalChartOccupiedLifts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CountableArrangementNoClock
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerIsomorphism HironakaG8CountablePlaneSheets
  HironakaG8CountablePlaneArrangement HironakaG8FirstFootprintOrder
  HironakaG8OccupiedSlotComparison HironakaG8CofinalOccupiedAncestry HironakaG8CofinalEventLimit
  HironakaG8CorrectedOrderedEndpoint HironakaG8NoncompactInitialBoundaryAtlas
  HironakaG8LabelledEmbeddedAtlas HironakaG8LabelledNativeHistory HironakaG3RTowerClass
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaResolutionSpaceLocal HironakaEmbeddedAnalytic HironakaG8PhysicalChartOccupiedLifts

variable {Z : CMfd.{0} 2} {P : Z → sheetManifold}

abbrev ArrangementChart :=
  TowerChart (orderedInitialBoundaryClass (X := sheetManifold) countablePlaneArrangement []) Z P

def FirstHit (c : ArrangementChart (P := P)) (x : c.U) (k : ℕ) : Prop :=
  x ∈ slotFootprint c.T k ∧ ∀ j < k, x ∉ slotFootprint c.T j

theorem firstHit_unique (c : ArrangementChart (P := P)) (x : c.U) {i j : ℕ}
    (hi : FirstHit c x i) (hj : FirstHit c x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (hj.2 i h hi.1).elim
  · exact h
  · exact (hi.2 j h hj.1).elim

private theorem ordered_chart_first_hits (c : ArrangementChart (P := P))
    (hC : InitialBoundaryChartEpochs c) {i j : ℕ} (hij : i < j)
    (hi : ((i,0) : PlaneSheets) ∈ c.U) (hj : ((j,0) : PlaneSheets) ∈ c.U) :
    ∃ a b : ℕ, a < b ∧ FirstHit c ⟨(j,0),hj⟩ a ∧ FirstHit c ⟨(i,0),hi⟩ b := by
  let x : c.U := ⟨(i,0),hi⟩
  let y : c.U := ⟨(j,0),hj⟩
  let W := (Subtype.val : c.U → PlaneSheets) ⁻¹' countablePlaneArrangement
  obtain ⟨B,D,S,Q,χ,L,hS,_,_,hIso⟩ := hC
  have hSing (u : c.U) (hu : u.val.2 = 0) : u ∈ singularSet (n := 2) W := by
    dsimp only [W]
    rw [singularSet_preimage_val,countablePlaneArrangement_singularSet]
    exact hu
  have hProfile :
      toLex (hilbertSamuelAt (vanishingIdeal (n := 2) W) x) <
      toLex (hilbertSamuelAt (vanishingIdeal (n := 2) W) y) := by
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any c.U countablePlaneArrangement x),
      funext (hilbertSamuelAt_vanishing_actual_open_any c.U countablePlaneArrangement y)]
    exact countablePlaneArrangement_origin_profile_strictMono hij
  obtain ⟨a,b,hab,ha,hb,hDa,hDb⟩ := exists_ordered_first_hits_of_original_profiles
    hS (mem_univ x) (mem_univ y) (hSing x rfl) (hSing y rfl) hProfile
  have hTransfer (u : c.U) {r : ℕ} (hu : u ∈ slotFootprint S r)
      (hFirst : ∀ q < r, u ∉ slotFootprint S q) : FirstHit c u r := by
    have hr := hit_slot_lt_length S hu
    have hRead (q : ℕ) (hq : q < S.length) :
        slotFootprint c.T q = slotFootprint S q := by
      rw [slotFootprint_of_isTowerIso hIso, slotFootprint_append, if_pos hq]
      rfl
    exact ⟨(hRead r hr).symm ▸ hu,
      fun q hq => (hRead q (hq.trans hr)).symm ▸ hFirst q hq⟩
  exact ⟨a,b,hab,hTransfer y ha hDa,hTransfer x hb hDb⟩

theorem no_rank_of_firstHit_compatible {I : Type}
    (c : ℕ → ArrangementChart (P := P)) (A : CofinalEvents c I)
    (hMono : Monotone fun i => (c i).U)
    (hCover : ∀ K : Set PlaneSheets, IsCompact K → ∃ i, K ⊆ ((c i).U : Set PlaneSheets))
    (hEpochs : ∀ i, InitialBoundaryChartEpochs (c i))
    (hLift : ∀ {i j : ℕ} (h : i ≤ j) (x : (c i).U) p,
      FirstHit (c i) x p.val →
        FirstHit (c j) ⟨x.val,hMono h x.property⟩ (A.lift h p).val) :
    ¬ ∃ rank : I → ℕ, ∀ ⦃a b⦄, A.Before a b → rank a < rank b := by
  classical
  rintro ⟨rank,hRank⟩
  have hCoverOrigins (m : ℕ) :
      ∃ i, ∀ k ≤ m, ((k,0) : PlaneSheets) ∈ (c i).U := by
    let K : Set PlaneSheets := (fun k : ℕ => ((k,0) : PlaneSheets)) '' Set.Iic m
    have hc : IsCompact K := ((Set.finite_Iic m).image _).isCompact
    obtain ⟨i,hi⟩ := hCover K hc
    exact ⟨i,fun k hk => hi ⟨k,hk,rfl⟩⟩
  obtain ⟨i,hi⟩ := hCoverOrigins 1
  obtain ⟨_,b,_,_,hb⟩ := ordered_chart_first_hits (c i) (hEpochs i)
    (by decide : 0 < 1) (hi 0 (by decide)) (hi 1 (by decide))
  let p : Slots c i := ⟨b,(slotFootprint_nonempty_iff _ b).mp ⟨_,hb.1⟩⟩
  let m := rank (A.event i p) + 1
  have hm : 0 < m := Nat.succ_pos _
  obtain ⟨j,hj⟩ := hCoverOrigins m
  let t := max i j
  let hit (k : Fin (m+1)) : (c t).U :=
    ⟨(k.val,0),hMono (le_max_right i j) (hj k.val (Nat.le_of_lt_succ k.isLt))⟩
  have hEach (k : Fin (m+1)) : ∃ a : ℕ, FirstHit (c t) (hit k) a := by
    by_cases h : k.val = 0
    · obtain ⟨_,b,_,_,hb⟩ := ordered_chart_first_hits (c t) (hEpochs t)
        (by decide : 0 < 1) (hj 0 (Nat.zero_le _) |> hMono (le_max_right i j))
        (hj 1 hm |> hMono (le_max_right i j))
      exact ⟨b,by simpa only [hit,h] using hb⟩
    · obtain ⟨a,_,_,ha,_⟩ := ordered_chart_first_hits (c t) (hEpochs t)
        (Nat.pos_of_ne_zero h) (hj 0 (Nat.zero_le _) |> hMono (le_max_right i j)) (hit k).property
      exact ⟨a,ha⟩
  choose idx hIdx using hEach
  let slot (k : Fin (m+1)) : Slots c t :=
    ⟨idx k,(slotFootprint_nonempty_iff _ _).mp ⟨_,(hIdx k).1⟩⟩
  have hOrder (a b : Fin (m+1)) (hab : a < b) : idx b < idx a := by
    obtain ⟨x,y,hxy,hx,hy⟩ := ordered_chart_first_hits (c t) (hEpochs t)
      (show a.val < b.val from hab) (hit a).property (hit b).property
    rwa [firstHit_unique (c t) (hit a) hy (hIdx a),
      firstHit_unique (c t) (hit b) hx (hIdx b)] at hxy
  have hLiftP := hLift (le_max_left i j) ⟨(0,0),hi 0 (by decide)⟩ p hb
  have hSame : A.lift (le_max_left i j) p = slot 0 :=
    Subtype.ext (firstHit_unique (c t) (hit 0) hLiftP (hIdx 0))
  have hBound (k : ℕ) (hk : k ≤ m) :
      k + rank (A.event t (slot ⟨k,Nat.lt_succ_of_le hk⟩)) ≤ rank (A.event i p) := by
    induction k with
    | zero =>
      have he := A.lift_event (le_max_left i j) p
      simpa [hSame] using (congrArg rank he).le
    | succ k ih =>
      have hk' : k ≤ m := (Nat.le_succ k).trans hk
      have hr := hRank ((A.before_iff_slot_lt t
        (slot ⟨k+1,Nat.lt_succ_of_le hk⟩) (slot ⟨k,Nat.lt_succ_of_le hk'⟩)).mpr
          (hOrder _ _ (Nat.lt_succ_self k)))
      have hprev := ih hk'
      omega
  have h := hBound m le_rfl
  dsimp only [m] at h
  omega


open G3UniversePhysicalClassComparisons HironakaG8NestedOccupiedSlotComparison

theorem physical_chart_lift_preserves_firstHit
    (cmp : HasPhysicalComparisons
      (orderedInitialBoundaryClass (X := sheetManifold) countablePlaneArrangement []))
    (c d : ArrangementChart (P := P)) (h : c.U ≤ d.U) (x : c.U)
    (p : {k // Occupied c.T k}) (hp : FirstHit c x p.val) :
    FirstHit d ⟨x.val,h x.property⟩ (chartOccupiedLift cmp c d h p).val := by
  let hCompare := physical_comparison_nested_chart cmp c d h
  have hf := first_hit_preserved_by_occupiedLiftOnOpen d.T _
    hCompare.choose_spec.2.choose_spec x p hp.1 hp.2
  have he : (hCompare.choose x).val = (⟨x.val,h x.property⟩ : d.U) :=
    Subtype.ext (hCompare.choose_spec.1 x)
  rw [he] at hf
  exact hf


open HironakaG8CofinalPhysicalCharts HironakaG8OrderedSmoothSuffix
  HironakaG8LabelledEmbeddedTape HironakaG8InitialBoundaryAtlasMarkOne NormalCrossings HironakaG8LocalMixedSmoothCleanup

/-- A certified original mark-one atlas can have no natural-valued rank
for the order retaining every pair of occupied slots in the same chart. -/
theorem exists_certified_countableArrangement_no_clock :
    ∃ (Z : CMfd.{0} 2) (P : Z → sheetManifold),
      IsGluedFrom (orderedInitialBoundaryClass countablePlaneArrangement []) Z P ∧
      ∃ c : ℕ → ArrangementChart (P := P),
        Monotone (fun i => (c i).U) ∧
        (∀ K : Set PlaneSheets, IsCompact K → ∃ i, K ⊆ ((c i).U : Set PlaneSheets)) ∧
        (∀ i, InitialBoundaryChartMarkOne (c i) ∧ InitialBoundaryChartEpochs (c i)) ∧
        ∃ (I : Type) (A : CofinalEvents c I),
          (∀ e, ∃ (i : ℕ) (p : Slots c i), A.event i p = e) ∧
          ¬ (∃ rank : I → ℕ, ∀ ⦃a b⦄, A.Before a b → rank a < rank b) := by
  have hW := isComplexAnalyticSubset_countablePlaneArrangement
  have hE : IsSNCDivisor 2 ([] : List (Set PlaneSheets)) := isSNCDivisor_nil
  have hDense : countablePlaneArrangement ⊆
      closure (countablePlaneArrangement \ ⋃ B ∈ ([] : List (Set PlaneSheets)), B) := by
    simpa using (subset_closure : countablePlaneArrangement ⊆ closure countablePlaneArrangement)
  obtain ⟨Z,P,hGlued,c,hMono,_,_,hCover⟩ :=
    exists_ordered_initial_boundary_cofinal_physical_charts (X := sheetManifold) (m := 1) hW hE hDense
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate 2) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange 3) hB hT' hT
  let cmp := initial_boundary_class_physical (X := sheetManifold) (W := countablePlaneArrangement) (E := []) (Nat.succ_pos 1) hC hW hE hDense
  let up {i j : ℕ} (h : i ≤ j) : Slots c i → Slots c j :=
    chartOccupiedLift cmp (c i) (c j) (hMono h)
  have upId (i : ℕ) (p : Slots c i) : up (le_refl i) p = p :=
    congrArg (fun e => e p) (chartOccupiedLift_id cmp (c i))
  have upComp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (p : Slots c i) :
      up hjk (up hij p) = up (hij.trans hjk) p :=
    congrArg (fun e => e p) (chartOccupiedLift_comp cmp (c i) (c j) (c k) (hMono hij) (hMono hjk))
  have upMono {i j : ℕ} (h : i ≤ j) : StrictMono (up h) :=
    (chartOccupiedLift cmp (c i) (c j) (hMono h)).strictMono
  let A := eventLimit c up (up_comp := upComp) (up_id := upId) (up_mono := upMono)
  refine ⟨Z,P,hGlued,c,hMono,hCover,?_,_,A,?_,?_⟩
  · intro i
    exact ⟨initial_boundary_chart_original_markOne hW hE hDense hGlued (c i),
      initial_boundary_chart_epochs (c i)⟩
  · exact eventLimit_occurs c up (up_comp := upComp) (up_id := upId) (up_mono := upMono)
  · apply no_rank_of_firstHit_compatible c A hMono hCover (fun i => initial_boundary_chart_epochs (c i))
    intro i j h x p hp
    exact physical_chart_lift_preserves_firstHit cmp (c i) (c j) (hMono h) x p hp

end
end Hironaka.HironakaG8CountableArrangementNoClock
