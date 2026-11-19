import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence
import Hironaka.Resolution.HironakaG8DisjointWordLocalCover

/-! Global rank-round footprints and their exact finite chart traces. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalRoundFootprints

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts HironakaG8OccupiedSlotComparison
  HironakaG8SpatialCofinalPrecedence HironakaG8StageRankCoherence HironakaG8DisjointWordLocalCover MaxLocusLocal

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (E : CofinalEvents c ι)

def cofinalRoundFootprint (rank : ι → ℕ) (k : ℕ) : Set X :=
  ⋃ a : {a // rank a = k}, cofinalEventFootprint E a.val

abbrev ChartRoundSlots (rank : ι → ℕ) (k i : ℕ) :=
  {p : {l // Occupied (c i).T l} // rank (E.event i p) = k}

def chartRoundFootprint (rank : ι → ℕ) (k i : ℕ) : Set (c i).U :=
  ⋃ p : ChartRoundSlots E rank k i, slotFootprint (c i).T p.val.val

/-- The preimage of the global round is the exact union of the finite
occupied slots on the chart, including an empty union at absent ranks. -/
theorem cofinalRoundFootprint_preimage_eq
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (k i : ℕ) :
    (Subtype.val : (c i).U → X) ⁻¹' cofinalRoundFootprint E rank k =
      chartRoundFootprint E rank k i := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    obtain ⟨p,hp,hFoot⟩ :=
      (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a.val x.property).mp ha
    obtain ⟨y,hy,hxy⟩ := hFoot
    have he : y = x := Subtype.ext hxy
    exact mem_iUnion.mpr ⟨⟨p,hp ▸ a.property⟩,he ▸ hy⟩
  · intro hx
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨E.event i p.val,p.property⟩,i,p.val,rfl,mem_image_of_mem _ hp⟩

/-- The same trace as a subset of the common original base. -/
theorem cofinalRoundFootprint_inter_chart_eq
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (k i : ℕ) :
    cofinalRoundFootprint E rank k ∩ ((c i).U : Set X) =
      (Subtype.val : (c i).U → X) '' chartRoundFootprint E rank k i := by
  rw [← cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k i]
  ext x
  constructor
  · rintro ⟨hF,hU⟩
    exact ⟨⟨x,hU⟩,hF,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hy,y.property⟩

/-- Canonical flattening identifies the two actual chart round traces. -/
theorem chartRoundFootprint_nested_eq
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (k i j : ℕ)
    (e : CMfd.of (n := n) (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens (c j).U (c i).U))
    (he : ∀ x : (c i).U, (e x).val.val = x.val) :
    chartRoundFootprint E rank k i =
      e ⁻¹' ((Subtype.val : nestedOpens (c j).U (c i).U → (c j).U) ⁻¹'
        chartRoundFootprint E rank k j) := by
  rw [← cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k i,
      ← cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k j]
  ext x
  change x.val ∈ cofinalRoundFootprint E rank k ↔
    (e x).val.val ∈ cofinalRoundFootprint E rank k
  rw [he x]

theorem chartRoundFootprint_eq_empty_of_absent
    (rank : ι → ℕ) (k i : ℕ) (hAbsent : ∀ p : {l // Occupied (c i).T l},
      rank (E.event i p) ≠ k) : chartRoundFootprint E rank k i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨p,_⟩ := mem_iUnion.mp hx
  exact hAbsent p.val p.property

private theorem finite_occupied_slots (i : ℕ) : Finite {l // Occupied (c i).T l} :=
  Finite.of_injective
    (fun p => (⟨p.val,occupied_lt_length _ p.property⟩ : Fin (c i).T.length))
    (fun _ _ h => Subtype.ext (congrArg Fin.val h))

theorem finite_chartRoundSlots (rank : ι → ℕ) (k i : ℕ) :
    Finite (ChartRoundSlots E rank k i) := by
  let _ : Finite {l // Occupied (c i).T l} := finite_occupied_slots (c := c) i
  infer_instance

/-- The entire round family is globally closed and locally finite, with
exact original-base traces on the covering physical charts. -/
theorem cofinalRoundFootprint_closed_locallyFinite
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) (rank : ι → ℕ) :
    (∀ k, IsClosed (cofinalRoundFootprint E rank k)) ∧
      LocallyFinite (cofinalRoundFootprint E rank) := by
  classical
  let F (k i : ℕ) := cofinalRoundFootprint E rank k ∩ ((c i).U : Set X)
  have hFinite (i : ℕ) : {k | (F k i).Nonempty}.Finite := by
    let _ : Finite {l // Occupied (c i).T l} := finite_occupied_slots (c := c) i
    refine (finite_range (fun p => rank (E.event i p))).subset ?_
    rintro k ⟨x,hx,hxi⟩
    have h := (cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k i)
    have hx' : (⟨x,hxi⟩ : (c i).U) ∈ chartRoundFootprint E rank k i :=
      h ▸ hx
    obtain ⟨p,_⟩ := mem_iUnion.mp hx'
    exact ⟨p.val,p.property⟩
  have hClosed (k i : ℕ) : IsClosed ((Subtype.val : (c i).U → X) ⁻¹' F k i) := by
    have hEq : (Subtype.val : (c i).U → X) ⁻¹' F k i =
        chartRoundFootprint E rank k i := by
      rw [← cofinalRoundFootprint_preimage_eq E cmp hMono hLift rank k i]
      ext x
      exact ⟨And.left,fun h => ⟨h,x.property⟩⟩
    rw [hEq]
    let _ : Finite (ChartRoundSlots E rank k i) := finite_chartRoundSlots E rank k i
    exact isClosed_iUnion_of_finite fun p : ChartRoundSlots E rank k i =>
      isClosed_slotFootprint (c i).T p.val.val
  obtain ⟨S,hS,hLF,hTrace⟩ := exists_locally_finite_closed_stage_supports
    (fun i => (c i).U) F hCover (fun _ _ => inter_subset_right) hClosed
    (fun k i j => by simp only [F,inter_assoc,inter_comm ((c i).U : Set X) ((c j).U : Set X)])
    hFinite
  have hEq : S = cofinalRoundFootprint E rank := by
    funext k
    ext x
    obtain ⟨i,hi⟩ := hCover x
    constructor
    · intro hx
      have hh : x ∈ S k ∩ ((c i).U : Set X) := ⟨hx,hi⟩
      rw [hTrace k i] at hh
      exact hh.1
    · intro hx
      have hh : x ∈ F k i := ⟨hx,hi⟩
      rw [← hTrace k i] at hh
      exact hh.1
  rw [← hEq]
  exact ⟨hS,hLF⟩

/-- Each actual projected event footprint is closed on the original base,
by taking it as the only member of round zero. -/
theorem isClosed_cofinalEventFootprint
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) (a : ι) :
    IsClosed (cofinalEventFootprint E a) := by
  classical
  let rank (b : ι) : ℕ := if b = a then 0 else 1
  have hEq : cofinalRoundFootprint E rank 0 = cofinalEventFootprint E a := by
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      have he : b.val = a := by simpa [rank] using b.property
      exact he ▸ hb
    · intro hx
      exact mem_iUnion.mpr ⟨⟨a,by simp [rank]⟩,hx⟩
  rw [← hEq]
  exact (cofinalRoundFootprint_closed_locallyFinite E cmp hMono hLift hCover rank).1 0

end Hironaka.HironakaG8CofinalRoundFootprints
