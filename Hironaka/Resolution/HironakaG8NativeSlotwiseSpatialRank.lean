import Hironaka.Resolution.HironakaG8NativeOccupiedFootprintSymmetry
import Hironaka.Resolution.HironakaG8SpatialRankByFootprintConfinement

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NativeSlotwiseSpatialRank

open BlowupTowers HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8SpatialCofinalPrecedence
  HironakaG8PhysicalChartOccupiedLifts HironakaG8OccupiedSlotComparison
  HironakaG8NativeOccupiedFootprintSymmetry HironakaG8LabelledNativeHistory
  HironakaG8SpatialRankByFootprintConfinement

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} {W : Set X}

/-- Slotwise transitivity on actual native charts makes every spatial
edge reverse the inclusion order of its whole cofinal footprints. -/
theorem reverse_footprint_nesting_of_native_slotwise_transitivity
    (hn : 0 < n) (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hNative : ∀ i, ∃ L, LabelledNativeTower n
      ((Subtype.val : (c i).U → X) ⁻¹' W) [] univ (c i).T L)
    (hTrans : ∀ i k, Occupied (c i).T k → ∀ x y : (c i).U,
      x ∈ slotFootprint (c i).T k → y ∈ slotFootprint (c i).T k →
      ∃ φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U,
        φ ⁻¹' ((Subtype.val : (c i).U → X) ⁻¹' W) =
          ((Subtype.val : (c i).U → X) ⁻¹' W) ∧ φ x = y)
    {a b : ι} (hab : SpatialBefore E a b) :
    cofinalEventFootprint E b ⊆ cofinalEventFootprint E a := by
  obtain ⟨_,y,hyA,hyB⟩ :=
    (spatialBefore_iff_before_and_footprint_meets E cmp hMono hLift).mp hab
  intro x hx
  obtain ⟨i,hi⟩ := hCover x
  obtain ⟨j,hj⟩ := hCover y
  let k := max i j
  have hxK : x ∈ (c k).U := hMono (le_max_left i j) hi
  have hyK : y ∈ (c k).U := hMono (le_max_right i j) hj
  obtain ⟨p,hp,hyp⟩ :=
    (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift k a hyK).mp hyA
  obtain ⟨q,hq,hyq⟩ :=
    (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift k b hyK).mp hyB
  obtain ⟨r,hr,hxr⟩ :=
    (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift k b hxK).mp hx
  have he : r = q := E.injective k (hr.trans hq.symm)
  rw [he] at hxr
  obtain ⟨x',hx',rfl⟩ := hxr
  obtain ⟨y',hy',hy'e⟩ := hyq
  obtain ⟨y'',hy'',hy''e⟩ := hyp
  have he' : y' = y'' := Subtype.ext (hy'e.trans hy''e.symm)
  have hyP : y' ∈ slotFootprint (c k).T p.val := he'.symm ▸ hy''
  obtain ⟨φ,hW,hφ⟩ := hTrans k q.val q.property x' y' hx' hy'
  obtain ⟨L,hN⟩ := hNative k
  have hxP : x' ∈ slotFootprint (c k).T p.val := by
    rw [native_empty_boundary_footprint_symmetry hn hN φ hW p.val]
    change φ x' ∈ slotFootprint (c k).T p.val
    rwa [hφ]
  exact ⟨k,p,hp,mem_image_of_mem _ hxP⟩

theorem exists_injective_spatial_rank_of_native_slotwise_transitivity
    (hn : 0 < n) (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hNative : ∀ i, ∃ L, LabelledNativeTower n
      ((Subtype.val : (c i).U → X) ⁻¹' W) [] univ (c i).T L)
    (hTrans : ∀ i k, Occupied (c i).T k → ∀ x y : (c i).U,
      x ∈ slotFootprint (c i).T k → y ∈ slotFootprint (c i).T k →
      ∃ φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U,
        φ ⁻¹' ((Subtype.val : (c i).U → X) ⁻¹' W) =
          ((Subtype.val : (c i).U → X) ⁻¹' W) ∧ φ x = y) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, Relation.TransGen (SpatialBefore E) a b → rank a < rank b :=
  exists_injective_spatial_rank_of_reverse_footprint_nesting E cmp hMono hLift hCover hOccurs
    (fun _ _ => reverse_footprint_nesting_of_native_slotwise_transitivity hn E cmp hMono hLift
      hCover hNative hTrans)

end Hironaka.HironakaG8NativeSlotwiseSpatialRank
