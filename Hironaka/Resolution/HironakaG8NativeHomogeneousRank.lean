import Hironaka.Resolution.HironakaG8CofinalFiniteRank
import Hironaka.Resolution.HironakaG8NativeOccupiedFootprintSymmetry
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8SpatialWeakRankHeight
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaAdmissibleSequence

/-! A uniform finite event rank for homogeneous native windows. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeHomogeneousRank
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaEmbeddedAnalytic HironakaResolutionSpaceLocal HironakaStageCenters
  HironakaAdmissibleSequence HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaG8LabelledNativeHistory HironakaG8NativeOccupiedFootprintSymmetry
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8SpatialCofinalPrecedence
  HironakaG8PhysicalChartOccupiedLifts HironakaG8SpatialWeakRankHeight
  HironakaG8StageRankCoherence

variable {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}

/-- A whole native boundary-free TEST stage projects into the original singular locus. -/
theorem native_footprint_subset_original_singular
    {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (hT : LabelledNativeTower n W [] univ T L) (i : ℕ) :
    slotFootprint T i ⊆ singularSet (n := n) W := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,
    (isClosed_singularSet hT.source_analytic.isClosed).isOpen_compl⟩
  have hAvoid := intrinsic_singular_history_avoids_regular_open hT.source_analytic
    O disjoint_compl_right T hT.test_and_singular.2
  have hOver := centresOver_compl_of_centresAvoid O T hAvoid
  have hSub := slotFootprint_subset_of_centresOver T hOver i
  change slotFootprint T i ⊆ ((singularSet (n := n) W)ᶜ)ᶜ at hSub
  rwa [compl_compl] at hSub

theorem native_occupied_footprint_eq_singular_of_transitivity (hn : 0<n)
    {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (hT : LabelledNativeTower n W [] univ T L)
    (hTransitive : ∀ (p q : X), p∈singularSet (n := n) W → q∈singularSet (n := n) W →
      ∃ φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
        φ ⁻¹' W=W ∧ φ p=q)
    (i : ℕ) (hi : Occupied T i) :
    slotFootprint T i = singularSet (n := n) W := by
  have hSub := native_footprint_subset_original_singular hT i
  refine Subset.antisymm hSub ?_
  obtain ⟨q,hq⟩ := (slotFootprint_nonempty_iff T i).mpr hi
  intro p hp
  obtain ⟨φ,hW,hpq⟩ := hTransitive p q hp (hSub hq)
  have hSym := native_empty_boundary_footprint_symmetry hn hT φ hW i
  rw [hSym]
  change φ p∈slotFootprint T i
  rwa [hpq]

variable {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z→X}
  {c : ℕ→TowerChart K Z P} {ι : Type*}

theorem finite_serial_rank_of_homogeneous_native_windows (hn : 0<n)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x∈(c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a)
    (hNative : ∀ i, ∃ L : List (ℕ→ℕ),
      LabelledNativeTower n ((Subtype.val : (c i).U→X) ⁻¹' W) [] univ (c i).T L)
    (hTransitive : ∀ i (p q : (c i).U),
      p∈singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) →
      q∈singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) →
      ∃ φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U,
        φ ⁻¹' ((Subtype.val : (c i).U→X) ⁻¹' W)=((Subtype.val : (c i).U→X) ⁻¹' W) ∧
        φ p=q) :
    Finite ι ∧ ∃ (i₀ : ℕ) (rank : ι→ℕ), Function.Injective rank ∧
      (∀ a, rank a<(c i₀).T.length) ∧
      (∀ ⦃a b⦄, E.Before a b → rank a<rank b) ∧
      (∀ b, ∃ bound, ∀ l, DependencyPath (SpatialBefore E) l b → l≤bound) := by
  classical
  have hLocal (i : ℕ) (p : {k // Occupied (c i).T k}) :
      slotFootprint (c i).T p.val =
        singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) := by
    obtain ⟨L,hN⟩ := hNative i
    exact native_occupied_footprint_eq_singular_of_transitivity hn hN
      (hTransitive i) p.val p.property
  have hReference : ∃ i₀, ∀ a, ∃ p : {k // Occupied (c i₀).T k}, E.event i₀ p=a := by
    by_cases hS : (singularSet (n := n) W).Nonempty
    · obtain ⟨x₀,hx₀⟩ := hS
      obtain ⟨i₀,hi₀⟩ := hCover x₀
      refine ⟨i₀,fun a => ?_⟩
      obtain ⟨i,p,hp⟩ := hOccurs a
      let j := max i i₀
      let q := E.lift (le_max_left i i₀) p
      have hxj : x₀∈(c j).U := hMono (le_max_right i i₀) hi₀
      let xj : (c j).U := ⟨x₀,hxj⟩
      have hxSing : xj∈singularSet (n := n) ((Subtype.val : (c j).U→X) ⁻¹' W) := by
        rw [singularSet_preimage_val]
        exact hx₀
      have hxFoot : xj∈slotFootprint (c j).T q.val := by
        rw [hLocal j q]
        exact hxSing
      have hxGlobal : x₀∈cofinalEventFootprint E a :=
        ⟨j,q,(E.lift_event (le_max_left i i₀) p).trans hp,⟨xj,hxFoot,rfl⟩⟩
      obtain ⟨r,hr,_⟩ :=
        (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i₀ a hi₀).mp hxGlobal
      exact ⟨r,hr⟩
    · refine ⟨0,fun a => ?_⟩
      exfalso
      obtain ⟨i,p,_⟩ := hOccurs a
      obtain ⟨x,hx⟩ := (slotFootprint_nonempty_iff (c i).T p.val).mpr p.property
      have hxSing : x∈singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) := by
        rw [← hLocal i p]
        exact hx
      rw [singularSet_preimage_val] at hxSing
      exact hS ⟨x.val,hxSing⟩
  obtain ⟨i₀,hAll⟩ := hReference
  obtain ⟨hFinite,rank,hInj,hBound,hOrder⟩ :=
    HironakaG8CofinalFiniteRank.finite_serial_rank_of_reference_chart E i₀ hAll
  have hHeight : ∀ b, ∃ bound, ∀ l, DependencyPath (SpatialBefore E) l b → l≤bound :=
    (exists_weak_spatial_rank_iff_bounded_height E).mp
      ⟨rank,fun {_ _} h => hOrder (spatialBefore_imp_before E h)⟩
  exact ⟨hFinite,i₀,rank,hInj,hBound,fun {_ _} h => hOrder h,hHeight⟩

end
end Hironaka.HironakaG8NativeHomogeneousRank
