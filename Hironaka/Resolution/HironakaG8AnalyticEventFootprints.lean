import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8SpatialCofinalPrecedence
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Resolution.HironakaG8DisjointWordLocalCover
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

/-! Actual cofinal centre footprints are analytic and cover the singular locus on finished atlases. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8AnalyticEventFootprints

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ProperMappingTheorem AnalyticSubsetPreimage AnalyticSubsetOpens
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  HironakaG8SpatialCofinalPrecedence HironakaG8OccupiedSlotComparison
  HironakaG8DisjointWordLocalCover HironakaStageCenters HironakaEmbeddedAnalytic
  RestrictEmptyTower HironakaLocalPrincipalization HironakaResolutionSpaceLocal

variable {n : ℕ} {X Y Z : CMfd.{0} n}

theorem slotFootprint_analytic (T : BlowupTower X Y) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (slotFootprint T k) := by
  induction T with
  | refl => exact isComplexAnalyticSubset_empty
  | step T C π hπ ih =>
    rw [slotFootprint]
    split
    · exact isComplexAnalyticSubset_image T.contMDiff_proj
        (isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1) (fun _ hK =>
          ((isProperMap_proj T).isCompact_preimage hK).inter_left hπ.1.1)
    · exact ih

variable {K : LocalTowerClass X} {P : Z → X} {c : ℕ → TowerChart K Z P} {ι : Type*}
  (E : CofinalEvents c ι)

/-- A global cofinal event has either its single literal analytic
occurrence trace or empty trace on each chart. -/
theorem cofinalEventFootprint_analytic
    (cmp : HasPhysicalComparisons K) (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) (a : ι) :
    IsComplexAnalyticSubset (n := n) (cofinalEventFootprint E a) := by
  classical
  apply isComplexAnalyticSubset_of_forall_opens
  intro x
  obtain ⟨i,hi⟩ := hCover x
  refine ⟨(c i).U,hi,?_⟩
  by_cases h : ∃ p, E.event i p = a
  · obtain ⟨p,hp⟩ := h
    have hEq : (Subtype.val : (c i).U → X) ⁻¹' cofinalEventFootprint E a =
        slotFootprint (c i).T p.val := by
      ext y
      constructor
      · intro hy
        obtain ⟨q,hq,hF⟩ :=
          (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a y.property).mp hy
        have hqp : q = p := (E.injective i) (hq.trans hp.symm)
        subst q
        obtain ⟨z,hz,hzy⟩ := hF
        have hzEq : z = y := Subtype.ext hzy
        exact hzEq ▸ hz
      · intro hy
        exact ⟨i,p,hp,mem_image_of_mem _ hy⟩
    exact hEq.symm ▸ slotFootprint_analytic (c i).T p.val
  · have hEq : (Subtype.val : (c i).U → X) ⁻¹' cofinalEventFootprint E a = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨p,hp,_⟩ := (mem_cofinalEventFootprint_iff_chart E cmp hMono hLift i a y.property).mp hy
      exact h ⟨p,hp⟩
    rw [hEq]
    exact isComplexAnalyticSubset_empty

private theorem centresAvoid_of_slotFootprints (T : BlowupTower X Y) (U : Opens X)
    (hMiss : ∀ k < T.length, ∀ x ∈ U, x ∉ slotFootprint T k) :
    CentresAvoid U T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih (fun k hk x hx hF => ?_),disjoint_left.mpr (fun z hz hU => ?_)⟩
    · apply hMiss k (hk.trans (Nat.lt_succ_self _)) x hx
      simpa only [slotFootprint,if_neg (Nat.ne_of_lt hk)] using hF
    · apply hMiss T.length (Nat.lt_succ_self _) (T.proj z) hU
      simpa [slotFootprint] using mem_image_of_mem T.proj hz

/-- Smooth terminal strict transform forces a literal raw footprint
to hit every singular point of the original set. -/
theorem exists_slotFootprint_of_mem_singular_of_smooth
    (T : BlowupTower X Y) {W : Set X} (hW : IsClosed W)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W))
    {x : X} (hx : x ∈ singularSet (n := n) W) :
    ∃ k : {i // Occupied T i}, x ∈ slotFootprint T k.val := by
  classical
  by_contra hMiss
  let F : Set X := ⋃ k : Fin T.length, slotFootprint T k.val
  have hF : IsClosed F := isClosed_iUnion_of_finite fun k => isClosed_slotFootprint T k.val
  let U : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
  have hxU : x ∈ U := by
    intro h
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    exact hMiss ⟨⟨k.val,(slotFootprint_nonempty_iff T k.val).mp ⟨x,hk⟩⟩,hk⟩
  have hAvoid := centresAvoid_of_slotFootprints T U
    (fun k hk z hz hmem => hz (mem_iUnion.mpr ⟨⟨k,hk⟩,hmem⟩))
  obtain ⟨y,rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
  obtain ⟨hyW,hySing⟩ := mem_singularSet_iff.mp hx
  have hyT := (EmbeddedFromResolution.mem_strictTransform_iff_of_centresAvoid U T hAvoid hW hxU).mpr hyW
  obtain ⟨d,hd⟩ := hSmooth.2 y hyT
  have hNoExc := EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid U T hAvoid y hxU
  exact hySing d
    ((regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW hNoExc d).mp hd)

/-- Every original singular point is reached by some cofinal event in a
covering atlas of completed local strict transforms. -/
theorem singularSet_subset_iUnion_cofinalEventFootprint
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) {W : Set X} (hW : IsClosed W)
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (c i).T.proj
      ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    singularSet (n := n) W ⊆ ⋃ a, cofinalEventFootprint E a := by
  intro x hx
  obtain ⟨i,hi⟩ := hCover x
  let y : (c i).U := ⟨x,hi⟩
  have hy : y ∈ singularSet (n := n) ((Subtype.val : (c i).U → X) ⁻¹' W) := by
    rw [singularSet_preimage_val]
    exact hx
  obtain ⟨p,hp⟩ := exists_slotFootprint_of_mem_singular_of_smooth (c i).T
    (hW.preimage continuous_subtype_val) (hSmooth i) hy
  exact mem_iUnion.mpr ⟨E.event i p,i,p,rfl,mem_image_of_mem _ hp⟩

open HironakaAdmissibleSequence HironakaG8FirstFootprintOrder HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular

/-- For an atlas consisting entirely of intrinsic singular-centred towers,
the union of the finished physical event footprints is the exact singular locus. -/
theorem iUnion_cofinalEventFootprint_eq_singularSet
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U) {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hStage : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (c i).T.proj
      ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    (⋃ a, cofinalEventFootprint E a) = singularSet (n := n) W := by
  apply subset_antisymm ?_ (singularSet_subset_iUnion_cofinalEventFootprint E hCover hW.isClosed hSmooth)
  intro x hx
  obtain ⟨a,i,p,_,y,hy,rfl⟩ := mem_iUnion.mp hx
  let A : Set (c i).U := (Subtype.val : (c i).U → X) ⁻¹' W
  have hA : IsComplexAnalyticSubset (n := n) A := isComplexAnalyticSubset_preimage_val hW (c i).U
  let O : Opens (c i).U := ⟨(singularSet (n := n) A)ᶜ,(isClosed_singularSet hA.isClosed).isOpen_compl⟩
  have hAvoid : CentresAvoid O (c i).T :=
    (actual_singular_history_original_regular_protection A hA (c i).T
      (intrinsic_stage_native_history A (c i).T (hStage i))).1
  have hOver : CentresOver (singularSet (n := n) A) (c i).T := by
    have h := centresOver_compl_of_centresAvoid O (c i).T hAvoid
    change CentresOver ((singularSet (n := n) A)ᶜ)ᶜ (c i).T at h
    simpa only [compl_compl] using h
  have hSing := slotFootprint_subset_of_centresOver (c i).T hOver p.val hy
  change y ∈ singularSet (n := n) ((Subtype.val : (c i).U → X) ⁻¹' W) at hSing
  rw [singularSet_preimage_val] at hSing
  exact hSing

end Hironaka.HironakaG8AnalyticEventFootprints
