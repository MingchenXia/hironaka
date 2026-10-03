/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Analytic.CoordinatePlaneDivision
import Hironaka.Blowup.LiftedOpenModel
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A blowup of a compact manifold along a smooth centre is compact

`compactSpace_of_isBlowupAlong`: if `π: Z → M` is the blowup of a compact complex manifold along a nowhere dense
closed submanifold (`IsBlowupAlong`, a universal property), then `Z` is compact.

Every `y ∈ M` has a neighbourhood `K` with `π⁻¹ K` compact:
* off `C`, the inclusion of `M \ C` lifts to `s`, and uniqueness of lifts on `π⁻¹(M \ C)` gives
  `π⁻¹ K = s(K)` for a compact neighbourhood `K ⊆ M \ C`;
* on `C`, with a flattening chart, `π⁻¹ K` for `K = (Φ ∘ e)⁻¹ (closed ball)` is the finite union
  over `j ≥ k` of the images under the monomial lifts `ℓⱼ` of the compact sets
  `{w : σⱼ(w) ∈ closed ball, ‖wᵢ‖ ≤ 1 for i ≥ k, i ≠ j}`
  (`BlowupLocalSurjectivity.exists_monomialLift_eq`).
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupCompact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

theorem isCompact_monomialBox (k : ℕ) (j : Fin n) (q : ComplexModel n) (R : ℝ) :
    IsCompact {w : ComplexModel n | monomial k j w ∈ closedBall q R ∧
      ∀ i : Fin n, k ≤ i.1 → i ≠ j → ‖w i‖ ≤ 1} := by
  set c : ℝ := max 1 (‖q‖ + R)
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {w : ComplexModel n | monomial k j w ∈ closedBall q R} :=
      isClosed_closedBall.preimage (contDiff_monomial k j).continuous
    have h2 : IsClosed (⋂ (i : Fin n) (_ : k ≤ i.1) (_ : i ≠ j),
        {w : ComplexModel n | ‖w i‖ ≤ 1}) :=
      isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.norm)
          continuous_const
    have heq : {w : ComplexModel n | monomial k j w ∈ closedBall q R ∧
        ∀ i : Fin n, k ≤ i.1 → i ≠ j → ‖w i‖ ≤ 1} =
        {w : ComplexModel n | monomial k j w ∈ closedBall q R} ∩
          ⋂ (i : Fin n) (_ : k ≤ i.1) (_ : i ≠ j), {w : ComplexModel n | ‖w i‖ ≤ 1} := by
      ext w
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [heq]
    exact h1.inter h2
  · have hcoord : ∀ w ∈ {w : ComplexModel n | monomial k j w ∈ closedBall q R ∧
        ∀ i : Fin n, k ≤ i.1 → i ≠ j → ‖w i‖ ≤ 1}, ∀ i, ‖w i‖ ≤ c := by
      rintro w ⟨hw1, hw2⟩ i
      by_cases hij : k ≤ i.1 ∧ i ≠ j
      · exact (hw2 i hij.1 hij.2).trans (le_max_left _ _)
      · have : monomial k j w i = w i := by simp [monomial_apply, hij]
        rw [← this]
        refine (CoordinatePlaneDivision.norm_apply_le _ i).trans ((le_max_right _ _).trans' ?_)
        have := mem_closedBall_iff_norm.mp hw1
        calc ‖monomial k j w‖ = ‖(monomial k j w - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖monomial k j w - q‖ + ‖q‖ := norm_add_le _ _
          _ ≤ ‖q‖ + R := by linarith
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt (n * c ^ 2), fun w hw => ?_⟩
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, c ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord w hw i) 2
      _ = n * c ^ 2 := by simp

/-- Over a closed ball in a flattening chart, the preimage under a blowup is compact. -/
theorem isCompact_preimage_flatBall (hπ : IsBlowupAlong n C π) {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {q : ComplexModel n} {R : ℝ} (hR : closedBall q R ⊆ Φ.target) :
    IsCompact (π ⁻¹' {y | y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ closedBall q R}) := by
  classical
  choose ℓ hℓ using fun (j : Fin n) (hj : k ≤ j.1) =>
    (existsUnique_monomialLift hπ hΦsrc hflat hj).exists
  have hset : π ⁻¹' {y | y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ closedBall q R} =
      ⋃ (j : Fin n) (hj : k ≤ j.1), ℓ j hj '' (LiftedOpen.toModel _ ⁻¹'
        {w : ComplexModel n | monomial k j w ∈ closedBall q R ∧
          ∀ i : Fin n, k ≤ i.1 → i ≠ j → ‖w i‖ ≤ 1}) := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨hz, hball⟩
      obtain ⟨j, hj, w, hw, hbound⟩ := exists_monomialLift_eq hπ hΦsrc hflat hz
      have hwz : ℓ j hj w = z := hw _ (hℓ j hj).1 (hℓ j hj).2
      refine ⟨j, hj, w, ⟨?_, hbound⟩, hwz⟩
      have h1 := congrFun (hℓ j hj).2 w
      simp only [Function.comp_apply, hwz] at h1
      have hmc : Φ.toFun (chartAt (ComplexModel n) y₀ (monomialChart Φ k j w)) =
          monomial k j (LiftedOpen.toModel _ w) :=
        (flatInverse_mem Φ (LiftedOpen.toModel_mem _ w) hΦsrc).2
      rwa [h1, hmc] at hball
    · rintro ⟨j, hj, w, ⟨hw1, -⟩, rfl⟩
      have h1 := congrFun (hℓ j hj).2 w
      simp only [Function.comp_apply] at h1
      rw [h1]
      refine ⟨monomialChart_mem_flatDomain hΦsrc w, ?_⟩
      have hmc : Φ.toFun (chartAt (ComplexModel n) y₀ (monomialChart Φ k j w)) =
          monomial k j (LiftedOpen.toModel _ w) :=
        (flatInverse_mem Φ (LiftedOpen.toModel_mem _ w) hΦsrc).2
      rwa [hmc]
  rw [hset]
  refine isCompact_iUnion fun j => isCompact_iUnion fun hj => ?_
  refine IsCompact.image ?_ (hℓ j hj).1.continuous
  refine ((LiftedOpen.isOpenEmbedding_toModel _).isInducing.isCompact_preimage_iff ?_).mpr
    (isCompact_monomialBox k j q R)
  rintro w ⟨hw, -⟩
  exact ⟨LiftedOpen.mk _ w (hR hw), rfl⟩

/-- Off the centre, the preimage of a compact set is compact: the inclusion of `M \ C` lifts to
the blowup, and the lift is inverse to `π` there. -/
theorem isCompact_preimage_of_disjoint (hπ : IsBlowupAlong n C π) {K : Set M}
    (hK : IsCompact K) (hKC : Disjoint K C) : IsCompact (π ⁻¹' K) := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hset : π ⁻¹' K = s '' (Subtype.val ⁻¹' K) := by
    ext z
    constructor
    · intro hz
      have hzC : π z ∈ Cᶜ := fun h => hKC.le_bot ⟨hz, h⟩
      exact ⟨⟨π z, hzC⟩, hz, hsec z hzC⟩
    · rintro ⟨y, hy, rfl⟩
      have := congrFun hsπ y
      simp only [Function.comp_apply] at this
      rw [mem_preimage, this]
      exact hy
  rw [hset]
  refine IsCompact.image ?_ hs.continuous
  refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).mpr hK
  intro y hy
  exact ⟨⟨y, fun h => hKC.le_bot ⟨hy, h⟩⟩, rfl⟩

/-- **A blowup of a compact complex manifold along a smooth centre is compact.** -/
theorem compactSpace_of_isBlowupAlong [CompactSpace M] (hπ : IsBlowupAlong n C π) :
    CompactSpace Z := by
  classical
  have key : ∀ y : M, ∃ K ∈ 𝓝 y, IsCompact (π ⁻¹' K) := by
    intro y
    by_cases hy : y ∈ C
    · obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hπ.1.2 y hy
      set q := Φ.toFun (chartAt (ComplexModel n) y y)
      have hq : q ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
      obtain ⟨R, hR, hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (Φ.isOpen_target.mem_nhds hq)
      refine ⟨_, ?_, isCompact_preimage_flatBall hπ hΦsrc hflat hRsub⟩
      have hy' := mem_flatDomain_self Φ
      have hcont : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel n) y y')) y :=
        ((Φ.toFun_holomorphic.differentiableAt
          (Φ.isOpen_source.mem_nhds hy'.2)).continuousAt).comp
          ((chartAt (ComplexModel n) y).continuousAt hy'.1)
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy',
        hcont.eventually (closedBall_mem_nhds q hR)] with y' h1 h2
      exact ⟨h1, h2⟩
    · obtain ⟨K, hK, hKsub, hKc⟩ :=
        local_compact_nhds (hπ.1.1.isOpen_compl.mem_nhds hy)
      exact ⟨K, hK, isCompact_preimage_of_disjoint hπ hKc
        (Set.disjoint_left.mpr fun _ h hC => hKsub h hC)⟩
  choose K hK hKc using key
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover K fun y _ => hK y
  refine ⟨?_⟩
  have : (univ : Set Z) = ⋃ y ∈ t, π ⁻¹' K y := by
    refine (eq_univ_of_forall fun z => ?_).symm
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ (π z)))
    exact mem_iUnion₂.mpr ⟨y, hyt, hy⟩
  rw [this]
  exact t.isCompact_biUnion fun y _ => hKc y

end

end Hironaka.BlowupCompact
