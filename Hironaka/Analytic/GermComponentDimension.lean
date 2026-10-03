/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.PureDimension
import Hironaka.Analytic.IrreducibleGermLocal
import Hironaka.Analytic.GermParametrizationDense
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.AnalyticGermDecomposition
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.GermParametrizationSets
import Hironaka.Analytic.RegularAtDimChart
import Hironaka.Analytic.RegularPointDimension
set_option autoImplicit false

/-!
# The dimension of a local irreducible component of an irreducible subvariety

This module proves it.  The chain is:

* `regularAtDim_preimage_iff` — regularity in `ℂⁿ` is invariant under a linear
  automorphism (the translation case is
  `Hironaka.AnalyticLocalStatement.regularAtDim_translate_iff`);
* `exists_regularAtDim_near_zero` — the parametrization data of a germ exhibits
  regular points of dimension `P.dim` arbitrarily near `0`: over every base point
  off the discriminant locus the fibre is nonempty
  (`SetsData.ncard_fibre` and `ParametrizationData.deg_pos`) and consists of
  regular points of that dimension (`SetsData.regular`), and `SetsData.small`
  confines the fibre to a small polydisc, hence to a small ball;
* `exists_pure_nhds_dim` — therefore the pure dimension produced by
  `Hironaka.IrreducibleGermLocal.exists_pure_nhds` IS `P.dim`;
* `exists_isOpen_disjoint_others` — a nonempty open set meeting one member of an
  irredundant family of irreducible germs and missing all the others, obtained by
  the same induction as `Hironaka.PureDimension.exists_isOpen_disjoint_others` from
  `Hironaka.IrreducibleGermLocal.exists_thin_nhds` and the relative closedness of
  an analytic germ near `0`;
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.GermComponentDimension

open Hironaka.RegularLocusDense AnalyticGermDecomposition GermParametrization
open Hironaka.GermParametrizationData
open Hironaka.AnalyticLocalStatement
open Hironaka.RegularPointDimension
open Hironaka.RegularAtDimChart
open Hironaka.AnalyticDescendingChain

noncomputable section

variable {n : ℕ}

/-! ### Regularity is invariant under a linear automorphism -/

/-- A linear automorphism of the model space as a partial homeomorphism. -/
def linearHomeo (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  L.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem linearHomeo_apply (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (z : ComplexModel n) : linearHomeo L z = L z := rfl

@[simp] theorem linearHomeo_source (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    (linearHomeo L).source = (univ : Set (ComplexModel n)) := rfl

@[simp] theorem linearHomeo_symm_apply (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (z : ComplexModel n) : (linearHomeo L).symm z = L.symm z := rfl

theorem differentiableOn_linearHomeo (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    DifferentiableOn ℂ (linearHomeo L) (linearHomeo L).source :=
  (L : ComplexModel n →L[ℂ] ComplexModel n).differentiable.differentiableOn

theorem differentiableOn_linearHomeo_symm (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    DifferentiableOn ℂ (linearHomeo L).symm (linearHomeo L).target :=
  (L.symm : ComplexModel n →L[ℂ] ComplexModel n).differentiable.differentiableOn

/-- **Regularity in the model space is invariant under a linear automorphism.** -/
theorem regularAtDim_preimage_iff (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (S : Set (ComplexModel n)) (y : ComplexModel n) {k : ℕ} :
    RegularAtDim (n := n) (M := ComplexModel n) (L ⁻¹' S) y k ↔
      RegularAtDim (n := n) (M := ComplexModel n) S (L y) k := by
  constructor
  · rintro ⟨hk, hyS, Φ, -, hΦ0, hflat⟩
    have hc : L y ∈ (linearHomeo L.symm).source := mem_univ _
    have hTc : linearHomeo L.symm (L y) = y := by simp
    refine ⟨hk, hyS, precomp (linearHomeo L.symm) (differentiableOn_linearHomeo L.symm)
      (differentiableOn_linearHomeo_symm L.symm) hc hTc Φ, subset_univ _, ?_, ?_⟩
    · change Φ.toFun (linearHomeo L.symm (L y)) = 0
      rw [hTc]
      exact hΦ0
    · intro w _ hw
      change w ∈ (linearHomeo L.symm).source ∩ linearHomeo L.symm ⁻¹' Φ.source at hw
      change w ∈ S ↔ Φ.toFun (linearHomeo L.symm w) ∈ complexCoordinatePlane n k
      have h := hflat (y := L.symm w) (mem_univ _) hw.2
      rw [mem_preimage, L.apply_symm_apply] at h
      exact h
  · rintro ⟨hk, hyS, Ψ, -, hΨ0, hflat⟩
    have hc : y ∈ (linearHomeo L).source := mem_univ _
    have hTc : linearHomeo L y = L y := rfl
    refine ⟨hk, hyS, precomp (linearHomeo L) (differentiableOn_linearHomeo L)
      (differentiableOn_linearHomeo_symm L) hc hTc Ψ, subset_univ _, ?_, ?_⟩
    · change Ψ.toFun (linearHomeo L y) = 0
      rw [hTc]
      exact hΨ0
    · intro w _ hw
      change w ∈ (linearHomeo L).source ∩ linearHomeo L ⁻¹' Ψ.source at hw
      change w ∈ L ⁻¹' S ↔ Ψ.toFun (linearHomeo L w) ∈ complexCoordinatePlane n k
      exact hflat (y := L w) (mem_univ _) hw.2

/-! ### Regular points of a parametrized germ accumulate at the origin -/

/-- Off the discriminant locus the fibre of the adapted projection is nonempty. -/
theorem nonempty_fibre {A : Set (ComplexModel n)} {P : ParametrizationData A} (S : SetsData P)
    {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) :
    (fibre S x).Nonempty := by
  have hcard : (S.finite_fibre x hx hd).toFinset.card = P.deg := card_toFinset_fibre S hx hd
  have hne : (S.finite_fibre x hx hd).toFinset.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact P.deg_pos
  obtain ⟨y, hy⟩ := hne
  exact ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩

/-- Regular points of `A` of dimension `P.dim` occur arbitrarily near `0`: every base point
off the discriminant locus carries a nonempty fibre of such points, and `SetsData.small`
confines the fibre over a small base point to a small polydisc. -/
theorem exists_regularAtDim_near_zero_aux {A : Set (ComplexModel n)}
    {P : ParametrizationData A} (S : SetsData P) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ ball (0 : ComplexModel n) ε,
      RegularAtDim (n := n) (M := ComplexModel n)
        (A ∩ polydisc n P.dim S.r₁ S.r₂) y P.dim := by
  set ε' := ε / ((n : ℝ) + 2) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hprod : ((n : ℝ) + 1) * ε' ≤ ε := by
    have h2 : ε' * ((n : ℝ) + 2) = ε := by rw [hε']; field_simp
    nlinarith [hε'0]
  obtain ⟨η, hη, hηs⟩ := S.small ε' hε'0
  have hr0 : 0 < min (min η ε') S.r₁ := lt_min (lt_min hη hε'0) S.r₁_pos
  have hfreq : ∃ᶠ x in 𝓝 (0 : ComplexModel P.dim), P.disc x ≠ 0 :=
    Filter.not_eventually.mp P.disc_not_eventually_zero
  obtain ⟨x, hxb, hdx⟩ := (Filter.frequently_iff.mp hfreq) (ball_mem_nhds _ hr0)
  have hxn : ‖x‖ < min (min η ε') S.r₁ := mem_ball_zero_iff.1 hxb
  have hxr₁ : ‖x‖ < S.r₁ := hxn.trans_le (min_le_right _ _)
  have hxη : ‖x‖ < η := hxn.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hxε' : ‖x‖ < ε' := hxn.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨y, hy⟩ := nonempty_fibre S hxr₁ hdx
  have hπ : coordinateProjection n P.dim y = x := hy.2
  have hpoly : y ∈ polydisc n P.dim ε' ε' := by
    refine ⟨by rw [hπ]; exact hxε', fun k hk => ?_⟩
    exact hηs y hy.1 (by rw [hπ]; exact hxη) k hk
  refine ⟨y, ?_, S.regular y hy.1 (by rw [hπ]; exact hdx)⟩
  exact ball_subset_ball hprod (polydisc_subset_ball hε'0 hpoly)

/-- **Regular points of dimension `P.dim` accumulate at `0`**, for parametrization data of a
linear change of coordinates `L⁻¹B` of the germ `B`. -/
theorem exists_regularAtDim_near_zero {B : Set (ComplexModel n)}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) {P : ParametrizationData (L ⁻¹' B)}
    (S : SetsData P) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ ball (0 : ComplexModel n) ε, ∃ Δ : Set (ComplexModel n), IsOpen Δ ∧ y ∈ Δ ∧
      RegularAtDim (n := n) (M := ComplexModel n) (B ∩ Δ) y P.dim := by
  set c := ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1 with hc
  have hc0 : 0 < c := by
    have := norm_nonneg (L : ComplexModel n →L[ℂ] ComplexModel n)
    rw [hc]; linarith
  obtain ⟨y', hy'b, hy'reg⟩ :=
    exists_regularAtDim_near_zero_aux S (div_pos hε hc0)
  have hy'n : ‖y'‖ < ε / c := mem_ball_zero_iff.1 hy'b
  refine ⟨L y', ?_, (L.symm : ComplexModel n → ComplexModel n) ⁻¹'
    polydisc n P.dim S.r₁ S.r₂, (isOpen_polydisc _ _ _ _).preimage L.symm.continuous, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    have h1 : ‖L y'‖ ≤ ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ * ‖y'‖ :=
      (L : ComplexModel n →L[ℂ] ComplexModel n).le_opNorm y'
    have h3 : ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ * ‖y'‖ ≤ c * ‖y'‖ :=
      mul_le_mul_of_nonneg_right (by rw [hc]; linarith) (norm_nonneg _)
    have h4 : c * ‖y'‖ < c * (ε / c) := mul_lt_mul_of_pos_left hy'n hc0
    have h5 : c * (ε / c) = ε := by field_simp
    linarith
  · show (L.symm : ComplexModel n → ComplexModel n) (L y') ∈ polydisc n P.dim S.r₁ S.r₂
    simpa using hy'reg.2.1.2
  · rw [← regularAtDim_preimage_iff]
    have hset : (L : ComplexModel n → ComplexModel n) ⁻¹'
          (B ∩ (L.symm : ComplexModel n → ComplexModel n) ⁻¹' polydisc n P.dim S.r₁ S.r₂)
        = (L : ComplexModel n → ComplexModel n) ⁻¹' B ∩ polydisc n P.dim S.r₁ S.r₂ := by
      ext z
      simp
    rw [hset]
    exact hy'reg

/-- **The dimension of parametrization data of an irreducible germ is its pure dimension.**
The conclusion of `Hironaka.IrreducibleGermLocal.exists_pure_nhds` holds with `d = d₀`
whenever regular points of dimension `d₀` occur arbitrarily near `0`. -/
theorem exists_pure_nhds_dim {B : Set (ComplexModel n)} (hB : IsIrreducibleGerm B) {d₀ : ℕ}
    (hnear : ∀ ε > 0, ∃ y ∈ ball (0 : ComplexModel n) ε, ∃ Δ : Set (ComplexModel n),
      IsOpen Δ ∧ y ∈ Δ ∧ RegularAtDim (n := n) (M := ComplexModel n) (B ∩ Δ) y d₀) :
    ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      ∀ Ω' : Set (ComplexModel n), IsOpen Ω' → Ω' ⊆ Ω →
        (∀ {y : ComplexModel n} {k : ℕ},
          RegularAtDim (n := n) (M := ComplexModel n) (B ∩ Ω') y k → k = d₀) ∧
        B ∩ Ω' ⊆ closure (regularLocus (n := n) (M := ComplexModel n) (B ∩ Ω') d₀) := by
  obtain ⟨d, Ω, hΩo, hΩ0, hΩ⟩ := IrreducibleGermLocal.exists_pure_nhds hB
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩo 0 hΩ0
  obtain ⟨y, hyb, Δ, hΔo, hyΔ, hyreg⟩ := hnear ε hε
  have hΩ'o : IsOpen (ball (0 : ComplexModel n) ε ∩ Δ) := isOpen_ball.inter hΔo
  have hΩ'sub : ball (0 : ComplexModel n) ε ∩ Δ ⊆ Ω := fun z hz => hball hz.1
  have heq : (B ∩ Δ) ∩ (ball (0 : ComplexModel n) ε ∩ Δ)
      = (B ∩ (ball (0 : ComplexModel n) ε ∩ Δ)) ∩ (ball (0 : ComplexModel n) ε ∩ Δ) := by
    ext z
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.2.2⟩, h.2⟩⟩
  have hd : d₀ = d :=
    (hΩ _ hΩ'o hΩ'sub).1 (regularAtDim_of_inter_eq hΩ'o ⟨hyb, hyΔ⟩ heq hyreg)
  subst hd
  exact ⟨Ω, hΩo, hΩ0, hΩ⟩

/-! ### An open set meeting one component and missing the others -/

/-- An analytic germ is relatively closed on a small ball: its equations are holomorphic
there and describe it exactly. -/
theorem exists_isOpen_ball_diff {B : Set (ComplexModel n)} (hB : IsAnalyticGerm B) :
    ∃ ρ > 0, IsOpen (ball (0 : ComplexModel n) ρ \ B) := by
  obtain ⟨s, g, hgd, hgB⟩ := hB
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      (∀ j, DifferentiableAt ℂ (g j) z) ∧ (z ∈ B ↔ ∀ j, g j z = 0) :=
    (Filter.eventually_all.2 hgd).and hgB
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨ρ, hρ, ?_⟩
  have hset : ball (0 : ComplexModel n) ρ \ B
      = ⋃ j : Fin s, (ball (0 : ComplexModel n) ρ ∩ g j ⁻¹' ({0} : Set ℂ)ᶜ) := by
    ext z
    constructor
    · rintro ⟨hz, hzB⟩
      have hiff := (hρs z hz).2
      obtain ⟨j, hj⟩ := not_forall.mp (fun h => hzB (hiff.2 h))
      exact mem_iUnion.2 ⟨j, hz, hj⟩
    · intro hz
      obtain ⟨j, hzj, hgj⟩ := mem_iUnion.mp hz
      exact ⟨hzj, fun hzB => hgj ((hρs z hzj).2.1 hzB j)⟩
  rw [hset]
  refine isOpen_iUnion fun j => ?_
  have hcont : ContinuousOn (g j) (ball (0 : ComplexModel n) ρ) := fun z hz =>
    ((hρs z hz).1 j).continuousAt.continuousWithinAt
  exact hcont.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton

/-- Members of an irredundant family of irreducible germs meet every neighbourhood of `0`. -/
theorem frequently_mem_of_isIrreducibleGerm {B : Set (ComplexModel n)}
    (hB : IsIrreducibleGerm B) : ∃ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ B := by
  have h : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      (z ∈ B ↔ z ∈ (∅ : Set (ComplexModel n))) := by
    rw [← Filter.eventuallyEq_set]
    exact hB.2.1
  exact (Filter.not_eventually.mp h).mono fun z hz => by simpa using hz

/-- **A nonempty open set meeting one member of an irredundant family of irreducible germs and
missing all the others.**  This is the germ-level form of
`Hironaka.PureDimension.exists_isOpen_disjoint_others`, and is proved by the same induction:
each step shrinks by the relatively open complement of one other member, keeping a point of
the distinguished member supplied by thinness. -/
theorem exists_isOpen_disjoint_others {r : ℕ} {A : Fin r → Set (ComplexModel n)}
    (hA : ∀ i, IsIrreducibleGerm (A i)) (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j))
    (i : Fin r) {O : Set (ComplexModel n)} (hO : IsOpen O) (hO0 : (0 : ComplexModel n) ∈ O) :
    ∃ O' : Set (ComplexModel n), IsOpen O' ∧ O' ⊆ O ∧ (O' ∩ A i).Nonempty ∧
      ∀ j, j ≠ i → O' ∩ A j = ∅ := by
  classical
  have hfreq := frequently_mem_of_isIrreducibleGerm (hA i)
  have key : ∀ j : Fin r, ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      IsOpen (Ω \ A j) ∧ (j ≠ i → ∀ U : Set (ComplexModel n), IsOpen U →
        (U ∩ (A i ∩ Ω)).Nonempty → ∃ y ∈ U ∩ (A i ∩ Ω), y ∉ A j) := by
    intro j
    obtain ⟨ρ, hρ, hballo⟩ := exists_isOpen_ball_diff (hA j).1
    by_cases hji : j = i
    · exact ⟨ball 0 ρ, isOpen_ball, mem_ball_self hρ, hballo, fun h => absurd hji h⟩
    · obtain ⟨Ωt, hΩto, hΩt0, hthin⟩ :=
        IrreducibleGermLocal.exists_thin_nhds (hA i) (hA j).1 (hpw (Ne.symm hji))
      refine ⟨Ωt ∩ ball 0 ρ, hΩto.inter isOpen_ball, ⟨hΩt0, mem_ball_self hρ⟩, ?_,
        fun _ U hU hne => ?_⟩
      · have hrw : (Ωt ∩ ball (0 : ComplexModel n) ρ) \ A j
            = Ωt ∩ (ball (0 : ComplexModel n) ρ \ A j) := by
          ext z
          exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
        rw [hrw]
        exact hΩto.inter hballo
      · obtain ⟨w, hw⟩ := hne
        obtain ⟨y, hy, hyj⟩ := hthin (U ∩ ball 0 ρ) (hU.inter isOpen_ball)
          ⟨w, ⟨hw.1, hw.2.2.2⟩, hw.2.1, hw.2.2.1⟩
        exact ⟨y, ⟨hy.1.1, hy.2.1, hy.2.2, hy.1.2⟩, hyj⟩
  choose Ω hΩo hΩ0 hΩd hΩt using key
  have main : ∀ m : ℕ, ∃ O' : Set (ComplexModel n), IsOpen O' ∧ O' ⊆ O ∧
      (∀ j, O' ⊆ Ω j) ∧ (O' ∩ A i).Nonempty ∧
      ∀ j : Fin r, j.val < m → j ≠ i → O' ∩ A j = ∅ := by
    intro m
    induction m with
    | zero =>
      refine ⟨O ∩ ⋂ j, Ω j, hO.inter (isOpen_iInter_of_finite hΩo), inter_subset_left,
        fun j z hz => mem_iInter.mp hz.2 j, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      obtain ⟨z, hz1, hz2⟩ := (Filter.frequently_iff.mp hfreq)
        ((hO.inter (isOpen_iInter_of_finite hΩo)).mem_nhds ⟨hO0, mem_iInter.2 hΩ0⟩)
      exact ⟨z, hz1, hz2⟩
    | succ m ih =>
      obtain ⟨O', hO'o, hO'O, hO'Ω, hne, hdisj⟩ := ih
      by_cases hm : m < r
      · by_cases hmi : (⟨m, hm⟩ : Fin r) = i
        · refine ⟨O', hO'o, hO'O, hO'Ω, hne, fun j hj hji => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
          · exact hdisj j hlt hji
          · exact absurd (hmi ▸ Fin.ext heq) hji
        · obtain ⟨y, hy, hyj⟩ := hΩt ⟨m, hm⟩ hmi O' hO'o
            (by obtain ⟨w, hw1, hw2⟩ := hne; exact ⟨w, hw1, hw2, hO'Ω _ hw1⟩)
          refine ⟨O' ∩ (Ω ⟨m, hm⟩ \ A ⟨m, hm⟩), hO'o.inter (hΩd _),
            inter_subset_left.trans hO'O, fun j z hz => hO'Ω j hz.1,
            ⟨y, ⟨hy.1, hy.2.2, hyj⟩, hy.2.1⟩, ?_⟩
          intro j hj hji
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
          · exact subset_empty_iff.mp ((inter_subset_inter_left _ inter_subset_left).trans
              (hdisj j hlt hji).subset)
          · have hj' : j = ⟨m, hm⟩ := Fin.ext heq
            subst hj'
            exact eq_empty_iff_forall_notMem.mpr fun w hw => hw.1.2.2 hw.2
      · refine ⟨O', hO'o, hO'O, hO'Ω, hne, fun j hj hji => ?_⟩
        exact hdisj j (lt_of_lt_of_le j.isLt (not_lt.mp hm)) hji
  obtain ⟨O', hO'o, hO'O, -, hne, hdisj⟩ := main r
  exact ⟨O', hO'o, hO'O, hne, fun j hji => hdisj j j.isLt hji⟩

end

end Hironaka.GermComponentDimension
