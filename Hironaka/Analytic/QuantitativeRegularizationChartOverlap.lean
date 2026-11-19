import Hironaka.Analytic.QuantitativeRegularizationChartBranch
import Hironaka.Analytic.QuantitativeRegularizationSingularOverlap
import Hironaka.Analytic.BergmanBiholomorphicTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `eq:reg-overlap` across two charts (Copy-4 `lem:regularization`, Step 2)

Source: Copy-4, `lem:regularization`, Step 2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:909-967`);
blueprint `ana:regularization`.

`QuantitativeRegularizationChartBranch` builds the Bergman branch of ONE chart ball,
`b = m⁻¹ log K_{B, e^{-m(φ ∘ e⁻¹ + ρ)}} ∘ e - ρ ∘ e`, and
`QuantitativeRegularizationSingularOverlap` compares two Bergman kernels of balls of ONE
chart.  Copy-4 compares the branches of two overlapping balls `B_j`, `B_l` of its fixed
cover, which are coordinate balls of two DIFFERENT charts `e_j`, `e_l`, "in the coordinates of
`B_l`", with "the uniform comparison between `dλ` and `dV_Z` absorbed into the constants".
This module proves that comparison:

> `exists_const_forall_chartBergmanBranch_le_add`: for a compact set `K` lying in the source
> of both charts, with `e_j(K) ⊆ B_j` and `e_l(K) ⊆ B̄_l`, there is ONE constant `C ≥ 0`,
> depending only on the two charts and balls, such that
> `b_j ≤ b_l + C/m` at every point of `K` in the `l`-th patch, for EVERY form `ζ`, EVERY pair
> of smooth potentials of `ζ` on the two potential balls, EVERY `ζ`-PSH `φ` and every `m ≥ 1`.

Near a point `x₀` of `K` the comparison is a chain of five steps, each with a constant fixed
by the geometry alone:

1. shrink `B_j` to a small ball `D'` around `e_j(x₀)` inside the overlap of the two charts
   (the kernel is antitone in the domain, `bergmanSup_le_of_subset`);
2. replace the potential `ρ_j` on `D'` by the transported potential `ρ_l ∘ (e_l ∘ e_j⁻¹)`
   (`chartBergmanBranch_eq_of_potentials`, Copy-4's transformation rule; exact);
3. transport `D'` to the chart `e_l` (`bergmanLog_le_image`; the Jacobian of the transition is
   bounded near `e_j(x₀)`, which costs `log A`);
4. shrink the image to a ball `E` around `e_l(x₀)` (antitone again);
5. compare `E` with `B_l` in the chart `e_l` (`exists_overlapConst_pair_multiplierWeight`, the
   Hörmander point extension of `BergmanOverlapFixedCover` passed to singular weights; this
   costs `log C`).

Compactness of `K` (`IsCompact.induction_on`) turns the local constants into one.

Unlike Copy-4 the comparison needs no Lebesgue-number hypothesis on the cover: it only uses
that `K` lies in both chart sources.  The constants do not depend on `ζ` because the only
`ζ`-dependent objects, the potentials, enter through the exact transformation rule.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace Hironaka.QuantitativeRegularizationChartOverlap

open Hironaka.AnalyticGluingData Hironaka.HolomorphicMaps
  Hironaka.LocalPotentialPullback Hironaka.MongeAmpere BergmanSupWeight
  QuantitativeRegularizationChartBranch

noncomputable section

variable {d : ℕ}

/-! ### Two balls of one chart, singular weight -/

/-- **Two coordinate balls of one chart, for an arbitrary plurisubharmonic weight.**  One
constant `C > 0`, fixed by the two balls, with
`K_{ball c β, e^{-mu}}(x) ≤ C · K_{ball c' β', e^{-mu}}(x)` for every psh `u` on `Ω`, every
`m > 0`, and every `x` in the inner half ball `ball c (ρ/2)` and in `ball c' β'`.  This is
`BergmanOverlapFixedCover.exists_overlapConst_ball` passed to singular weights by
`QuantitativeRegularizationSmoothWeightLimit`, exactly as
`QuantitativeRegularizationSingularOverlap` does for finite families. -/
theorem exists_overlapConst_pair_multiplierWeight (hd : 0 < d)
    {A Ω : Opens (ComplexModel d)} (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω) (c c' : ComplexModel d) {ρ β β' : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ < β) (hcA : closedBall c β ⊆ (A : Set (ComplexModel d)))
    (hβ' : 0 < β') (hcA' : closedBall c' β' ⊆ (A : Set (ComplexModel d))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : ComplexModel d → EReal), PlurisubharmonicOn u Ω →
        ∀ m : ℝ, 0 < m → ∀ x, x ∈ ball c (ρ / 2) → x ∈ ball c' β' →
          bergmanSup (ball c β) (fun z => multiplierWeight m (u z)) x ≤
            ENNReal.ofReal C *
              bergmanSup (ball c' β') (fun z => multiplierWeight m (u z)) x := by
  have hAb : Bornology.IsBounded (A : Set (ComplexModel d)) :=
    hAΩ.1.isBounded.subset subset_closure
  obtain ⟨C, hC, hCle⟩ := BergmanOverlapFixedCover.exists_overlapConst_ball hd A.isOpen
    hAconv hAb c c' hρ hρβ hcA hβ' hcA'
  refine ⟨C, hC, fun u hu m hm x hxc hxc' => ?_⟩
  refine QuantitativeRegularizationSmoothWeightLimit.bergmanSup_multiplierWeight_le_mul_of_smoothPsh
    hAΩ hu hm measurableSet_ball ((ball_subset_closedBall).trans hcA) isOpen_ball
    ((ball_subset_closedBall).trans hcA') (by simpa using hC) ENNReal.ofReal_ne_top hxc' ?_
  intro g hg hgB
  obtain ⟨B, hB⟩ := hgB
  obtain ⟨hsmooth, hlevi⟩ :=
    QuantitativeRegularizationSingularOverlap.smul_isAdmissibleWeight hg hm.le
  have hlower : ∀ z ∈ (A : Set (ComplexModel d)), -(-(m * B)) ≤ m * g z := by
    intro z hz
    simpa using mul_le_mul_of_nonneg_left (hB z hz) hm.le
  have := hCle (fun z => m * g z) hsmooth hlevi (-(m * B)) hlower x hxc hxc'
  simpa only [multiplierWeight_coe] using this

/-- The logarithmic form of a multiplicative comparison of two kernels. -/
theorem log_le_log_add_of_le_ofReal_mul {P Q : ℝ≥0∞} {C : ℝ} (hC : 0 < C)
    (h : P ≤ ENNReal.ofReal C * Q) :
    ENNReal.log P ≤ ENNReal.log Q + (Real.log C : EReal) := by
  calc ENNReal.log P ≤ ENNReal.log (ENNReal.ofReal C * Q) := ENNReal.log_monotone h
    _ = (Real.log C : EReal) + ENNReal.log Q := by
        rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC]
    _ = ENNReal.log Q + (Real.log C : EReal) := add_comm _ _

/-! ### `EReal` bookkeeping -/

/-- `L₁ ≤ L₂ + c` gives `a L₁ - r ≤ (a L₂ - r) + a c` for `a > 0` and reals `c`, `r`. -/
theorem mul_sub_le_mul_sub_add {a : ℝ} (ha : 0 < a) {L₁ L₂ : EReal} {c : ℝ}
    (h : L₁ ≤ L₂ + (c : EReal)) (r : ℝ) :
    (a : EReal) * L₁ - (r : EReal) ≤ ((a : EReal) * L₂ - (r : EReal)) + ((a * c : ℝ) : EReal) := by
  induction L₂ using EReal.rec with
  | bot =>
      rw [EReal.bot_add, le_bot_iff] at h
      rw [h, EReal.coe_mul_bot_of_pos ha, EReal.bot_sub]
      exact bot_le
  | top =>
      rw [EReal.coe_mul_top_of_pos ha, EReal.top_sub_coe, EReal.top_add_coe]
      exact le_top
  | coe t =>
      induction L₁ using EReal.rec with
      | bot =>
          rw [EReal.coe_mul_bot_of_pos ha, EReal.bot_sub]
          exact bot_le
      | top =>
          rw [← EReal.coe_add] at h
          exact absurd h (not_le.mpr (EReal.coe_lt_top _))
      | coe s =>
          rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
          rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub,
            ← EReal.coe_add, EReal.coe_le_coe_iff]
          nlinarith

/-- Raising the additive constant. -/
theorem add_coe_div_le_add_coe_div {L : EReal} {C C' : ℝ} (h : C ≤ C') {m : ℝ} (hm : 0 < m) :
    L + ((C / m : ℝ) : EReal) ≤ L + ((C' / m : ℝ) : EReal) :=
  add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_right h hm.le))

/-! ### The local comparison near one point -/

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]
  [IsComplexManifold d Z]

variable (ej el : ComplexChart d Z) (cj cl : ComplexModel d) (βj Pj βl Pl : ℝ) in
/-- **The overlap bound on a set `t` with constant `C`**: for every form `ζ`, every pair of
smooth potentials of `ζ` on the two potential balls, every `ζ`-PSH `φ` and every `m ≥ 1`, the
`j`-th chart branch is at most the `l`-th one plus `C/m` at every point of `t` in the `l`-th
patch. -/
def OverlapBound (t : Set Z) (C : ℝ) : Prop :=
  ∀ (ζ : SmoothRealForm d Z 2) (ρj ρl : ComplexModel d → ℝ),
    IsSmoothLocalPotential ζ ej (ball cj Pj) ρj →
    IsSmoothLocalPotential ζ el (ball cl Pl) ρl →
    ∀ φ : Z → EReal, ThetaPlurisubharmonic ζ φ → ∀ m : ℕ, 0 < m →
    ∀ x ∈ t, x ∈ chartPatch el (ball cl βl) →
      chartBergmanBranch ej (ball cj βj) ρj φ m x ≤
        chartBergmanBranch el (ball cl βl) ρl φ m x + ((C / (m : ℝ) : ℝ) : EReal)

/-- **`eq:reg-overlap` near one point.**  If `x₀` lies in the sources of both charts, with
`e_j(x₀) ∈ ball c_j β_j` and `e_l(x₀) ∈ closedBall c_l β_l`, then some open neighbourhood `N`
of `x₀` carries the overlap bound with a constant `C ≥ 0` fixed by the charts and balls. -/
theorem exists_nhds_overlapBound (hd : 0 < d) (ej el : ComplexChart d Z)
    {cj cl : ComplexModel d} {βj Pj βl Pl : ℝ} (hβPj : βj < Pj) (hβl : 0 < βl)
    (hβPl : βl < Pl) {x₀ : Z} (hx₀j : x₀ ∈ ej.val.source) (hx₀l : x₀ ∈ el.val.source)
    (hj : ej.val x₀ ∈ ball cj βj) (hl : el.val x₀ ∈ closedBall cl βl) :
    ∃ N : Set Z, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧
      OverlapBound ej el cj cl βj Pj βl Pl N C := by
  have hid : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (id : Z → Z) :=
    contMDiff_id
  set F : ComplexModel d → ComplexModel d := coordinateMap (id : Z → Z) ej el with hFdef
  set G : ComplexModel d → ComplexModel d := coordinateMap (id : Z → Z) el ej with hGdef
  set z₀ : ComplexModel d := ej.val x₀ with hz₀def
  set y₀ : ComplexModel d := el.val x₀ with hy₀def
  set Dom : Set (ComplexModel d) := coordinateDomain (id : Z → Z) ej el with hDomdef
  have hDomo : IsOpen Dom := coordinateDomain_isOpen hid ej el
  have hz₀Dom : z₀ ∈ Dom := mem_coordinateDomain hx₀j hx₀l
  have hFz₀ : F z₀ = y₀ := coordinateMap_at hx₀j
  -- the domain of the transported potential `ρ_l ∘ F`
  set PD : Set (ComplexModel d) := potentialDomain (id : Z → Z) ej el (ball cl Pl) with hPDdef
  have hPDo : IsOpen PD := potentialDomain_isOpen hid ej el isOpen_ball
  have hz₀PD : z₀ ∈ PD := by
    refine ⟨hz₀Dom, ?_⟩
    change F z₀ ∈ ball cl Pl
    rw [hFz₀]
    exact closedBall_subset_ball hβPl hl
  -- the Jacobian of `F` is bounded near `z₀`
  have hFcd : ContDiffOn ℂ ∞ F Dom := coordinateMap_contDiffOn hid ej el
  have hJcont : ContinuousAt (fun z => |((fderiv ℂ F z).restrictScalars ℝ).det|) z₀ := by
    have h1 : ContinuousAt (fun z => fderiv ℂ F z) z₀ :=
      (hFcd.continuousOn_fderiv_of_isOpen hDomo (by simp)).continuousAt (hDomo.mem_nhds hz₀Dom)
    have h2 : Continuous (fun L : ComplexModel d →L[ℂ] ComplexModel d => L.restrictScalars ℝ) :=
      (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel d) (ComplexModel d) ℝ ℝ).continuous
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      (h2.continuousAt.comp h1)).abs
  set A₀ : ℝ := |((fderiv ℂ F z₀).restrictScalars ℝ).det| + 1 with hA₀def
  have hA₀ : 0 < A₀ := by positivity
  have hJev : ∀ᶠ z in 𝓝 z₀, |((fderiv ℂ F z).restrictScalars ℝ).det| < A₀ :=
    hJcont.eventually (gt_mem_nhds (lt_add_one _))
  -- a ball around `z₀` where everything is available
  have hU : ball cj βj ∩ PD ∩ Dom ∩ {z | |((fderiv ℂ F z).restrictScalars ℝ).det| < A₀}
      ∈ 𝓝 z₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (isOpen_ball.mem_nhds hj)
      (hPDo.mem_nhds hz₀PD)) (hDomo.mem_nhds hz₀Dom)) hJev
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hε2 : 0 < ε / 2 := by positivity
  set D' : Set (ComplexModel d) := ball z₀ (ε / 2) with hD'def
  have hD'ε : D' ⊆ ball z₀ ε := ball_subset_ball (by linarith)
  have hD'U : ∀ z ∈ D', z ∈ ball cj βj ∧ z ∈ PD ∧ z ∈ Dom ∧
      |((fderiv ℂ F z).restrictScalars ℝ).det| < A₀ := fun z hz => by
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hεU (hD'ε hz)
    exact ⟨h1, h2, h3, h4⟩
  -- the image of `D'` is a neighbourhood of `y₀`
  have hFD' : F '' D' ∈ 𝓝 y₀ := by
    have h := (chartTransition ej el).image_mem_nhds (x := z₀) hz₀Dom (isOpen_ball.mem_nhds
      (mem_ball_self hε2))
    rw [← hFz₀]
    exact h
  obtain ⟨t₁, ht₁, ht₁D'⟩ := Metric.mem_nhds_iff.mp hFD'
  -- the comparison ball `E = ball y₀ t₀` in the chart `e_l`
  set P' : ℝ := (βl + Pl) / 2 with hP'def
  have hβP' : βl < P' := by rw [hP'def]; linarith
  have hP'P : P' < Pl := by rw [hP'def]; linarith
  set t₀ : ℝ := min (t₁ / 2) ((P' - βl) / 2) with ht₀def
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by linarith)
  have hEsub : ball y₀ t₀ ⊆ F '' D' :=
    (ball_subset_ball ((min_le_left _ _).trans (by linarith))).trans ht₁D'
  have hEA : closedBall y₀ t₀ ⊆ ball cl P' := by
    intro z hz
    rw [mem_closedBall] at hz hl
    rw [mem_ball]
    have : t₀ ≤ (P' - βl) / 2 := min_le_right _ _
    linarith [dist_triangle z y₀ cl]
  let A : Opens (ComplexModel d) := ⟨ball cl P', isOpen_ball⟩
  let Ω : Opens (ComplexModel d) := ⟨ball cl Pl, isOpen_ball⟩
  have hAconv : Convex ℝ (A : Set (ComplexModel d)) := convex_ball cl P'
  have hAΩ : RelativelyCompactIn A Ω :=
    ⟨isBounded_ball.isCompact_closure,
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball hP'P)⟩
  obtain ⟨C₀, hC₀, hC₀le⟩ := exists_overlapConst_pair_multiplierWeight hd hAconv hAΩ y₀ cl
    (ρ := t₀ / 2) (β := t₀) (β' := βl) (by positivity) (by linarith) hEA hβl
    (closedBall_subset_ball hβP')
  -- the neighbourhood
  set N : Set Z := (ej.val.source ∩ ej.val ⁻¹' D') ∩
    (el.val.source ∩ el.val ⁻¹' ball y₀ (t₀ / 2 / 2)) with hNdef
  have hNo : IsOpen N :=
    (ej.val.isOpen_inter_preimage isOpen_ball).inter (el.val.isOpen_inter_preimage isOpen_ball)
  have hx₀N : x₀ ∈ N :=
    ⟨⟨hx₀j, mem_ball_self hε2⟩, ⟨hx₀l, mem_ball_self (by positivity)⟩⟩
  set Cf : ℝ := max 0 (Real.log C₀ + Real.log A₀) with hCfdef
  refine ⟨N, hNo, hx₀N, Cf, le_max_left _ _, ?_⟩
  intro ζ ρj ρl hρj hρl φ hφ m hm x hxN hxl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨⟨hxj, hxD'⟩, ⟨hxl', hxE⟩⟩ := hxN
  set yj : ComplexModel d := ej.val x with hyjdef
  set y : ComplexModel d := el.val x with hydef
  have hFyj : F yj = y := coordinateMap_at hxj
  have hyjU := hD'U yj hxD'
  -- the two potentials of `ζ` on `ball z₀ ε`
  have hρjε : IsSmoothLocalPotential ζ ej (ball z₀ ε) ρj :=
    hρj.mono isOpen_ball fun z hz => ball_subset_ball hβPj.le (hεU hz).1.1.1
  have hρlF : IsSmoothLocalPotential ζ ej PD (ρl ∘ F) :=
    (SmoothRealForm.pullback_id_geometricallyEq ζ).localPotential_iff ej PD (ρl ∘ F) |>.mp
      (isSmoothLocalPotential_pullback hid ej hρl)
  have hρlFε : IsSmoothLocalPotential ζ ej (ball z₀ ε) (ρl ∘ F) :=
    hρlF.mono isOpen_ball fun z hz => (hεU hz).1.1.2
  -- the weights
  set wl : ComplexModel d → ℝ≥0∞ :=
    fun z => multiplierWeight (m : ℝ) (correctedWeight el ρl φ z) with hwldef
  set wj : ComplexModel d → ℝ≥0∞ :=
    fun z => multiplierWeight (m : ℝ) (correctedWeight ej ρj φ z) with hwjdef
  -- Step 1: shrink `B_j` to `D'`
  have hpatchD' : x ∈ chartPatch ej D' := ⟨hxj, hxD'⟩
  have hpatchBj : x ∈ chartPatch ej (ball cj βj) := ⟨hxj, hyjU.1⟩
  have hstep1 : chartBergmanBranch ej (ball cj βj) ρj φ m x ≤
      chartBergmanBranch ej D' ρj φ m x := by
    rw [chartBergmanBranch_of_mem hpatchBj, chartBergmanBranch_of_mem hpatchD']
    refine EReal.sub_le_sub (mul_le_mul_of_nonneg_left ?_ (EReal.coe_nonneg.mpr
      (inv_nonneg.mpr hmR.le))) le_rfl
    exact ENNReal.log_monotone (BergmanBiholomorphicTransport.bergmanSup_le_of_subset
      (fun z hz => (hD'U z hz).1) _ _)
  -- Step 2: change the potential on `D'` to `ρ_l ∘ F`
  have hstep2 : chartBergmanBranch ej D' ρj φ m x =
      chartBergmanBranch ej D' (ρl ∘ F) φ m x :=
    (chartBergmanBranch_eq_of_potentials hε hρjε hρlFε isOpen_ball subset_rfl φ hm
      hpatchD').symm
  -- the transported weight is `w_l ∘ F` on `D'`
  have hweight : ∀ z ∈ D', multiplierWeight (m : ℝ) (correctedWeight ej (ρl ∘ F) φ z) =
      wl (F z) := by
    intro z hz
    have hzDom : z ∈ Dom := (hD'U z hz).2.2.1
    have hsymm : el.val.symm (F z) = ej.val.symm z :=
      el.val.left_inv (hzDom.2 : ej.val.symm z ∈ el.val.source)
    simp only [hwldef, correctedWeight, chartFunction, Function.comp_apply, hsymm]
  -- Step 3: transport to the chart `e_l`
  have hFdiff : DifferentiableOn ℂ F D' :=
    (hFcd.differentiableOn (by simp)).mono fun z hz => (hD'U z hz).2.2.1
  have hGF : ∀ z ∈ D', G (F z) = z := by
    intro z hz
    have hzDom : z ∈ Dom := (hD'U z hz).2.2.1
    have hz2 : ej.val.symm z ∈ el.val.source := hzDom.2
    simp only [hGdef, hFdef, coordinateMap, Function.comp_apply, id]
    rw [el.val.left_inv hz2, ej.val.right_inv hzDom.1]
  have hGdiff : DifferentiableOn ℂ G (F '' D') := by
    refine ((coordinateMap_contDiffOn hid el ej).differentiableOn (by simp)).mono ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzDom : z ∈ Dom := (hD'U z hz).2.2.1
    have hz2 : ej.val.symm z ∈ el.val.source := hzDom.2
    refine ⟨el.val.map_source hz2, ?_⟩
    change el.val.symm (F z) ∈ ej.val.source
    simp only [hFdef, coordinateMap, Function.comp_apply, id]
    rw [el.val.left_inv hz2]
    exact ej.val.map_target hzDom.1
  have hJ : ∀ z ∈ D', BergmanBiholomorphicTransport.realJacobian F z ≤ ENNReal.ofReal A₀ :=
    fun z hz => ENNReal.ofReal_le_ofReal (hD'U z hz).2.2.2.le
  have hstep3 := BergmanBiholomorphicTransport.bergmanLog_le_image isOpen_ball hFdiff hGdiff hGF
    hA₀ hJ wl hxD'
  rw [hFyj] at hstep3
  -- Steps 4 and 5: shrink to `E` and compare with `B_l`
  have hstep4 : bergmanLog (F '' D') wl y ≤ bergmanLog (ball y₀ t₀) wl y :=
    ENNReal.log_monotone (BergmanBiholomorphicTransport.bergmanSup_le_of_subset hEsub _ _)
  have hu : PlurisubharmonicOn (correctedWeight el ρl φ) Ω :=
    plurisubharmonicOn_correctedWeight hφ hρl
  have hstep5 : bergmanLog (ball y₀ t₀) wl y ≤
      bergmanLog (ball cl βl) wl y + (Real.log C₀ : EReal) :=
    log_le_log_add_of_le_ofReal_mul hC₀ (hC₀le _ hu (m : ℝ) hmR y hxE hxl.2)
  -- assemble
  have hD'log : bergmanLog D' (fun z => multiplierWeight (m : ℝ)
      (correctedWeight ej (ρl ∘ F) φ z)) yj = bergmanLog D' (fun z => wl (F z)) yj := by
    simp only [bergmanLog]
    rw [QuantitativeRegularizationSingularWeight.bergmanSup_congr_of_eqOn
      measurableSet_ball hweight]
  have hchain : bergmanLog D' (fun z => multiplierWeight (m : ℝ)
      (correctedWeight ej (ρl ∘ F) φ z)) yj ≤
        bergmanLog (ball cl βl) wl y + ((Real.log C₀ + Real.log A₀ : ℝ) : EReal) := by
    rw [hD'log, EReal.coe_add, ← add_assoc]
    refine hstep3.trans (add_le_add_left (hstep4.trans hstep5) _)
  refine (hstep1.trans_eq hstep2).trans ?_
  rw [chartBergmanBranch_of_mem hpatchD', chartBergmanBranch_of_mem hxl]
  have hρF : (ρl ∘ F) (ej.val x) = ρl y := by
    simp only [Function.comp_apply]
    rw [hFyj]
  rw [hρF]
  refine (mul_sub_le_mul_sub_add (inv_pos.mpr hmR) hchain (ρl y)).trans ?_
  refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (le_max_right _ _) hmR.le

/-! ### One constant on a compact set -/

/-- **`eq:reg-overlap` on a compact set** (Copy-4 `lem:regularization`, Step 2).  If the
compact `K` lies in the sources of both charts, with `e_j(K) ⊆ ball c_j β_j` and
`e_l(K) ⊆ closedBall c_l β_l`, then one constant `C ≥ 0`, fixed by the charts and balls,
gives `b_j ≤ b_l + C/m` at every point of `K` in the `l`-th patch, for every `ζ`, every pair
of potentials, every `ζ`-PSH `φ` and every `m ≥ 1`. -/
theorem exists_const_overlapBound (hd : 0 < d) (ej el : ComplexChart d Z)
    {cj cl : ComplexModel d} {βj Pj βl Pl : ℝ} (hβPj : βj < Pj) (hβl : 0 < βl)
    (hβPl : βl < Pl) {K : Set Z} (hK : IsCompact K)
    (hKj : ∀ x ∈ K, x ∈ ej.val.source ∧ ej.val x ∈ ball cj βj)
    (hKl : ∀ x ∈ K, x ∈ el.val.source ∧ el.val x ∈ closedBall cl βl) :
    ∃ C : ℝ, 0 ≤ C ∧ OverlapBound ej el cj cl βj Pj βl Pl K C := by
  refine hK.induction_on (p := fun t => ∃ C : ℝ, 0 ≤ C ∧ OverlapBound ej el cj cl βj Pj βl Pl t C)
    ⟨0, le_rfl, fun _ _ _ _ _ _ _ _ _ x hx => absurd hx (notMem_empty x)⟩ ?_ ?_ ?_
  · rintro s t hst ⟨C, hC, h⟩
    exact ⟨C, hC, fun ζ ρj ρl hρj hρl φ hφ m hm x hx => h ζ ρj ρl hρj hρl φ hφ m hm x (hst hx)⟩
  · rintro s t ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
    refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun ζ ρj ρl hρj hρl φ hφ m hm x hx hxl => ?_⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rcases hx with hx | hx
    · exact (h₁ ζ ρj ρl hρj hρl φ hφ m hm x hx hxl).trans
        (add_coe_div_le_add_coe_div (le_max_left _ _) hmR)
    · exact (h₂ ζ ρj ρl hρj hρl φ hφ m hm x hx hxl).trans
        (add_coe_div_le_add_coe_div (le_max_right _ _) hmR)
  · intro x hx
    obtain ⟨N, hN, hxN, C, hC, h⟩ := exists_nhds_overlapBound hd ej el hβPj hβl hβPl
      (hKj x hx).1 (hKl x hx).1 (hKj x hx).2 (hKl x hx).2
    exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.mem_nhds hxN), C, hC, h⟩

end

end Hironaka.QuantitativeRegularizationChartOverlap
