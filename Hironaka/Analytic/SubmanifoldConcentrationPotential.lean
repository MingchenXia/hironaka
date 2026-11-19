import Hironaka.Analytic.ConcentrationPotentialLevi
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Analytic.IdealPresentation
import Hironaka.Analytic.ChartPartition
import Hironaka.Analytic.ManifoldTubePositivity
import Hironaka.Analytic.KahlerDomination
import Hironaka.Analytic.MeteredDivisorWeightBounds

set_option autoImplicit false

/-!
# Demailly--Păun's concentration potentials along a closed submanifold

Source: Demailly--Păun, Lemma 2.1 (`dp04-kahler-cone:2.1`,
`references/dp04-kahler-cone/source/0105176.tex:588-700`), the construction of `ψ`, `ψ_ε` and
`ω_ε`; quoted by Boucksom (`bou02-volume:4.11`).  Used for
Boucksom 4.8 (programme TN.4).

Let `Y` be a closed complex submanifold of a compact complex manifold `M` with a Kähler form `ω`.

* `ConcentrationPartition` — dp04's data: finitely many local generator systems `g_{a,·}` of the
  vanishing ideal `𝓘_Y` (holomorphic on open domains; off `Y` the unit ideal), and a chart-smooth
  partition of unity `θ_a` subordinate to the domains.  (dp04 normalises `∑ θ_a² = 1`; only
  `∑ θ_a = 1` is used here, the weight below carries the squares.)
* `weight` — `U = ∑_a θ_a² ∑_i |g_{a,i}|²` (dp04's `e^{2ψ}`); `chartSmooth_weight`,
  `weight_eq_zero_of_mem`, `weight_pos_of_notMem`.
* `exists_nhds_genNormSq_le_weight` — comparability of the generator systems near every point
  (dp04: "by Cartan's theorem A ... all terms `|g_{j,k}|²` are uniformly bounded by
  `e^{2ψ} + ε²`"), from `IdealWeightComparison` and the generating property.
* `exists_local_levi_bound`, `exists_pos_isSemipositive_ddc_log_weight` — **dp04 2.1 (ii)**: one
  `A > 0` with `ddᶜ log (U + s) + A ω ≥ 0` for every `s > 0`; the local estimate is
  `ConcentrationPotentialLevi.neg_le_leviForm_log_sum` (dp04 (2.2)--(2.3)), made uniform by
  compactness and transported between charts by the tensor law of forms;
  `exists_pos_levi_log_weight`: the same `A` for `log U` itself at points where `U > 0` (`s → 0⁺`).
* `potential`, `isSemipositive_half_add_ddc_potential` — `f_ε = log (U + ε²) / (2A)` and
  `½ ω + ddᶜ f_ε ≥ 0`, i.e. **`ω_ε = ω + ddᶜ f_ε ≥ ω/2`** (dp04 2.1 (iii), first sentence).
* `tube`, `isOpen_tube`, `tube_mono`, `iInter_closure_tube_subset` — `V_ε = {U < ε²}` (dp04's
  `{ψ < log ε}`) are open, increase with `ε`, and shrink to `Y`.
* `exists_of_isCoherent` — a concentration partition exists whenever `𝓘_Y` is coherent.
* `exists_adapted` — for a point `x ∈ Y` regular of dimension `k`, a partition whose weight equals
  `∑_{i ≥ k} |ζ_i|²` near `x`, `ζ` the flat coordinates of the flattening at `x` (`flatGen`).
  This is the one adaptation of the source: the partition is chosen with `θ_{a₀} = 1` near `x`,
  so that the local mass estimate at `x` (next module) works with the exact formula
  `log (|ζ''|² + ε²)` instead of dp04's eigenvalue argument with the `γ_{j,k}`.  The
  consumer fixes `x` first (blueprint `bou:uniform-diagonal-domination`).

Not here: the lower bound of the mass of `ω_ε^p ∧ ω^{N-p}` on `U ∩ V_ε` (dp04 2.1 (iii)/(iv),
next module) and the diagonal of `X × X`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.SubmanifoldConcentrationPotential

open Hironaka.HolomorphicIdealSheaves ChartPartition
open Hironaka.IdealWeightComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n) in
/-- A finite family of local generator systems of the vanishing ideal of `Y` (each on an open
domain, holomorphic there and generating `𝓘_Y` at every point of it), with a chart-smooth partition
of unity subordinate to the domains.  Off `Y` a generator system may be the constant `1`. -/
structure ConcentrationPartition (Y : Set M) (ι : Type*) [Fintype ι] where
  dom : ι → Set M
  isOpen_dom : ∀ a, IsOpen (dom a)
  arity : ι → ℕ
  gen : (a : ι) → Fin (arity a) → M → ℂ
  gen_mdifferentiableOn : ∀ a i,
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (gen a i) (dom a)
  gen_spec : ∀ a, ∀ y ∈ dom a, ∀ f,
    (vanishingIdeal (n := n) Y).mem y f ↔ IsInSpanAt (n := n) (· ∈ range (gen a)) y f
  part : ι → M → ℝ
  part_smooth : ∀ a, ChartSmooth (n := n) (part a)
  part_nonneg : ∀ a y, 0 ≤ part a y
  part_tsupport : ∀ a, tsupport (part a) ⊆ dom a
  part_sum : ∀ y, ∑ a, part a y = 1

namespace ConcentrationPartition

variable {Y : Set M} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n Y ι)

/-- `∑_i |g_{a,i}|²`, extended by zero off the `a`-th domain. -/
def genNormSq (a : ι) : M → ℝ :=
  (P.dom a).indicator (generatorNormSq (P.gen a))

/-- **Demailly--Păun's weight** `U = ∑_a θ_a² ∑_i |g_{a,i}|²` (dp04 2.1, `e^{2ψ}`). -/
def weight (y : M) : ℝ := ∑ a, P.part a y ^ 2 * P.genNormSq a y

theorem genNormSq_nonneg (a : ι) (y : M) : 0 ≤ P.genNormSq a y :=
  Set.indicator_nonneg (fun _ _ => generatorNormSq_nonneg _ _) y

theorem weight_nonneg (y : M) : 0 ≤ P.weight y :=
  Finset.sum_nonneg fun a _ => mul_nonneg (sq_nonneg _) (P.genNormSq_nonneg a y)

theorem part_le_one (a : ι) (y : M) : P.part a y ≤ 1 := by
  rw [← P.part_sum y]
  exact Finset.single_le_sum (fun b _ => P.part_nonneg b y) (Finset.mem_univ a)

theorem part_eq_zero_of_notMem_tsupport {a : ι} {y : M} (hy : y ∉ tsupport (P.part a)) :
    P.part a y = 0 :=
  image_eq_zero_of_notMem_tsupport hy

theorem continuousAt_part (a : ι) (x : M) : ContinuousAt (P.part a) x :=
  MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (n := n) (h := P.part a)
    isOpen_univ (fun e => by simpa using P.part_smooth a e) (mem_univ x)

theorem exists_part_pos (y : M) : ∃ a, 0 < P.part a y := by
  by_contra hcon
  push Not at hcon
  have hle : ∑ a, P.part a y ≤ 0 := Finset.sum_nonpos fun a _ => hcon a
  rw [P.part_sum y] at hle
  linarith

/-- The generators read in a chart are holomorphic near every point of the domain. -/
theorem eventually_differentiableAt_gen_chart (a : ι) (i : Fin (P.arity a))
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hza : e.val.symm z ∈ P.dom a) :
    ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => P.gen a i (e.val.symm w)) w := by
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' P.dom a) :=
    e.val.isOpen_inter_preimage_symm (P.isOpen_dom a)
  filter_upwards [hopen.mem_nhds ⟨hz, hza⟩] with w hw
  exact mdifferentiableAt_iff_differentiableAt.mp
    (((P.gen_mdifferentiableOn a i).mdifferentiableAt ((P.isOpen_dom a).mem_nhds hw.2)).comp w
      (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hw.1))

open Classical in
/-- Near a chart point, the `a`-th term of the weight is `θ_a² ∑_i |g_{a,i}|²` if the point lies
in the closed support of `θ_a`, and vanishes identically otherwise. -/
theorem eventually_term_eq (a : ι) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    ∀ᶠ w in 𝓝 z, P.part a (e.val.symm w) ^ 2 * P.genNormSq a (e.val.symm w) =
      if e.val.symm z ∈ tsupport (P.part a) then
        ∑ i, P.part a (e.val.symm w) ^ 2 * Complex.normSq (P.gen a i (e.val.symm w))
      else 0 := by
  split_ifs with hza
  · have hdom : e.val.symm z ∈ P.dom a := P.part_tsupport a hza
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' P.dom a) :=
      e.val.isOpen_inter_preimage_symm (P.isOpen_dom a)
    filter_upwards [hopen.mem_nhds ⟨hz, hdom⟩] with w hw
    have hw2 : e.val.symm w ∈ P.dom a := hw.2
    rw [genNormSq, Set.indicator_of_mem hw2, generatorNormSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_norm_sq]
  · have hcl : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (tsupport (P.part a))ᶜ) :=
      e.val.isOpen_inter_preimage_symm (isClosed_tsupport _).isOpen_compl
    filter_upwards [hcl.mem_nhds ⟨hz, hza⟩] with w hw
    rw [P.part_eq_zero_of_notMem_tsupport hw.2]
    ring

/-- **The weight is chart-smooth.** -/
theorem chartSmooth_weight : ChartSmooth (n := n) P.weight := by
  classical
  intro e z hz
  refine ContDiffAt.contDiffWithinAt ?_
  simp only [weight]
  refine ContDiffAt.sum fun a _ => ?_
  have hpart : ContDiffAt ℝ ∞ (fun w => P.part a (e.val.symm w)) z :=
    (P.part_smooth a e).contDiffAt (e.val.open_target.mem_nhds hz)
  refine ContDiffAt.congr_of_eventuallyEq ?_ (P.eventually_term_eq a e hz)
  split_ifs with hza
  · refine ContDiffAt.sum fun i _ => (hpart.pow 2).mul ?_
    have hG := P.eventually_differentiableAt_gen_chart a i e hz (P.part_tsupport a hza)
    have h := ConcentrationPotentialLevi.contDiffAt_of_eventually_differentiableAt hG
    have hfun : (fun w => Complex.normSq (P.gen a i (e.val.symm w))) =
        fun w => ‖P.gen a i (e.val.symm w)‖ ^ 2 := by
      funext w; exact Complex.normSq_eq_norm_sq _
    rw [hfun]
    exact (contDiff_norm_sq ℝ).contDiffAt.comp z h
  · exact contDiffAt_const

/-- `log (U + s)` is chart-smooth for `s > 0`. -/
theorem chartSmooth_log_weight {s : ℝ} (hs : 0 < s) :
    ChartSmooth (n := n) fun y => Real.log (P.weight y + s) := by
  intro e z hz
  have h := (P.chartSmooth_weight e z hz).add (contDiffWithinAt_const (c := s))
  exact h.log (ne_of_gt (add_pos_of_nonneg_of_pos (P.weight_nonneg _) hs))

/-- **Comparability of the generator systems** (dp04: "the generators `(g_{j,k})` can be
expressed as holomorphic linear combinations of the `(g_{j',k})` by Cartan's theorem A").
Near a point `y₀`, every generator system whose cut-off reaches `y₀` is dominated by the weight. -/
theorem exists_nhds_genNormSq_le_weight (y₀ : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 y₀, ∀ a, y₀ ∈ tsupport (P.part a) →
      generatorNormSq (P.gen a) y ≤ C * P.weight y := by
  classical
  obtain ⟨a₀, ha₀⟩ := P.exists_part_pos y₀
  have hy₀ : y₀ ∈ P.dom a₀ := P.part_tsupport a₀ (subset_tsupport _ ha₀.ne')
  have hmemgen : ∀ a, y₀ ∈ P.dom a → ∀ j,
      IsInSpanAt (n := n) (· ∈ range (P.gen a₀)) y₀ (P.gen a j) := by
    intro a hya j
    refine (P.gen_spec a₀ y₀ hy₀ _).mp ((P.gen_spec a y₀ hya _).mpr ?_)
    refine isInSpanAt_of_eq_mul ⟨j, rfl⟩ ?_ (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
    filter_upwards [(P.isOpen_dom a).mem_nhds hya] with z hz
    exact (P.gen_mdifferentiableOn a j z hz).mdifferentiableAt ((P.isOpen_dom a).mem_nhds hz)
  have key : ∀ a, ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 y₀, y₀ ∈ tsupport (P.part a) →
      generatorNormSq (P.gen a) y ≤ B * generatorNormSq (P.gen a₀) y := by
    intro a
    by_cases hya : y₀ ∈ tsupport (P.part a)
    · obtain ⟨B, hB, hBy⟩ := exists_nhds_generatorNormSq_le_of_forall_isInSpanAt
        (hmemgen a (P.part_tsupport a hya))
      exact ⟨B, hB, hBy.mono fun y hy _ => hy⟩
    · exact ⟨1, one_pos, Eventually.of_forall fun y h => absurd h hya⟩
  choose B hB hBy using key
  have hall := eventually_all.mpr hBy
  have hlow : ∀ᶠ y in 𝓝 y₀, P.part a₀ y₀ / 2 < P.part a₀ y :=
    (P.continuousAt_part a₀ y₀).eventually (eventually_gt_nhds (by linarith))
  have hsum : (0 : ℝ) ≤ ∑ a, B a := Finset.sum_nonneg fun a _ => (hB a).le
  set c := P.part a₀ y₀ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  refine ⟨(∑ a, B a + 1) / c ^ 2, by positivity, ?_⟩
  filter_upwards [hall, hlow, (P.isOpen_dom a₀).mem_nhds hy₀] with y hyB hylow hyd a ha
  have hterm : P.part a₀ y ^ 2 * generatorNormSq (P.gen a₀) y ≤ P.weight y := by
    have h1 : P.genNormSq a₀ y = generatorNormSq (P.gen a₀) y := Set.indicator_of_mem hyd _
    rw [← h1]
    exact Finset.single_le_sum (f := fun a => P.part a y ^ 2 * P.genNormSq a y)
      (fun a _ => mul_nonneg (sq_nonneg _) (P.genNormSq_nonneg a y)) (Finset.mem_univ a₀)
  have hN0 : 0 ≤ generatorNormSq (P.gen a₀) y := generatorNormSq_nonneg _ _
  have hc2 : c ^ 2 * generatorNormSq (P.gen a₀) y ≤ P.weight y := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hN0) hterm
    exact pow_le_pow_left₀ hcpos.le hylow.le 2
  have hBa : B a ≤ ∑ a, B a + 1 := by
    have := Finset.single_le_sum (f := B) (fun b _ => (hB b).le) (Finset.mem_univ a)
    linarith
  calc generatorNormSq (P.gen a) y ≤ B a * generatorNormSq (P.gen a₀) y := hyB a ha
    _ ≤ (∑ a, B a + 1) * generatorNormSq (P.gen a₀) y := mul_le_mul_of_nonneg_right hBa hN0
    _ = (∑ a, B a + 1) / c ^ 2 * (c ^ 2 * generatorNormSq (P.gen a₀) y) := by
        field_simp
    _ ≤ (∑ a, B a + 1) / c ^ 2 * P.weight y :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)

end ConcentrationPartition

/-! ### Local estimates in a chart -/

section LocalBounds

open ConcentrationPotentialLevi KahlerDomination

/-- A Kähler form is quantitatively positive near every chart point. -/
theorem exists_eventually_kahler_lower (omega : PositiveClasses.KahlerBackground n M)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ z in 𝓝 z₀, ∀ v : ComplexModel n,
      m * ‖v‖ ^ 2 ≤ omega.form.val.coeff e z ![v, Complex.I • v] := by
  obtain ⟨m, hm, hmle⟩ := exists_lineValue_lower_bound (omega.isKahler.1 e z₀ hz₀).2
  refine ⟨m / 2, by positivity, ?_⟩
  have hωc : ContinuousAt (omega.form.val.coeff e) z₀ :=
    ((omega.form.val.smooth e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz₀)
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖omega.form.val.coeff e z - omega.form.val.coeff e z₀‖ < m / 2 := by
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hωc (m / 2) (by positivity)
  filter_upwards [h1] with z hz1 v
  have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
  have hsplit : omega.form.val.coeff e z ![v, Complex.I • v]
      = omega.form.val.coeff e z₀ ![v, Complex.I • v]
        + (omega.form.val.coeff e z - omega.form.val.coeff e z₀) ![v, Complex.I • v] := by simp
  have hdrift := neg_le_of_abs_le (abs_lineValue_le
    (omega.form.val.coeff e z - omega.form.val.coeff e z₀) v)
  have := hmle v
  nlinarith [mul_le_mul_of_nonneg_right hz1.le hv2]

/-- For a chart-smooth `h` with `|h| ≤ 1`, the remainder `|∂h(v)|² - h ddᶜh(v, v̄)` of dp04 (2.2)
is bounded by `K ‖v‖²` near every chart point. -/
theorem exists_eventually_remainder_le {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hle : ∀ y, |h y| ≤ 1) (e : ComplexChart n M) {z₀ : ComplexModel n}
    (hz₀ : z₀ ∈ e.val.target) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ z in 𝓝 z₀, ∀ v : ComplexModel n,
      Complex.normSq (delC (fun w => h (e.val.symm w)) z v) -
          h (e.val.symm z) * leviForm (fun w => h (e.val.symm w)) z v ≤ K * ‖v‖ ^ 2 := by
  set c : ComplexModel n → ℝ := fun w => h (e.val.symm w) with hc_def
  have hcs : ContDiffOn ℝ ∞ c e.val.target := hh e
  have hdc : ContinuousAt (fderiv ℝ c) z₀ :=
    (hcs.continuousOn_fderiv_of_isOpen e.val.open_target (by simp)).continuousAt
      (e.val.open_target.mem_nhds hz₀)
  have hddc : ContinuousAt (fun z => Hironaka.smoothDDC c z) z₀ := by
    have := ((ManifoldTubePositivity.ddcClosedForm h hh).val.smooth e).continuousOn.continuousAt
      (e.val.open_target.mem_nhds hz₀)
    simpa [ManifoldTubePositivity.ddcClosedForm_coeff, hc_def] using this
  set D₁ := ‖fderiv ℝ c z₀‖ + 1
  set D₂ := ‖Hironaka.smoothDDC c z₀‖ + 1
  have hD₁ : 0 ≤ D₁ := by positivity
  have hD₂ : 0 ≤ D₂ := by positivity
  refine ⟨D₁ ^ 2 / 2 + Real.pi * D₂, by positivity, ?_⟩
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ c z‖ ≤ D₁ := by
    have := hdc.norm.eventually (gt_mem_nhds (show ‖fderiv ℝ c z₀‖ < D₁ by simp [D₁]))
    exact this.mono fun z hz => hz.le
  have h2 : ∀ᶠ z in 𝓝 z₀, ‖Hironaka.smoothDDC c z‖ ≤ D₂ := by
    have := hddc.norm.eventually (gt_mem_nhds (show ‖Hironaka.smoothDDC c z₀‖ < D₂ by simp [D₂]))
    exact this.mono fun z hz => hz.le
  have h3 : ∀ᶠ z in 𝓝 z₀, z ∈ e.val.target := e.val.open_target.mem_nhds hz₀
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3 v
  have hc2 : ContDiffAt ℝ 2 c z :=
    (hcs.contDiffAt (e.val.open_target.mem_nhds hz3)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
  -- the first-order part
  have hIv : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul]; simp
  have hd1 : |fderiv ℝ c z v| ≤ D₁ * ‖v‖ :=
    ((fderiv ℝ c z).le_opNorm v).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans
      (mul_le_mul_of_nonneg_right hz1 (norm_nonneg _))
  have hd2 : |fderiv ℝ c z (Complex.I • v)| ≤ D₁ * ‖v‖ := by
    have := ((fderiv ℝ c z).le_opNorm (Complex.I • v)).trans
      (mul_le_mul_of_nonneg_right hz1 (norm_nonneg _))
    rwa [hIv, ← Real.norm_eq_abs] at *
  have hdel : Complex.normSq (delC c z v) ≤ D₁ ^ 2 / 2 * ‖v‖ ^ 2 := by
    rw [normSq_delC]
    have e1 : fderiv ℝ c z v ^ 2 ≤ (D₁ * ‖v‖) ^ 2 := sq_le_sq' (abs_le.mp hd1).1 (abs_le.mp hd1).2
    have e2 : fderiv ℝ c z (Complex.I • v) ^ 2 ≤ (D₁ * ‖v‖) ^ 2 :=
      sq_le_sq' (abs_le.mp hd2).1 (abs_le.mp hd2).2
    nlinarith
  -- the second-order part
  have hlevi : leviForm c z v = Real.pi * Hironaka.smoothDDC c z ![v, Complex.I • v] := by
    rw [Hironaka.smoothDDC_complexDiagonal_eq_leviForm hc2 v]
    field_simp
  have hsd : |Hironaka.smoothDDC c z ![v, Complex.I • v]| ≤ D₂ * ‖v‖ ^ 2 :=
    (abs_lineValue_le _ v).trans (mul_le_mul_of_nonneg_right hz2 hv2)
  have hhz : |h (e.val.symm z)| ≤ 1 := hle _
  have hprod : -(h (e.val.symm z) * leviForm c z v) ≤ Real.pi * (D₂ * ‖v‖ ^ 2) := by
    rw [hlevi]
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have : |h (e.val.symm z) * (Real.pi * Hironaka.smoothDDC c z ![v, Complex.I • v])| ≤
        Real.pi * (D₂ * ‖v‖ ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hpi]
      calc |h (e.val.symm z)| * (Real.pi * |Hironaka.smoothDDC c z ![v, Complex.I • v]|)
          ≤ 1 * (Real.pi * (D₂ * ‖v‖ ^ 2)) := by
            apply mul_le_mul hhz _ (by positivity) zero_le_one
            exact mul_le_mul_of_nonneg_left hsd hpi
        _ = _ := one_mul _
    linarith [neg_abs_le (h (e.val.symm z) * (Real.pi * Hironaka.smoothDDC c z ![v, Complex.I • v]))]
  nlinarith

end LocalBounds

namespace ConcentrationPartition

open ConcentrationPotentialLevi KahlerDomination

variable {Y : Set M} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n Y ι)

/-- **dp04 2.1 (ii), locally.**  Near every point, in its preferred chart, one constant `A`
bounds the Levi form of `log (U + s)` below by `-A ω`, for every `s > 0`. -/
theorem exists_local_levi_bound (omega : PositiveClasses.KahlerBackground n M) (y₀ : M) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ z in 𝓝 ((complexChartAt (n := n) y₀).val y₀),
      z ∈ (complexChartAt (n := n) y₀).val.target ∧ ∀ s : ℝ, 0 < s → ∀ v : ComplexModel n,
        -(A * omega.form.val.coeff (complexChartAt (n := n) y₀) z ![v, Complex.I • v]) ≤
          leviForm (fun w => Real.log
            (P.weight ((complexChartAt (n := n) y₀).val.symm w) + s)) z v := by
  classical
  set e := complexChartAt (n := n) y₀ with he
  have hy₀ : y₀ ∈ e.val.source := mem_complexChartAt_source y₀
  set z₀ := e.val y₀ with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hy₀
  have hsym : e.val.symm z₀ = y₀ := e.val.left_inv hy₀
  -- the active indices and the local family
  let T := {a : ι // y₀ ∈ tsupport (P.part a)}
  let J := Σ a : T, Fin (P.arity a.1)
  let c : J → ComplexModel n → ℝ := fun j w => P.part j.1.1 (e.val.symm w)
  let G : J → ComplexModel n → ℂ := fun j w => P.gen j.1.1 j.2 (e.val.symm w)
  -- the local representation `U = ∑_j c_j² |G_j|²`
  have hrep : ∀ᶠ w in 𝓝 z₀, P.weight (e.val.symm w) =
      ∑ j : J, c j w ^ 2 * Complex.normSq (G j w) := by
    filter_upwards [eventually_all.mpr fun a => P.eventually_term_eq a e hz₀] with w hw
    rw [weight, Finset.sum_congr rfl fun a _ => hw a]
    simp only [hsym]
    rw [← Finset.sum_filter, Finset.sum_subtype (p := fun a => y₀ ∈ tsupport (P.part a))
      (Finset.univ.filter fun a => y₀ ∈ tsupport (P.part a)) (fun a => by simp)
      (fun a => ∑ i, P.part a (e.val.symm w) ^ 2 * Complex.normSq (P.gen a i (e.val.symm w))),
      Fintype.sum_sigma]
  have hrep2 := hrep.eventually_nhds
  -- comparability, pulled back to the chart
  obtain ⟨C, hC, hCy⟩ := P.exists_nhds_genNormSq_le_weight y₀
  have htend : Tendsto e.val.symm (𝓝 z₀) (𝓝 y₀) := by
    have := (e.val.continuousAt_symm hz₀).tendsto
    rwa [hsym] at this
  have hCz := htend.eventually hCy
  -- the second-order remainders of the cut-offs
  have hK : ∀ a, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ z in 𝓝 z₀, ∀ v : ComplexModel n,
      Complex.normSq (delC (fun w => P.part a (e.val.symm w)) z v) -
          P.part a (e.val.symm z) * leviForm (fun w => P.part a (e.val.symm w)) z v ≤
        K * ‖v‖ ^ 2 := fun a =>
    exists_eventually_remainder_le (P.part_smooth a)
      (fun y => abs_le.mpr ⟨by linarith [P.part_nonneg a y], P.part_le_one a y⟩) e hz₀
  choose K hK0 hKz using hK
  have hKall := eventually_all.mpr hKz
  set Ks := ∑ a, K a with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun a _ => hK0 a
  have hKa : ∀ a, K a ≤ Ks := fun a =>
    Finset.single_le_sum (f := K) (fun b _ => hK0 b) (Finset.mem_univ a)
  -- the Kähler form
  obtain ⟨m, hm, hmz⟩ := exists_eventually_kahler_lower omega e hz₀
  -- holomorphy of the local generators
  have hG : ∀ j, ∀ᶠ z in 𝓝 z₀, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (G j) w := by
    intro j
    have hd : e.val.symm z₀ ∈ P.dom j.1.1 := by
      rw [hsym]; exact P.part_tsupport _ j.1.2
    exact (P.eventually_differentiableAt_gen_chart j.1.1 j.2 e hz₀ hd).eventually_nhds
  have hGall := eventually_all.mpr hG
  have htgt : ∀ᶠ z in 𝓝 z₀, z ∈ e.val.target := e.val.open_target.mem_nhds hz₀
  set cardT := (Fintype.card T : ℝ) with hcardT
  have hcardT0 : 0 ≤ cardT := Nat.cast_nonneg _
  refine ⟨2 * Ks * cardT * C / m + 1, by positivity, ?_⟩
  filter_upwards [hrep2, hCz, hKall, hmz, hGall, htgt] with z hzrep hzC hzK hzm hzG hzt
  refine ⟨hzt, fun s hs v => ?_⟩
  have hc2 : ∀ j, ContDiffAt ℝ 2 (c j) z := fun j =>
    ((P.part_smooth j.1.1 e).contDiffAt (e.val.open_target.mem_nhds hzt)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcongr : (fun w => Real.log (P.weight (e.val.symm w) + s)) =ᶠ[𝓝 z]
      fun w => Real.log (∑ j : J, c j w ^ 2 * Complex.normSq (G j w) + s) := by
    filter_upwards [hzrep] with w hw
    rw [hw]
  rw [GlobalTubeFunction.leviForm_congr_of_eventuallyEq hcongr v]
  have hbound := neg_le_leviForm_log_sum hs hc2 hzG v
  -- the bracket is at most `Ks ‖v‖²`
  have hbr : ∀ j : J, Complex.normSq (G j z) *
      (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v) ≤
        Complex.normSq (G j z) * (Ks * ‖v‖ ^ 2) := fun j =>
    mul_le_mul_of_nonneg_left ((hzK j.1.1 v).trans
      (mul_le_mul_of_nonneg_right (hKa _) (by positivity))) (Complex.normSq_nonneg _)
  have hsumG : ∑ j : J, Complex.normSq (G j z) ≤ cardT * (C * P.weight (e.val.symm z)) := by
    rw [Fintype.sum_sigma]
    calc ∑ a : T, ∑ i, Complex.normSq (G ⟨a, i⟩ z)
        = ∑ a : T, generatorNormSq (P.gen a.1) (e.val.symm z) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [generatorNormSq]
          exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _
      _ ≤ ∑ _a : T, C * P.weight (e.val.symm z) :=
          Finset.sum_le_sum fun a _ => hzC a.1 a.2
      _ = cardT * (C * P.weight (e.val.symm z)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hW : ∑ j : J, c j z ^ 2 * Complex.normSq (G j z) = P.weight (e.val.symm z) :=
    hzrep.self_of_nhds.symm
  have hU0 := P.weight_nonneg (e.val.symm z)
  set U := P.weight (e.val.symm z)
  have hSpos : 0 < U + s := by linarith
  rw [hW] at hbound
  have hnum : ∑ j : J, Complex.normSq (G j z) *
      (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v) ≤
        Ks * ‖v‖ ^ 2 * (cardT * (C * U)) := by
    calc _ ≤ ∑ j : J, Complex.normSq (G j z) * (Ks * ‖v‖ ^ 2) := Finset.sum_le_sum fun j _ => hbr j
      _ = Ks * ‖v‖ ^ 2 * ∑ j : J, Complex.normSq (G j z) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ Ks * ‖v‖ ^ 2 * (cardT * (C * U)) :=
          mul_le_mul_of_nonneg_left hsumG (by positivity)
  have hfrac : 2 * (∑ j : J, Complex.normSq (G j z) *
      (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) / (U + s) ≤
        2 * Ks * cardT * C * ‖v‖ ^ 2 := by
    rw [div_le_iff₀ hSpos]
    have hUle : U ≤ U + s := by linarith
    have h0 : 0 ≤ 2 * Ks * cardT * C * ‖v‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hUle h0]
  have hωv := hzm v
  have hω0 : 0 ≤ omega.form.val.coeff e z ![v, Complex.I • v] :=
    le_trans (by positivity) hωv
  have hv : ‖v‖ ^ 2 ≤ omega.form.val.coeff e z ![v, Complex.I • v] / m := by
    rw [le_div_iff₀ hm]; linarith
  have hfin : 2 * Ks * cardT * C * ‖v‖ ^ 2 ≤
      (2 * Ks * cardT * C / m + 1) * omega.form.val.coeff e z ![v, Complex.I • v] := by
    have h1 : 2 * Ks * cardT * C * ‖v‖ ^ 2 ≤
        2 * Ks * cardT * C * (omega.form.val.coeff e z ![v, Complex.I • v] / m) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    have h2 : 2 * Ks * cardT * C * (omega.form.val.coeff e z ![v, Complex.I • v] / m) =
        2 * Ks * cardT * C / m * omega.form.val.coeff e z ![v, Complex.I • v] := by ring
    nlinarith
  linarith

end ConcentrationPartition

/-! ### The global lower bound `ddᶜ log (U + s) ≥ -A ω` -/

namespace ConcentrationPartition

section Global

open ConcentrationPotentialLevi KahlerDomination ManifoldTubePositivity

variable {Y : Set M} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n Y ι)

/-- The line value of `ddᶜ log (U + s)` in a chart is the Levi form divided by `π`. -/
theorem ddc_log_weight_lineValue {s : ℝ} (hs : 0 < s) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (v : ComplexModel n) :
    (ddcClosedForm (fun y => Real.log (P.weight y + s)) (P.chartSmooth_log_weight hs)).val.coeff
        e z ![v, Complex.I • v] =
      leviForm (fun w => Real.log (P.weight (e.val.symm w) + s)) z v / Real.pi :=
  quad_ddcClosedForm_coeff (P.chartSmooth_log_weight hs) e hz v

/-- **dp04 2.1 (ii) on a compact manifold**: one `A > 0` with `ddᶜ log (U + s) + A ω ≥ 0` for
every `s > 0` (the source's `i∂∂̄ψ_ε ≥ -Aω`, `ψ_ε = ½ log (e^{2ψ} + ε²)`, `s = ε²`). -/
theorem exists_pos_isSemipositive_ddc_log_weight [CompactSpace M]
    (omega : PositiveClasses.KahlerBackground n M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℝ) (hs : 0 < s),
      (ddcClosedForm (fun y => Real.log (P.weight y + s)) (P.chartSmooth_log_weight hs) +
        A • omega.form).val.IsSemipositive := by
  classical
  have hloc : ∀ x : M, ∃ A : ℝ, ∃ V : Set (ComplexModel n), 0 < A ∧
      V ∈ 𝓝 ((complexChartAt (n := n) x).val x) ∧ V ⊆ (complexChartAt (n := n) x).val.target ∧
      ∀ z ∈ V, ∀ (s : ℝ) (hs : 0 < s), ∀ v : ComplexModel n,
        0 ≤ (ddcClosedForm (fun y => Real.log (P.weight y + s))
              (P.chartSmooth_log_weight hs)).val.coeff (complexChartAt (n := n) x) z
              ![v, Complex.I • v]
          + A * omega.form.val.coeff (complexChartAt (n := n) x) z ![v, Complex.I • v] := by
    intro x
    obtain ⟨A, hA, hev⟩ := P.exists_local_levi_bound omega x
    obtain ⟨V, hV, hVsub⟩ := Filter.eventually_iff_exists_mem.mp hev
    refine ⟨A / Real.pi, V, by positivity, hV, fun z hz => (hVsub z hz).1, ?_⟩
    intro z hz s hs v
    obtain ⟨hzt, hb⟩ := hVsub z hz
    rw [P.ddc_log_weight_lineValue hs _ hzt v]
    have h := hb s hs v
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, ← add_div]
    exact div_nonneg (by linarith) hpi.le
  choose A V hApos hVmem hVsub hVdom using hloc
  set U : M → Set M := fun x =>
    (complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹' V x with hU
  have hUmem : ∀ x : M, U x ∈ 𝓝 x := by
    intro x
    refine inter_mem ((complexChartAt (n := n) x).val.open_source.mem_nhds
      (mem_complexChartAt_source x)) ?_
    exact (complexChartAt (n := n) x).val.continuousAt (mem_complexChartAt_source x) (hVmem x)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hUmem x)
  have hsum : (0 : ℝ) ≤ ∑ x ∈ t, A x := Finset.sum_nonneg fun y _ => (hApos y).le
  refine ⟨1 + ∑ x ∈ t, A x, by linarith, fun s hs => ?_⟩
  intro f w hw v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hp : f.val.symm w ∈ f.val.source := f.val.map_target hw
  obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, f.val.symm w ∈ U x := by
    have := ht (mem_univ (f.val.symm w))
    simpa using this
  set e := complexChartAt (n := n) x with he
  have hsrc : f.val.symm w ∈ e.val.source := hxU.1
  have hzV : e.val (f.val.symm w) ∈ V x := hxU.2
  have hzt : e.val (f.val.symm w) ∈ e.val.target := hVsub x hzV
  have hwsrc : w ∈ (chartTransition f e).source := by
    rw [chartTransition]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨hw, hsrc⟩
  have hteq : chartTransition f e w = e.val (f.val.symm w) := rfl
  have hθt := lineValue_compatible (ddcClosedForm (fun y => Real.log (P.weight y + s))
    (P.chartSmooth_log_weight hs)).val f e hwsrc v
  have hωt := lineValue_compatible omega.form.val f e hwsrc v
  rw [hteq] at hθt hωt
  rw [hθt, hωt]
  set D := chartTransitionDerivative f e w v with hD
  have hmono : A x ≤ 1 + ∑ y ∈ t, A y :=
    le_trans (Finset.single_le_sum (fun y _ => (hApos y).le) hxt) (by linarith)
  have hωnn : 0 ≤ omega.form.val.coeff e (e.val (f.val.symm w)) ![D, Complex.I • D] :=
    lineValue_nonneg_of_isHermitian omega.isKahler.1 e hzt D
  have hdom := hVdom x _ hzV s hs D
  nlinarith [mul_le_mul_of_nonneg_right hmono hωnn]

/-- **The `s = 0` bound off the zero set** (for `log U` itself, TN3's pole potential): with the
same `A`, `ddᶜ log U + A ω ≥ 0` at every chart point where `U > 0` (as a pointwise Levi-form
inequality, since `log U` is smooth only there).  Obtained from the `s > 0` bound by letting
`s → 0⁺` in the explicit formula `L(log(F + s)) = L(F)/(F + s) - |∂F|²/(F + s)²`. -/
theorem exists_pos_levi_log_weight [CompactSpace M] (omega : PositiveClasses.KahlerBackground n M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      0 < P.weight (e.val.symm z) → ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (P.weight (e.val.symm w))) z v / Real.pi +
          A * omega.form.val.coeff e z ![v, Complex.I • v] := by
  obtain ⟨A, hA, hsemi⟩ := P.exists_pos_isSemipositive_ddc_log_weight omega
  refine ⟨A, hA, fun e z hz hpos v => ?_⟩
  set F : ComplexModel n → ℝ := fun w => P.weight (e.val.symm w) with hFdef
  have hF2 : ContDiffAt ℝ 2 F z :=
    ((P.chartSmooth_weight e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  set g : ℝ → ℝ := fun s => leviForm F z v / (F z + s) -
    (fderiv ℝ F z v ^ 2 + fderiv ℝ F z (Complex.I • v) ^ 2) / (4 * (F z + s) ^ 2) with hgdef
  have hlog : ∀ s : ℝ, 0 ≤ s →
      leviForm (fun w => Real.log (F w + s)) z v = g s := by
    intro s hs
    have hS : ContDiffAt ℝ 2 (fun w => F w + s) z := hF2.add contDiffAt_const
    have hSpos : 0 < F z + s := by linarith
    rw [ConcentrationPotentialLevi.leviForm_log_of_pos hS hSpos]
    have hL : leviForm (fun w => F w + s) z v = leviForm F z v := by
      rw [show (fun w => F w + s) = F + fun _ => s from rfl, leviForm_add hF2 contDiffAt_const,
        leviForm_const, add_zero]
    have hd : ∀ a, fderiv ℝ (fun w => F w + s) z a = fderiv ℝ F z a := fun a => by
      rw [fderiv_add_const]
    rw [hL, hd, hd]
  -- the bound for every `s > 0`
  have hpos' : ∀ s : ℝ, 0 < s → 0 ≤ g s / Real.pi + A * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro s hs
    have h := hsemi s hs e z hz v
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
    rw [P.ddc_log_weight_lineValue hs e hz v] at h
    rwa [← hlog s hs.le]
  -- continuity of `g` at `0`
  have hcont : ContinuousAt g 0 := by
    have hden : F z + 0 ≠ 0 := by simp only [add_zero]; exact hpos.ne'
    have h1 : ContinuousAt (fun s : ℝ => F z + s) 0 := continuousAt_const.add continuousAt_id
    refine (continuousAt_const.div h1 hden).sub (continuousAt_const.div
      (continuousAt_const.mul (h1.pow 2)) ?_)
    simp only [add_zero]; positivity
  have htend : Tendsto (fun s => g s / Real.pi + A * omega.form.val.coeff e z ![v, Complex.I • v])
      (𝓝[>] 0) (𝓝 (g 0 / Real.pi + A * omega.form.val.coeff e z ![v, Complex.I • v])) :=
    (((hcont.tendsto.div_const _).add_const _)).mono_left nhdsWithin_le_nhds
  have hlim := ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun s hs => hpos' s hs)
  have h0 : leviForm (fun w => Real.log (P.weight (e.val.symm w))) z v = g 0 := by
    have := hlog 0 le_rfl
    simpa only [add_zero] using this
  rw [h0]
  exact hlim

end Global

end ConcentrationPartition

/-! ### The potentials `f_ε`, the forms `ω_ε` and the tubes `V_ε` -/

namespace ConcentrationPartition

section Potentials

open ConcentrationPotentialLevi ManifoldTubePositivity KahlerDomination

variable {Y : Set M} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n Y ι)

/-- `f_ε = log (U + ε²) / (2A)`: dp04's `ψ_ε / A` (`ψ_ε = ½ log (e^{2ψ} + ε²)`), so that
`ω_ε = ω + ddᶜ f_ε` is the source's `ω + (2A)⁻¹ i∂∂̄ψ_ε` up to the normalisation of `ddᶜ`. -/
def potential (A ε : ℝ) (y : M) : ℝ := Real.log (P.weight y + ε ^ 2) / (2 * A)

theorem chartSmooth_potential (A : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ChartSmooth (n := n) (P.potential A ε) := fun e =>
  (P.chartSmooth_log_weight (pow_pos (abs_pos.mpr hε) 2 |>.trans_eq (sq_abs ε)) e).div_const _

/-- **`ω_ε ≥ ω/2`** (dp04 2.1 (iii), first sentence): if `ddᶜ log (U + s) + A ω ≥ 0` for every
`s > 0`, then `½ ω + ddᶜ f_ε ≥ 0`. -/
theorem isSemipositive_half_add_ddc_potential (omega : PositiveClasses.KahlerBackground n M)
    {A : ℝ} (hA : 0 < A)
    (hsemi : ∀ (s : ℝ) (hs : 0 < s),
      (ddcClosedForm (fun y => Real.log (P.weight y + s)) (P.chartSmooth_log_weight hs) +
        A • omega.form).val.IsSemipositive)
    {ε : ℝ} (hε : ε ≠ 0) :
    ((1 / 2 : ℝ) • omega.form +
      ddcClosedForm (P.potential A ε) (P.chartSmooth_potential A hε)).val.IsSemipositive := by
  intro e z hz v
  have hs : 0 < ε ^ 2 := pow_pos (abs_pos.mpr hε) 2 |>.trans_eq (sq_abs ε)
  have h := hsemi (ε ^ 2) hs e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h ⊢
  have hlog : ContDiffAt ℝ 2 (fun w => Real.log (P.weight (e.val.symm w) + ε ^ 2)) z :=
    ((P.chartSmooth_log_weight hs e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h1 := quad_ddcClosedForm_coeff (P.chartSmooth_potential A hε) e hz v
  have h2 := quad_ddcClosedForm_coeff (P.chartSmooth_log_weight hs) e hz v
  simp only [PositivityPerturbation.quad] at h1 h2
  rw [h1]
  rw [h2] at h
  have hfun : (fun w => P.potential A ε (e.val.symm w)) =
      (1 / (2 * A)) • fun w => Real.log (P.weight (e.val.symm w) + ε ^ 2) := by
    funext w; simp only [potential, Pi.smul_apply, smul_eq_mul]; ring
  rw [hfun, leviForm_smul hlog]
  have hω := lineValue_nonneg_of_isHermitian omega.isKahler.1 e hz v
  have hpi := Real.pi_pos
  have key : 1 / 2 * omega.form.val.coeff e z ![v, Complex.I • v] +
      1 / (2 * A) * leviForm (fun w => Real.log (P.weight (e.val.symm w) + ε ^ 2)) z v / Real.pi =
      1 / (2 * A) * (leviForm (fun w => Real.log (P.weight (e.val.symm w) + ε ^ 2)) z v /
        Real.pi + A * omega.form.val.coeff e z ![v, Complex.I • v]) := by
    field_simp
    ring
  rw [key]
  exact mul_nonneg (by positivity) h

theorem continuous_weight : Continuous P.weight := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (n := n) (h := P.weight)
    isOpen_univ (fun e => by simpa using P.chartSmooth_weight e) (mem_univ x)

/-- The tube `V_ε = {U < ε²}` (dp04: `{ψ < log ε}`). -/
def tube (ε : ℝ) : Set M := {y | P.weight y < ε ^ 2}

theorem isOpen_tube (ε : ℝ) : IsOpen (P.tube ε) :=
  isOpen_lt P.continuous_weight continuous_const

theorem tube_mono {ε ε' : ℝ} (hε : 0 < ε) (h : ε ≤ ε') : P.tube ε ⊆ P.tube ε' := fun _ hy =>
  lt_of_lt_of_le hy (pow_le_pow_left₀ hε.le h 2)

/-- Off `Y` the weight is positive: the unit germ lies in `𝓘_Y`, hence in the span of the
generators of any piece through the point, so some generator does not vanish there. -/
theorem weight_pos_of_notMem (hY : IsClosed Y) {y : M} (hy : y ∉ Y) : 0 < P.weight y := by
  obtain ⟨a, ha⟩ := P.exists_part_pos y
  have hya : y ∈ P.dom a := P.part_tsupport a (subset_tsupport _ ha.ne')
  have hone : (vanishingIdeal (n := n) Y).mem y (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1, ?_⟩
    filter_upwards [hY.isOpen_compl.mem_nhds hy] with y' hy' hY'
    exact absurd hY' hy'
  obtain ⟨-, K, s, c, hs, -, hsum⟩ := (P.gen_spec a y hya _).mp hone
  have hG : 0 < generatorNormSq (P.gen a) y := by
    by_contra hle
    push Not at hle
    have hz : ∀ j, P.gen a j y = 0 := by
      intro j
      have h1 := norm_sq_le_generatorNormSq (P.gen a) y j
      have h2 : ‖P.gen a j y‖ ^ 2 = 0 := le_antisymm (h1.trans hle) (sq_nonneg _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    have h1 : (1 : ℂ) = ∑ i, c i y * s i y := hsum.self_of_nhds
    have h0 : ∑ i, c i y * s i y = 0 := Finset.sum_eq_zero fun i _ => by
      obtain ⟨j, hj⟩ := hs i
      rw [← hj, hz j, mul_zero]
    rw [h0] at h1
    exact one_ne_zero h1
  have hterm : P.part a y ^ 2 * P.genNormSq a y ≤ P.weight y :=
    Finset.single_le_sum (f := fun a => P.part a y ^ 2 * P.genNormSq a y)
      (fun a _ => mul_nonneg (sq_nonneg _) (P.genNormSq_nonneg a y)) (Finset.mem_univ a)
  have hgen : P.genNormSq a y = generatorNormSq (P.gen a) y := Set.indicator_of_mem hya _
  rw [hgen] at hterm
  exact lt_of_lt_of_le (mul_pos (pow_pos ha 2) hG) hterm

theorem weight_eq_zero_of_mem {y : M} (hy : y ∈ Y) : P.weight y = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hya : y ∈ P.dom a
  · have hgen : P.genNormSq a y = generatorNormSq (P.gen a) y := Set.indicator_of_mem hya _
    rw [hgen]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
    have hmem : (vanishingIdeal (n := n) Y).mem y (P.gen a j) := by
      refine (P.gen_spec a y hya _).mpr ?_
      refine isInSpanAt_of_eq_mul ⟨j, rfl⟩ ?_ (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)
      filter_upwards [(P.isOpen_dom a).mem_nhds hya] with z hz
      exact (P.gen_mdifferentiableOn a j z hz).mdifferentiableAt ((P.isOpen_dom a).mem_nhds hz)
    rw [hmem.2.self_of_nhds hy]
    simp
  · have hgen : P.genNormSq a y = 0 := Set.indicator_of_notMem hya _
    rw [hgen, mul_zero]

/-- dp04 2.1: the tubes shrink to `Y`. -/
theorem iInter_closure_tube_subset (hY : IsClosed Y) :
    (⋂ ε ∈ Set.Ioc (0 : ℝ) 1, closure (P.tube ε)) ⊆ Y := by
  intro y hy
  by_contra hyY
  have hpos := P.weight_pos_of_notMem hY hyY
  obtain ⟨ε, hε0, hεw⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 < P.weight y := by
    refine ⟨min 1 (Real.sqrt (P.weight y) / 2), by positivity, ?_⟩
    have h1 : min 1 (Real.sqrt (P.weight y) / 2) ≤ Real.sqrt (P.weight y) / 2 := min_le_right _ _
    have h2 : 0 ≤ min 1 (Real.sqrt (P.weight y) / 2) := by positivity
    have hsq : (Real.sqrt (P.weight y)) ^ 2 = P.weight y := Real.sq_sqrt hpos.le
    have hs0 : 0 < Real.sqrt (P.weight y) := Real.sqrt_pos.mpr hpos
    nlinarith [pow_le_pow_left₀ h2 h1 2]
  have hε1 : min ε 1 ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min hε0 one_pos, min_le_right _ _⟩
  have hcl : y ∈ closure (P.tube (min ε 1)) := mem_iInter₂.mp hy _ hε1
  have hsub : closure (P.tube (min ε 1)) ⊆ {y | P.weight y ≤ (min ε 1) ^ 2} :=
    closure_minimal (fun y' hy' => show P.weight y' ≤ (min ε 1) ^ 2 from le_of_lt hy')
      (isClosed_le P.continuous_weight continuous_const)
  have := hsub hcl
  have hmin : (min ε 1) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (lt_min hε0 one_pos).le (min_le_left _ _) 2
  simp only [mem_ofPred_eq] at this
  linarith

end Potentials

end ConcentrationPartition

/-! ### A partition adapted to a point of `Y` -/

section Existence

open BlowupFlatCoordinates Hironaka.BlowupSequences

/-- The flat normal coordinates of a flattening, padded by `0` in the tangential slots. -/
def flatGen {x : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (i : Fin n) : M → ℂ :=
  if k ≤ i.1 then flatCoord Φ i else fun _ => 0

/-- **A concentration partition adapted to a point** `x ∈ Y`: the flattening `Φ` at `x` given by
`RegularAtDim Y x k`, and a partition whose weight is exactly `∑_{i ≥ k} |ζ_i|²` (the normal flat
coordinates) near `x`. -/
theorem exists_adapted [CompactSpace M] {Y : Set M} (hY : IsClosedSubmanifold n Y) {x : M}
    {k : ℕ} (hx : RegularAtDim (n := n) Y x k) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ Y ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ConcentrationPartition n Y ι),
        ∀ᶠ y in 𝓝 x, P.weight y = ∑ i : Fin n, ‖flatGen Φ k i y‖ ^ 2 := by
  classical
  obtain ⟨-, -, Φ, hΦsrc, hΦ0, hflat⟩ := hx
  refine ⟨Φ, hΦsrc, hΦ0, hflat, ?_⟩
  -- the special piece: the flattening at `x`
  set D₀ := flatDomain Φ with hD₀
  have hD₀open : IsOpen D₀ := isOpen_flatDomain Φ
  have hxD₀ : x ∈ D₀ := mem_flatDomain_self Φ
  have hg₀ : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (flatGen Φ k i) D₀ := by
    intro i
    by_cases hik : k ≤ i.1
    · simp only [flatGen, hik, if_true]
      exact fun z hz => (holomorphicAt_flatCoord Φ i hz).self_of_nhds.mdifferentiableWithinAt
    · simp only [flatGen, hik, if_false]
      exact mdifferentiableOn_const
  have hspec₀ : ∀ y ∈ D₀, ∀ f, (vanishingIdeal (n := n) Y).mem y f ↔
      IsInSpanAt (n := n) (· ∈ range (flatGen Φ k)) y f := by
    intro y hy f
    constructor
    · intro hf
      obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hf
      refine ⟨hf.1, n, flatGen Φ k, b, fun i => ⟨i, rfl⟩, hbhol, ?_⟩
      filter_upwards [hbeq] with y' h1
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hik : k ≤ i.1
      · simp [flatGen, hik]
      · rw [hb0 i (Nat.lt_of_not_le hik)]
        simp
    · refine VanishingIdealCoherent.mem_vanishingIdeal_of_isInSpanAt fun i => ?_
      by_cases hik : k ≤ i.1
      · simpa only [flatGen, hik, if_true] using flatCoord_mem_vanishingIdeal Φ hflat hik hy
      · simp only [flatGen, hik, if_false]
        exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩
  -- the bump at `x`
  obtain ⟨β, hβs, hβ0, hβ1, hβsupp, -, hβx⟩ :=
    exists_chartSmooth_bump (n := n) x ⟨D₀, hD₀open⟩ hxD₀
  -- a partition subordinate to the coherence cover of `𝓘_Y`
  choose S hS hmem N g hgd hspec using VanishingIdealCoherent.isCoherent_vanishingIdeal hY
  obtain ⟨m, χ, idx, hχsm, hχnn, hχsupp, -, hχsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) (fun x : M => ⟨S x, hS x⟩) fun x => ⟨x, hmem x⟩
  let P : ConcentrationPartition n Y (Option (Fin m)) :=
    { dom := fun a => match a with
        | none => D₀
        | some b => S (idx b)
      isOpen_dom := fun a => match a with
        | none => hD₀open
        | some b => hS (idx b)
      arity := fun a => match a with
        | none => n
        | some b => N (idx b)
      gen := fun a => match a with
        | none => flatGen Φ k
        | some b => g (idx b)
      gen_mdifferentiableOn := fun a => match a with
        | none => hg₀
        | some b => hgd (idx b)
      gen_spec := fun a => match a with
        | none => hspec₀
        | some b => hspec (idx b)
      part := fun a => match a with
        | none => β
        | some b => fun y => (1 - β y) * χ b y
      part_smooth := fun a => match a with
        | none => hβs
        | some b => fun e => (contDiffOn_const.sub (hβs e)).mul (hχsm b e)
      part_nonneg := fun a => match a with
        | none => hβ0
        | some b => fun y => mul_nonneg (by linarith [hβ1 y]) (hχnn b y)
      part_tsupport := fun a => match a with
        | none => hβsupp
        | some b => (tsupport_mul_subset_right (f := fun y => 1 - β y) (g := χ b)).trans
            (hχsupp b)
      part_sum := fun y => by
        rw [Fintype.sum_option]
        simp only
        rw [← Finset.mul_sum, hχsum y]
        ring }
  refine ⟨Option (Fin m), inferInstance, P, ?_⟩
  filter_upwards [hβx, hD₀open.mem_nhds hxD₀] with y hy hyD
  have hsome : ∀ b, P.part (some b) y = 0 := fun b => by
    change (1 - β y) * χ b y = 0
    rw [hy]; ring
  rw [ConcentrationPartition.weight, Fintype.sum_option]
  simp only [hsome]
  change β y ^ 2 * (D₀.indicator (generatorNormSq (flatGen Φ k)) y) + _ = _
  rw [hy, Set.indicator_of_mem hyD]
  simp [generatorNormSq]

/-- A concentration partition exists as soon as the vanishing ideal of `Y` is coherent (e.g. `Y`
a closed submanifold, `VanishingIdealCoherent.isCoherent_vanishingIdeal`, or a closed analytic
set by Cartan's theorem); no submanifold structure is used. -/
theorem exists_of_isCoherent [CompactSpace M] {Y : Set M}
    (h : (vanishingIdeal (n := n) Y).IsCoherent) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (ConcentrationPartition n Y ι) := by
  classical
  choose S hS hmem N g hgd hspec using h
  obtain ⟨m, χ, idx, hχsm, hχnn, hχsupp, -, hχsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) (fun x : M => ⟨S x, hS x⟩) fun x => ⟨x, hmem x⟩
  let P : ConcentrationPartition n Y (Fin m) :=
    { dom := fun b => S (idx b)
      isOpen_dom := fun b => hS (idx b)
      arity := fun b => N (idx b)
      gen := fun b => g (idx b)
      gen_mdifferentiableOn := fun b => hgd (idx b)
      gen_spec := fun b => hspec (idx b)
      part := χ
      part_smooth := hχsm
      part_nonneg := hχnn
      part_tsupport := hχsupp
      part_sum := hχsum }
  exact ⟨Fin m, inferInstance, ⟨P⟩⟩

end Existence

end

end Hironaka.SubmanifoldConcentrationPotential
