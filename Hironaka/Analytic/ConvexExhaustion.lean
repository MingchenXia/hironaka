import Mathlib.Analysis.Convex.Continuous
import Hironaka.Analytic.PotentialTheory.CircleSubmean
import Hironaka.Analytic.OhsawaTakegoshiInterface

set_option autoImplicit false

/-!
# Convex open sets: bounded exhaustions and convex exhaustion weights

Two constructions used to pass from the Ohsawa--Takegoshi theorem on bounded convex domains
with regular weights to the general statement.

1. Every open convex set `Ω` of a finite-dimensional real normed space is the increasing
   union of bounded open convex sets `K k` with `closure (K k) ⊆ K (k + 1)`.  One takes
   `a + t_k • (Ω ∩ B(a, k + 1) - a)` for a point `a ∈ Ω` and `t_k ↑ 1`.
2. A continuous convex function on an open convex subset of `ℂⁿ` is plurisubharmonic.
   Given a proper open convex set `Ω ⊆ ℂ^{m+1}` and a continuous function `f` on the
   hyperplane slice of `Ω`, there is a plurisubharmonic weight `ψ = χ ∘ ρ` on `Ω`, where
   `ρ = ‖z‖ + max (-log d(z, ∁Ω)) 0` is a convex exhaustion (the boundary distance is
   concave on a convex set) and `χ` is convex and increasing, such that `∫ |f|² e^{-cψ}`
   over the slice is finite.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



/-- A bounded convex exhaustion of an open convex set. -/
theorem exists_bounded_convex_exhaustion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) :
    ∃ K : ℕ → Set E, (∀ k, IsOpen (K k)) ∧ (∀ k, Convex ℝ (K k)) ∧
      (∀ k, Bornology.IsBounded (K k)) ∧ (∀ k, closure (K k) ⊆ K (k + 1)) ∧
      (∀ k, K k ⊆ Ω) ∧ (⋃ k, K k) = Ω := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨fun _ => ∅, fun _ => isOpen_empty, fun _ => convex_empty, fun _ =>
      Bornology.isBounded_empty, fun _ => by simp, fun _ => le_rfl, by simp⟩
  set s : ℕ → ℝ := fun k => ((k : ℝ) + 2) / ((k : ℝ) + 1) with hs
  have hs1 : ∀ k, 1 < s k := fun k => by
    rw [hs, one_lt_div (by positivity)]; linarith
  set g : ℕ → E → E := fun k y => a + s k • (y - a) with hg
  have hgc : ∀ k, Continuous (g k) := fun k => by fun_prop
  have hsub : ∀ k, g k ⁻¹' (Ω ∩ ball a ((k : ℝ) + 1)) ⊆ Ω := fun k y hy => by
    have hy' : y = a + (s k)⁻¹ • (g k y - a) := by
      simp only [hg, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ (zero_lt_one.trans (hs1 k)).ne', one_smul, add_sub_cancel]
    rw [hy']
    exact hΩc.add_smul_sub_mem ha hy.1 ⟨by have := hs1 k; positivity,
      inv_le_one_of_one_le₀ (hs1 k).le⟩
  refine ⟨fun k => g k ⁻¹' (Ω ∩ ball a ((k : ℝ) + 1)), fun k =>
    (hΩo.inter isOpen_ball).preimage (hgc k), fun k => ?_, fun k => ?_, fun k => ?_,
    hsub, ?_⟩
  · intro x hx y hy p q hp hq hpq
    have : g k (p • x + q • y) = p • g k x + q • g k y := by
      obtain rfl : q = 1 - p := by linarith
      simp only [hg]; module
    simp only [mem_preimage, this] at hx hy ⊢
    exact (hΩc.inter (convex_ball a _)) hx hy hp hq hpq
  · refine (isBounded_ball (x := a) (r := (k : ℝ) + 1)).subset fun y hy => ?_
    have h := hy.2
    simp only [hg, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans (hs1 k))] at h ⊢
    nlinarith [norm_nonneg (y - a), hs1 k]
  · intro y hy
    obtain ⟨hx1, hx2⟩ := (closure_inter_subset_inter_closure _ _)
      ((hgc k).closure_preimage_subset _ hy)
    rw [closure_ball _ (by positivity)] at hx2
    set r : ℝ := s (k + 1) / s k with hr
    have hr0 : 0 < r := div_pos (zero_lt_one.trans (hs1 _)) (zero_lt_one.trans (hs1 _))
    have hr1 : r < 1 := by
      rw [hr, hs, div_lt_one (by positivity)]
      push_cast
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hgr : g (k + 1) y = g k y + (1 - r) • (a - g k y) := by
      have : s (k + 1) = r * s k := by
        rw [hr, div_mul_cancel₀ _ (zero_lt_one.trans (hs1 _)).ne']
      simp only [hg, this]; module
    refine ⟨?_, ?_⟩
    · have h := hΩc.add_smul_sub_mem_interior' hx1 (hΩo.interior_eq.symm ▸ ha)
        (t := 1 - r) ⟨by linarith, by linarith⟩
      rwa [hΩo.interior_eq, ← hgr] at h
    · rw [hgr, mem_ball, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hx2
      have : g k y + (1 - r) • (a - g k y) - a = r • (g k y - a) := by module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      push_cast
      nlinarith [norm_nonneg (g k y - a)]
  · refine subset_antisymm (iUnion_subset hsub) fun z hz => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩo z hz
    obtain ⟨k, hk⟩ := exists_nat_gt (max (‖z - a‖ / ε) (2 * ‖z - a‖))
    have hk1 := (le_max_left _ _).trans_lt hk
    have hk2 := (le_max_right _ _).trans_lt hk
    rw [div_lt_iff₀ hε] at hk1
    have hsk : s k - 1 = 1 / ((k : ℝ) + 1) := by
      rw [hs]; field_simp; ring
    have hsk2 : s k ≤ 2 := by
      rw [hs, div_le_iff₀ (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    refine mem_iUnion.mpr ⟨k, hball ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      have : g k z - z = (s k - 1) • (z - a) := by simp only [hg]; module
      rw [this, norm_smul, hsk, Real.norm_eq_abs, abs_of_pos (by positivity),
        one_div, inv_mul_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (z - a)]
    · rw [mem_ball, dist_eq_norm]
      simp only [hg, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (zero_lt_one.trans (hs1 k))]
      nlinarith [norm_nonneg (z - a)]

/-- A real function whose circle parametrization is continuous and which lies above the
center value on average over antipodal pairs satisfies the circle submean inequality. -/
theorem le_circleAverage_of_antipodal {g : ℂ → ℝ} {r a : ℝ}
    (hg : Continuous fun t : ℝ => g (circleMap 0 r t))
    (h : ∀ z ∈ sphere (0 : ℂ) |r|, 2 * a ≤ g z + g (-z)) :
    a ≤ Real.circleAverage g 0 r := by
  have hpi : ∀ t, circleMap 0 r (t + Real.pi) = -circleMap 0 r t := fun t => by
    simp [circleMap, add_mul, Complex.exp_add]
  have h2 : 2 * Real.circleAverage g 0 r =
      (2 * Real.pi)⁻¹ * ∫ t in 0..2 * Real.pi,
        (g (circleMap 0 r t) + g (circleMap 0 r (t + Real.pi))) := by
    have hg' : Continuous fun t : ℝ => g (circleMap 0 r (t + Real.pi)) :=
      hg.comp (continuous_add_const _)
    rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hg'.intervalIntegrable _ _),
      mul_add, two_mul]
    congr 1
    rw [Real.circleAverage_eq_integral_add Real.pi, smul_eq_mul]
  have hle : ∫ t in 0..2 * Real.pi, 2 * a ≤ ∫ t in 0..2 * Real.pi,
      (g (circleMap 0 r t) + g (circleMap 0 r (t + Real.pi))) := by
    refine intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
      ((hg.add (hg.comp (continuous_add_const _))).intervalIntegrable _ _) fun t _ => ?_
    rw [hpi]
    exact h _ (circleMap_mem_sphere' 0 r t)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  have hp : 0 < 2 * Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hp.le)
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] at this
  linarith

/-- A continuous convex function on an open convex set of `ℂⁿ` is plurisubharmonic. -/
theorem plurisubharmonicOn_of_convexOn {n : ℕ} {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {u : ComplexModel n → ℝ} (hu : ConvexOn ℝ Ω u) (hcont : ContinuousOn u Ω) :
    PlurisubharmonicOn (fun z => (u z : EReal)) Ω := by
  intro x hx
  refine ⟨Ω, hΩ, hx, fun _ _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp_continuousOn hcont).upperSemicontinuousOn, ?_⟩
  intro y v r hr hD C hC
  have hmem : ∀ z ∈ closedBall (0 : ℂ) r, y + z • v ∈ Ω := fun z hz => hD ⟨z, hz, rfl⟩
  have hcirc : Continuous (fun t : ℝ => u (y + circleMap 0 r t • v)) :=
    hcont.comp_continuous (by fun_prop) fun t =>
      hD (circle_mem_affineClosedDisc y v hr.le t)
  apply (circleDeficit_coe_le_iff y v r C (hcirc.intervalIntegrable _ _)
    (fun t => EReal.coe_le_coe_iff.mp (hC _ (circle_mem_affineClosedDisc y v hr.le t)))
    (EReal.coe_le_coe_iff.mp (hC y (center_mem_affineClosedDisc y v hr.le)))).mpr
  refine le_circleAverage_of_antipodal hcirc fun z hz => ?_
  have hz' : z ∈ closedBall (0 : ℂ) r := by
    rw [abs_of_pos hr] at hz; exact sphere_subset_closedBall hz
  have hz'' : -z ∈ closedBall (0 : ℂ) r := by simpa using hz'
  have := hu.2 (hmem z hz') (hmem (-z) hz'') (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (y + z • v) + (1 / 2 : ℝ) • (y + (-z) • v) = y := by
    rw [neg_smul, ← smul_add]; module
  rw [hmid, smul_eq_mul, smul_eq_mul] at this
  linarith

theorem norm_hyperplaneEmbedding (m : ℕ) (w : ComplexModel m) :
    ‖hyperplaneEmbedding m w‖ = ‖w‖ := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]

theorem continuous_hyperplaneEmbedding (m : ℕ) : Continuous (hyperplaneEmbedding m) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  induction i using Fin.lastCases with
  | last => simpa using continuous_const
  | cast i => simpa using (PiLp.continuous_apply 2 _ i)

/-- The distance to the complement of a convex set is concave on the set. -/
theorem concaveOn_infDist_compl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩc : Convex ℝ Ω) (hΩ : Ωᶜ.Nonempty) :
    ConcaveOn ℝ Ω (fun z => infDist z Ωᶜ) := by
  refine ⟨hΩc, fun x hx y hy a b ha hb hab => ?_⟩
  have hmem : ∀ p ∈ Ω, ∀ e : E, ‖e‖ < infDist p Ωᶜ ∨ e = 0 → p + e ∈ Ω := by
    rintro p hp e (he | rfl)
    · exact ball_infDist_compl_subset (by rwa [mem_ball, dist_eq_norm, add_sub_cancel_left])
    · simpa using hp
  simp only [smul_eq_mul]
  refine (le_infDist hΩ).mpr fun q hq => le_of_not_gt fun hlt => hq ?_
  set dx := infDist x Ωᶜ
  set dy := infDist y Ωᶜ
  set p := a • x + b • y
  have hs : 0 < a * dx + b * dy := (dist_nonneg).trans_lt hlt
  set e := q - p
  have he : ‖e‖ < a * dx + b * dy := by rwa [dist_comm, dist_eq_norm] at hlt
  have hq' : q =
      a • (x + (dx / (a * dx + b * dy)) • e) + b • (y + (dy / (a * dx + b * dy)) • e) := by
    have : a * (dx / (a * dx + b * dy)) + b * (dy / (a * dx + b * dy)) = 1 := by
      field_simp
    simp only [smul_add, smul_smul, e, p]
    rw [add_add_add_comm, ← add_smul, this, one_smul]
    abel
  have key : ∀ z ∈ Ω, 0 ≤ infDist z Ωᶜ →
      z + (infDist z Ωᶜ / (a * dx + b * dy)) • e ∈ Ω := by
    intro z hz hdz
    refine hmem z hz _ ?_
    rcases hdz.eq_or_lt with h0 | hpos
    · right; rw [← h0, zero_div, zero_smul]
    · left
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_eq_mul_div,
        div_lt_iff₀ hs]
      exact mul_lt_mul_of_pos_left he hpos
  rw [hq']
  exact hΩc (key x hx infDist_nonneg) (key y hy infDist_nonneg) ha hb hab

/-- For every sequence there is a convex nondecreasing function on `ℝ` dominating it at the
integers shifted by one. -/
theorem exists_convexOn_monotone_ge (β : ℕ → ℝ) :
    ∃ χ : ℝ → ℝ, ConvexOn ℝ univ χ ∧ Monotone χ ∧ ∀ n : ℕ, β n ≤ χ ((n : ℝ) - 1) := by
  set F : ℝ → ℕ → ℝ := fun t k => max (β k) 0 * max (t + 2 - k) 0 with hF
  have hsum : ∀ t, Summable (F t) := fun t => by
    refine summable_of_ne_finset_zero (s := Finset.range (⌈t⌉₊ + 2)) fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    have : t + 2 - k ≤ 0 := by
      have := Nat.le_ceil t
      have hk' : ((⌈t⌉₊ + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at hk'
      linarith
    simp [hF, max_eq_right this]
  have hFnn : ∀ t k, 0 ≤ F t k := fun t k => by positivity
  refine ⟨fun t => ∑' k, F t k, ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩,
    fun x y hxy => (hsum x).tsum_le_tsum (fun k => ?_) (hsum y), fun n => ?_⟩
  · simp only [smul_eq_mul]
    rw [← tsum_mul_left, ← tsum_mul_left, ← ((hsum x).mul_left a).tsum_add ((hsum y).mul_left b)]
    refine (hsum _).tsum_le_tsum (fun k => ?_) (((hsum x).mul_left a).add ((hsum y).mul_left b))
    simp only [hF]
    have h1 : max (a * x + b * y + 2 - k) 0 ≤ a * max (x + 2 - k) 0 + b * max (y + 2 - k) 0 := by
      refine max_le ?_ (by positivity)
      have h2 : a * x + b * y + 2 - k = a * (x + 2 - k) + b * (y + 2 - k) := by
        obtain rfl : b = 1 - a := by linarith
        ring
      rw [h2]
      gcongr <;> exact le_max_left _ _
    have := mul_le_mul_of_nonneg_left h1 (le_max_right (β k) 0)
    nlinarith
  · simp only [hF]
    gcongr
  · refine (le_max_left _ 0).trans ?_
    refine le_of_eq_of_le ?_ ((hsum _).le_tsum n fun j _ => hFnn _ j)
    have : (n : ℝ) - 1 + 2 - n = 1 := by ring
    simp [hF, this]

/-- The convex exhaustion `‖z‖ + max (-log d(z, ∁Ω)) 0` of a proper open convex set. -/
theorem convexOn_norm_add_max_neg_log_infDist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω : Set E} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩ : Ωᶜ.Nonempty) :
    ConvexOn ℝ Ω (fun z => ‖z‖ + max (-Real.log (infDist z Ωᶜ)) 0) := by
  have hpos : ∀ z ∈ Ω, 0 < infDist z Ωᶜ := fun z hz =>
    (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩ).mp fun h => h hz
  have hlog : ConvexOn ℝ Ω (fun z => -Real.log (infDist z Ωᶜ)) := by
    refine ⟨hΩc, fun x hx y hy a b ha hb hab => ?_⟩
    have hd := (concaveOn_infDist_compl hΩc hΩ).2 hx hy ha hb hab
    have hl := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.mpr (hpos x hx))
      (mem_Ioi.mpr (hpos y hy)) ha hb hab
    simp only [smul_eq_mul] at hd hl ⊢
    have hs : 0 < a * infDist x Ωᶜ + b * infDist y Ωᶜ := by
      rcases ha.eq_or_lt with rfl | ha'
      · obtain rfl : b = 1 := by linarith
        simpa using hpos y hy
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hpos x hx)) (mul_nonneg hb infDist_nonneg)
    have := Real.log_le_log hs hd
    linarith
  exact (convexOn_norm hΩc).add (hlog.sup (convexOn_const 0 hΩc))

/-- An exhaustion weight making a continuous function on the hyperplane slice of a proper
open convex set weighted-`L²`. -/
theorem exists_plurisubharmonic_weight_lintegral_lt_top {m : ℕ}
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    {Ω : Set (ComplexModel (m + 1))} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩ : Ω ≠ univ)
    {c : ℝ} (hc : 0 < c) {f : ComplexModel m → ℂ}
    (hf : ContinuousOn f (hyperplaneEmbedding m ⁻¹' Ω)) :
    ∃ ψ : ComplexModel (m + 1) → EReal, PlurisubharmonicOn ψ Ω ∧
      (∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
        multiplierDensity (fun w => ψ (hyperplaneEmbedding m w)) c f w) < ⊤ := by
  have hne : Ωᶜ.Nonempty := nonempty_compl.mpr hΩ
  set ι := hyperplaneEmbedding m with hι_def
  have hι : Continuous ι := continuous_hyperplaneEmbedding m
  set d : ComplexModel (m + 1) → ℝ := fun z => infDist z Ωᶜ with hd
  have hdpos : ∀ z ∈ Ω, 0 < d z := fun z hz =>
    (hΩo.isClosed_compl.notMem_iff_infDist_pos hne).mp fun h => h hz
  set ρ : ComplexModel (m + 1) → ℝ := fun z => ‖z‖ + max (-Real.log (d z)) 0 with hρ
  have hρc : ConvexOn ℝ Ω ρ := convexOn_norm_add_max_neg_log_infDist hΩo hΩc hne
  set S : ℕ → Set (ComplexModel m) :=
    fun j => {w | ‖w‖ ≤ j ∧ Real.exp (-(j : ℝ)) ≤ d (ι w)} with hS
  have hSc : ∀ j, IsCompact (S j) := fun j => by
    refine Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const ((continuous_infDist_pt _).comp hι)))
      ((isBounded_closedBall (x := 0) (r := (j : ℝ))).subset fun w hw => ?_)
    simpa using hw.1
  have hSsub : ∀ j, S j ⊆ ι ⁻¹' Ω := fun j w hw => by
    have := (hΩo.isClosed_compl.notMem_iff_infDist_pos hne (x := ι w)).mpr
      ((Real.exp_pos _).trans_le hw.2)
    simpa using this
  have hM : ∀ j, ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ S j, ‖f w‖ ^ 2 ≤ M := fun j => by
    obtain ⟨C, hC⟩ := (hSc j).exists_bound_of_continuousOn (hf.mono (hSsub j))
    exact ⟨C ^ 2, by positivity, fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hC w hw) 2⟩
  choose M hM0 hM using hM
  set V : ℕ → ℝ := fun j => (volume (S j)).toReal with hV
  have hV0 : ∀ j, 0 ≤ V j := fun j => ENNReal.toReal_nonneg
  obtain ⟨χ, hχc, hχm, hχ⟩ := exists_convexOn_monotone_ge
    fun j => Real.log ((M j + 1) * (V j + 1) * 2 ^ j) / c
  have hψc : ConvexOn ℝ Ω (χ ∘ ρ) := by
    refine ⟨hΩc, fun x hx y hy a b ha hb hab => ?_⟩
    exact (hχm (hρc.2 hx hy ha hb hab)).trans
      (hχc.2 (mem_univ _) (mem_univ _) ha hb hab)
  refine ⟨fun z => ((χ (ρ z) : ℝ) : EReal),
    plurisubharmonicOn_of_convexOn hΩo hψc (hψc.continuousOn hΩo), ?_⟩
  set β : ℕ → ℝ := fun j => Real.log ((M j + 1) * (V j + 1) * 2 ^ j) / c with hβ
  set K : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (M j * Real.exp (-(c * β j))) with hK
  have hpt : ∀ w ∈ ι ⁻¹' Ω, multiplierDensity (fun w => ((χ (ρ (ι w)) : ℝ) : EReal)) c f w ≤
      ∑' j, (S j).indicator (fun _ => K j) w := by
    intro w hw
    have hlog : -Real.log (d (ι w)) ≤ max (-Real.log (d (ι w))) 0 := le_max_left _ _
    have hρ0 : 0 ≤ ρ (ι w) := by positivity
    set n := ⌈ρ (ι w)⌉₊
    have h1 : ρ (ι w) ≤ n := Nat.le_ceil _
    have hn : w ∈ S n := by
      refine ⟨?_, ?_⟩
      · have : ‖w‖ ≤ ρ (ι w) := by
          simp only [hρ, hι_def, norm_hyperplaneEmbedding]
          exact le_add_of_nonneg_right (le_max_right _ _)
        linarith
      · rw [← Real.le_log_iff_exp_le (hdpos _ hw)]
        have : max (-Real.log (d (ι w))) 0 ≤ ρ (ι w) := le_add_of_nonneg_left (norm_nonneg _)
        linarith
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [indicator_of_mem hn]
    simp only [multiplierDensity, multiplierWeight_coe, hK]
    rw [ENNReal.ofReal_mul (hM0 n)]
    have hβn : β n ≤ χ (ρ (ι w)) := (hχ n).trans
      (hχm (by have := Nat.ceil_lt_add_one hρ0; linarith))
    gcongr
    exact hM n w hn
  have hbound : ∀ j, K j * volume (S j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := fun j => by
    have hX : 0 < (M j + 1) * (V j + 1) * 2 ^ j := by
      have := hM0 j; have := hV0 j; positivity
    rw [hK, ← ENNReal.ofReal_toReal (hSc j).measure_lt_top.ne,
      ← ENNReal.ofReal_mul (by have := hM0 j; positivity),
      show (2⁻¹ : ℝ≥0∞) ^ j = ENNReal.ofReal ((1 / 2) ^ j) by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_ofNat]]
    apply ENNReal.ofReal_le_ofReal
    simp only [hβ]
    rw [mul_div_cancel₀ _ hc.ne', Real.exp_neg, Real.exp_log hX]
    change M j * _ * V j ≤ _
    rw [show M j * ((M j + 1) * (V j + 1) * 2 ^ j)⁻¹ * V j =
      (M j * V j) / ((M j + 1) * (V j + 1) * 2 ^ j) by ring, div_le_iff₀ hX]
    have h2 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    rw [show (1 / 2 : ℝ) ^ j * ((M j + 1) * (V j + 1) * 2 ^ j) =
      (M j + 1) * (V j + 1) * ((1 / 2) ^ j * 2 ^ j) by ring, h2, mul_one]
    have := hM0 j; have := hV0 j
    nlinarith
  have hmeas : MeasurableSet (ι ⁻¹' Ω) := (hΩo.preimage hι).measurableSet
  calc _ ≤ ∫⁻ w in ι ⁻¹' Ω, ∑' j, (S j).indicator (fun _ => K j) w := setLIntegral_mono' hmeas hpt
    _ ≤ ∫⁻ w, ∑' j, (S j).indicator (fun _ => K j) w := setLIntegral_le_lintegral _ _
    _ = ∑' j, K j * volume (S j) := by
        rw [lintegral_tsum fun j =>
          (measurable_const.indicator (hSc j).isClosed.measurableSet).aemeasurable]
        exact tsum_congr fun j => lintegral_indicator_const (hSc j).isClosed.measurableSet _
    _ ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j := ENNReal.tsum_le_tsum hbound
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt (ENNReal.inv_lt_one.mpr (by norm_num)))

end

end Hironaka
