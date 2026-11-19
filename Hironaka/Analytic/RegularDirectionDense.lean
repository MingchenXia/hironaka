import Hironaka.Analytic.HolomorphicZeroSetThin

set_option autoImplicit false

/-!
# The directions in which a nonzero germ is regular form an open dense set

`Hironaka.RegularDirection.exists_regular_continuousLinearEquiv` produces ONE direction
along which a holomorphic germ `g ≠ 0` at `0` has finite order, and says nothing about
which one.  Demailly's local parametrization theorem needs more: the normalizing direction
has to be DENSE, because `Hironaka.AdaptedProjectionGerm.exists_adaptedProjection` prescribes
a direction `B₀` and only approximates it, and it has to serve a FINITE FAMILY of germs at
once, because the germ of a subvariety at a point is reducible.

This module isolates the atom of both requirements.  Write

  `RegularAlong g w  ↔  t ↦ g (t • w)` is not identically zero near `0`.

* `regularAlong_iff` — the key reformulation: on a fixed disc `‖t‖ < ρ` small enough that
  the segment stays in the domain, `RegularAlong g w` is equivalent to the existence of a
  SINGLE `t` with `g (t • w) ≠ 0`.  This is the one-variable identity theorem: a
  holomorphic function of `t` vanishing near `0` vanishes on the whole disc.
* `isOpen_setOf_regularAlong` — hence the good directions are OPEN: one surviving nonzero
  value `g (t₀ • w₁) ≠ 0` survives a perturbation of `w₁`, and the reformulation turns that
  single value back into regularity.
* `dense_setOf_regularAlong` — and DENSE.  If they missed a ball `B(w₀, δ)` then `g` would
  vanish on `c • B(w₀, δ) = B(c • w₀, ‖c‖δ)` for `c = ρ/2 ≠ 0`, an open subset of the
  domain, hence on all of it by the identity theorem in `E`
  (`Hironaka.RiemannExtension.eventually_eq_zero_of_eventually_eq_zero`), contradicting
  `g ≠ 0`.
* `exists_forall_regularAlong` — open plus dense is exactly what makes a FINITE family
  collapse to one direction: a finite intersection of dense open sets is dense open, with
  no Baire category needed.

Degenerate cases.  `w = 0` is allowed and is regular exactly when `g 0 ≠ 0`; the statements
never assume `w ≠ 0`, and `dense_setOf_regularAlong` does not produce a nonzero `w` (it
cannot: for `g` vanishing at `0` the origin is a bad direction, which is why the conclusion
is density and not "every direction").  `E = 0` is allowed: there `g ≠ 0` near `0` forces
`g 0 ≠ 0`, every direction is good and the good set is `univ`.  The empty family in
`exists_forall_regularAlong` returns any `w` in the ball, which exists because `δ > 0`.
-/

open Filter Metric Set
open scoped Topology

namespace Hironaka.RegularDirectionDense

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `g` is **regular along** the direction `w`: its restriction to the complex line `ℂ w`
is not identically zero near the origin.  This is the hypothesis under which Weierstrass
preparation applies in the direction `w`. -/
def RegularAlong (g : E → ℂ) (w : E) : Prop := ¬ ∀ᶠ t : ℂ in 𝓝 0, g (t • w) = 0

theorem smul_mem_ball_of_norm_lt {r ρ : ℝ} {w : E} (hw : ρ * ‖w‖ < r) {t : ℂ}
    (ht : ‖t‖ < ρ) : t • w ∈ ball (0 : E) r := by
  rw [mem_ball_zero_iff, norm_smul]
  calc ‖t‖ * ‖w‖ ≤ ρ * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right ht.le (norm_nonneg w)
    _ < r := hw

/-- **Regularity along `w` is a single nonvanishing value.**  On a disc `‖t‖ < ρ` whose
image `ℂ w`-segment stays inside the domain of `g`, `g` is regular along `w` as soon as it
is nonzero at ONE point of that segment — by the one-variable identity theorem, a
holomorphic function of `t` that vanishes near `0` vanishes on the whole disc.  This is
what makes the set of good directions open. -/
theorem regularAlong_iff {g : E → ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball 0 r))
    {ρ : ℝ} (hρ : 0 < ρ) {w : E} (hw : ρ * ‖w‖ < r) :
    RegularAlong g w ↔ ∃ t : ℂ, ‖t‖ < ρ ∧ g (t • w) ≠ 0 := by
  constructor
  · intro hreg
    by_contra hcon
    push Not at hcon
    refine hreg (eventually_of_mem (ball_mem_nhds (0 : ℂ) hρ) fun t ht => hcon t ?_)
    simpa using ht
  · rintro ⟨t₀, ht₀, hne0⟩ hev
    set φ : ℂ → ℂ := fun t => g (t • w) with hφ
    have hmem : ∀ t ∈ ball (0 : ℂ) ρ, t • w ∈ ball (0 : E) r := fun t ht =>
      smul_mem_ball_of_norm_lt hw (by simpa using ht)
    have hdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) ρ) :=
      hg.comp (differentiable_id.smul_const w).differentiableOn hmem
    have hanal : AnalyticOnNhd ℂ φ (ball (0 : ℂ) ρ) := hdiff.analyticOnNhd isOpen_ball
    have h0 : φ =ᶠ[𝓝 0] 0 := hev
    have := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) ρ).isPreconnected (mem_ball_self hρ) h0
      (show t₀ ∈ ball (0 : ℂ) ρ by simpa using ht₀)
    exact hne0 this

/-- **The good directions are open.** -/
theorem isOpen_setOf_regularAlong {g : E → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r)) : IsOpen {w : E | RegularAlong g w} := by
  rw [Metric.isOpen_iff]
  intro w₁ hw₁
  set ρ : ℝ := r / (‖w₁‖ + 2) with hρdef
  have hpos : (0 : ℝ) < ‖w₁‖ + 2 := by positivity
  have hρ : 0 < ρ := div_pos hr hpos
  have hkey : ∀ w : E, ‖w‖ ≤ ‖w₁‖ + 1 → ρ * ‖w‖ < r := by
    intro w hw
    have h1 : ρ * ‖w‖ ≤ ρ * (‖w₁‖ + 1) := by
      exact mul_le_mul_of_nonneg_left hw hρ.le
    have h2 : ρ * (‖w₁‖ + 1) < r := by
      rw [hρdef, div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [norm_nonneg w₁]
    exact h1.trans_lt h2
  obtain ⟨t₀, ht₀, hne0⟩ :=
    (regularAlong_iff hg hρ (hkey w₁ (by linarith))).1 hw₁
  have hmem₁ : t₀ • w₁ ∈ ball (0 : E) r :=
    smul_mem_ball_of_norm_lt (hkey w₁ (by linarith)) ht₀
  have hcont : ContinuousAt (fun w : E => g (t₀ • w)) w₁ := by
    have hgat : DifferentiableAt ℂ g (t₀ • w₁) :=
      hg.differentiableAt (isOpen_ball.mem_nhds hmem₁)
    exact hgat.continuousAt.comp (by fun_prop)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.1 (hcont.eventually_ne hne0)
  refine ⟨min η 1, lt_min hη one_pos, fun w hw => ?_⟩
  have hw1 : dist w w₁ < 1 := lt_of_lt_of_le hw (min_le_right _ _)
  have hwη : w ∈ ball w₁ η := mem_ball.2 (lt_of_lt_of_le hw (min_le_left _ _))
  have hnorm : ‖w‖ ≤ ‖w₁‖ + 1 := by
    have := norm_sub_norm_le w w₁
    have hd : ‖w - w₁‖ < 1 := by simpa [dist_eq_norm] using hw1
    linarith
  exact (regularAlong_iff hg hρ (hkey w hnorm)).2 ⟨t₀, ht₀, hηsub hwη⟩

/-- **The good directions are dense.**  If they missed a ball `B(w₀, δ)` then `g` would
vanish identically on the open ball `B(c • w₀, ‖c‖ δ)` for any small `c ≠ 0`, hence — by
the identity theorem on the connected domain — near `0`. -/
theorem dense_setOf_regularAlong {g : E → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hne : ¬ ∀ᶠ z in 𝓝 (0 : E), g z = 0) :
    Dense {w : E | RegularAlong g w} := by
  rw [Metric.dense_iff]
  rintro w₀ δ hδ
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hbad : ∀ w ∈ ball w₀ δ, ¬ RegularAlong g w := by
    intro w hw hreg
    exact absurd (Set.eq_empty_iff_forall_notMem.1 hcon w ⟨hw, hreg⟩) (by simp)
  set ρ : ℝ := r / (‖w₀‖ + δ + 1) with hρdef
  have hpos : (0 : ℝ) < ‖w₀‖ + δ + 1 := by positivity
  have hρ : 0 < ρ := div_pos hr hpos
  have hkey : ∀ w : E, ‖w‖ ≤ ‖w₀‖ + δ → ρ * ‖w‖ < r := by
    intro w hw
    have h1 : ρ * ‖w‖ ≤ ρ * (‖w₀‖ + δ) := mul_le_mul_of_nonneg_left hw hρ.le
    have h2 : ρ * (‖w₀‖ + δ) < r := by
      rw [hρdef, div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [norm_nonneg w₀]
    exact h1.trans_lt h2
  set c : ℂ := ((ρ / 2 : ℝ) : ℂ) with hcdef
  have hcnorm : ‖c‖ = ρ / 2 := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hcnorm]; positivity
  have hclt : ‖c‖ < ρ := by rw [hcnorm]; linarith
  -- every direction in the ball is bad, so `g` kills the whole scaled ball
  have hzero : ∀ y ∈ ball (c • w₀) (ρ / 2 * δ), g y = 0 := by
    intro y hy
    set w : E := c⁻¹ • y with hwdef
    have hwmem : w ∈ ball w₀ δ := by
      rw [mem_ball, dist_eq_norm, hwdef]
      have : c⁻¹ • y - w₀ = c⁻¹ • (y - c • w₀) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, norm_smul, norm_inv, hcnorm]
      rw [mem_ball, dist_eq_norm] at hy
      rw [inv_mul_lt_iff₀ (by positivity)]
      linarith [hy]
    have hnormw : ‖w‖ ≤ ‖w₀‖ + δ := by
      have := (mem_ball.1 hwmem)
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le w w₀
      linarith
    have := hbad w hwmem
    rw [regularAlong_iff hg hρ (hkey w hnormw)] at this
    push Not at this
    have hcy : c • w = y := by rw [hwdef, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have := this c hclt
    rwa [hcy] at this
  have hmem0 : c • w₀ ∈ ball (0 : E) r :=
    smul_mem_ball_of_norm_lt (hkey w₀ (by linarith)) hclt
  have hev : ∀ᶠ z in 𝓝 (c • w₀), g z = 0 :=
    eventually_of_mem (ball_mem_nhds _ (by positivity)) hzero
  exact hne (RiemannExtension.eventually_eq_zero_of_eventually_eq_zero isOpen_ball
    (convex_ball (0 : E) r).isPreconnected hg hmem0 hev 0 (mem_ball_self hr))

/-- A finite intersection of dense open sets is dense — no Baire category needed. -/
theorem dense_biInter_finset {X : Type*} [TopologicalSpace X] {ι : Type*}
    (s : Finset ι) {S : ι → Set X} (ho : ∀ i ∈ s, IsOpen (S i)) (hd : ∀ i ∈ s, Dense (S i)) :
    Dense (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hrest : Dense (⋂ i ∈ s, S i) :=
        ih (fun i hi => ho i (Finset.mem_insert_of_mem hi))
          (fun i hi => hd i (Finset.mem_insert_of_mem hi))
      have hSa : Dense (S a) := hd a (Finset.mem_insert_self a s)
      have hSao : IsOpen (S a) := ho a (Finset.mem_insert_self a s)
      simpa [Finset.set_biInter_insert] using hSa.inter_of_isOpen_left hrest hSao

/-- **One direction for a finite family, as close as we like to a prescribed one.**  This
is the form Demailly's perturbation step consumes: the germ of a subvariety at a point is
reducible, and one normalizing direction has to serve all of its components at once. -/
theorem exists_forall_regularAlong {ι : Type*} [Fintype ι] {g : ι → E → ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ∀ i, DifferentiableOn ℂ (g i) (ball 0 r))
    (hne : ∀ i, ¬ ∀ᶠ z in 𝓝 (0 : E), g i z = 0) (w₀ : E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : E, ‖w - w₀‖ < δ ∧ ∀ i, RegularAlong (g i) w := by
  classical
  have hdense : Dense (⋂ i ∈ (Finset.univ : Finset ι), {w : E | RegularAlong (g i) w}) :=
    dense_biInter_finset _ (fun i _ => isOpen_setOf_regularAlong hr (hg i))
      (fun i _ => dense_setOf_regularAlong hr (hg i) (hne i))
  obtain ⟨w, hw, hmem⟩ := Metric.dense_iff.1 hdense w₀ δ hδ
  refine ⟨w, ?_, fun i => ?_⟩
  · rw [mem_ball, dist_eq_norm] at hw; exact hw
  · simpa using Set.mem_iInter₂.1 hmem i (Finset.mem_univ i)

/-- Scaling the direction by a nonzero constant does not change where `g` vanishes along it:
the good directions form a cone. -/
theorem eventually_smul_of_eventually {g : E → ℂ} (c : ℂ) {w : E}
    (h : ∀ᶠ t : ℂ in 𝓝 0, g (t • w) = 0) : ∀ᶠ t : ℂ in 𝓝 0, g (t • (c • w)) = 0 := by
  have htend : Tendsto (fun t : ℂ => t * c) (𝓝 0) (𝓝 0) := by
    have := (continuous_mul_const c).continuousAt (x := (0 : ℂ))
    simpa [ContinuousAt] using this
  filter_upwards [htend.eventually h] with t ht
  rwa [smul_smul]

/-- **Regularity only sees the complex line `ℂ w`.** -/
theorem regularAlong_smul {g : E → ℂ} {c : ℂ} (hc : c ≠ 0) (w : E) :
    RegularAlong g (c • w) ↔ RegularAlong g w := by
  unfold RegularAlong
  constructor
  · intro h hev
    exact h (eventually_smul_of_eventually c hev)
  · intro h hev
    refine h ?_
    have := eventually_smul_of_eventually c⁻¹ hev
    simpa [smul_smul, inv_mul_cancel₀ hc] using this

/-- `exists_forall_regularAlong` from the germ hypothesis: each `g i` is only required to be
complex differentiable NEAR `0`, the common domain being extracted as the smallest of the
finitely many radii. -/
theorem exists_forall_regularAlong' {ι : Type*} [Fintype ι] {g : ι → E → ℂ}
    (hg : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (g i) z)
    (hne : ∀ i, ¬ ∀ᶠ z in 𝓝 (0 : E), g i z = 0) (w₀ : E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : E, ‖w - w₀‖ < δ ∧ ∀ i, RegularAlong (g i) w := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨w₀, by simpa using hδ, fun i => (IsEmpty.false i).elim⟩
  choose r hr hball using fun i => Metric.eventually_nhds_iff_ball.1 (hg i)
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) r Finset.univ_nonempty
  refine exists_forall_regularAlong (r := r i₀) (hr i₀) (fun i => ?_) hne w₀ hδ
  intro y hy
  exact ((hball i y (ball_subset_ball (hmin i (Finset.mem_univ i)) hy)).differentiableWithinAt)

end Hironaka.RegularDirectionDense
