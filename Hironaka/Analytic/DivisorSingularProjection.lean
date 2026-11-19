import Hironaka.Analytic.DivisorRegularLocus
import Hironaka.Analytic.LastVariableTaylorDivision
import Hironaka.Analytic.HolomorphicZeroSetNull

set_option autoImplicit false

/-!
# Almost every line misses the non-transverse points of a divisor (Lelong--Poincaré, LP4)

Let `g` be holomorphic on an open set `Ω` of a finite-dimensional complex inner product space `V`,
vanishing identically near no point of `Ω`, let `u` be a unit vector and `V = ℂ u ⊕ ι(E)` an
orthogonal splitting.  A zero `y` of `g` is *bad* (for the direction `u`) if it is not a transverse
regular point of the divisor of `g` (`DivisorRegularLocus.transverseLocus`): either the divisor is
singular at `y`, or it is regular but tangent to `u` there.  We prove

  `μ (π '' {bad points}) = 0`  (`measure_image_bad_eq_zero`)

for every additive Haar measure `μ` on `E`: almost every line parallel to `u` meets the zero set of
`g` only at transverse regular points.  No dimension theory of the singular set is used.

## Proof

Stratify the zeros by the order `j` of vanishing of `g` along the line through them in the
direction `u` (`lineOrder_eq_iff`: it is read off from the iterated directional derivatives
`∂ᵤⁱ g`).

* `j = ∞` (`exists_nhds_null_top`): near a point, such zeros fill whole segments of lines; their
  projection is contained in the set of `w` over which `g` vanishes on a whole disc, which is null,
  for otherwise `g` would vanish on an open set.
* `j < ∞` (`exists_nhds_null_nat`): near `y₀` the zeros of order `j` lie on the smooth hypersurface
  `{∂ᵤ^{j-1} g = 0}`, which is transverse to `u`, hence a holomorphic graph `{k(w) u + ι w}`.  In
  the coordinates `(w, t) ↦ (k(w) + t) u + ι w`, Taylor division in the last variable writes
  `g = tᵃ Q(w, t)` with `Q(·, 0)` not identically zero.  Where `Q(w, 0) ≠ 0`, the point of the graph
  over `w` is a transverse regular point (`g = hᵃ v` with `h = ⟪u, ·⟫ - k ∘ π`, `dh(u) = 1`), so the
  bad points project into the null zero set of `Q(·, 0)`.
* A countable cover of each stratum finishes the proof.
-/

open Set Filter Function MeasureTheory Metric
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Hironaka.DivisorSingularProjection

open DivisorRegularLocus

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The directional derivative `∂ᵤ f`. -/
def dirDeriv (u : V) (f : V → ℂ) : V → ℂ := fun y => fderiv ℂ f y u

theorem differentiableOn_dirDeriv {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (u : V) : DifferentiableOn ℂ (dirDeriv u f) Ω :=
  Hironaka.differentiableOn_fderiv_apply_of_isOpen hf hΩ u

theorem differentiableOn_iterate_dirDeriv {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (u : V) (i : ℕ) :
    DifferentiableOn ℂ ((dirDeriv u)^[i] f) Ω := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact differentiableOn_dirDeriv hΩ ih u

theorem line_isOpen {Ω : Set V} (hΩ : IsOpen Ω) (y u : V) : IsOpen {s : ℂ | y + s • u ∈ Ω} :=
  hΩ.preimage (by fun_prop)

theorem hasDerivAt_line {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {y u : V} {s : ℂ} (hs : y + s • u ∈ Ω) :
    HasDerivAt (fun s : ℂ => f (y + s • u)) (dirDeriv u f (y + s • u)) s := by
  have hl : HasDerivAt (fun s : ℂ => y + s • u) u s := by
    simpa using ((hasDerivAt_id s).smul_const u).const_add y
  exact ((hf _ hs).differentiableAt (hΩ.mem_nhds hs)).hasFDerivAt.comp_hasDerivAt s hl

/-- The iterated derivatives of `g` along a line are the iterated directional derivatives. -/
theorem iteratedDeriv_line {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (y u : V) (i : ℕ) :
    ∀ s : ℂ, y + s • u ∈ Ω →
      iteratedDeriv i (fun s : ℂ => f (y + s • u)) s = (dirDeriv u)^[i] f (y + s • u) := by
  induction i with
  | zero => intro s _; simp
  | succ i ih =>
    intro s hs
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv i (fun s : ℂ => f (y + s • u)) =ᶠ[𝓝 s]
        fun s : ℂ => (dirDeriv u)^[i] f (y + s • u) := by
      filter_upwards [(line_isOpen hΩ y u).mem_nhds hs] with t ht
      exact ih t ht
    rw [hev.deriv_eq]
    exact (hasDerivAt_line hΩ (differentiableOn_iterate_dirDeriv hΩ hf u i) hs).deriv

theorem analyticAt_line {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {y u : V} {s : ℂ} (hs : y + s • u ∈ Ω) :
    AnalyticAt ℂ (fun s : ℂ => f (y + s • u)) s := by
  refine DifferentiableOn.analyticAt (s := {s : ℂ | y + s • u ∈ Ω}) ?_
    ((line_isOpen hΩ y u).mem_nhds hs)
  intro t ht
  exact (hasDerivAt_line hΩ hf ht).differentiableAt.differentiableWithinAt

/-- **The order along a line** is read off from the iterated directional derivatives. -/
theorem lineOrder_eq_iff {f : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {y : V} (hy : y ∈ Ω) (u : V) (j : ℕ) :
    analyticOrderAt (fun s : ℂ => f (y + s • u)) 0 = j ↔
      (∀ i < j, (dirDeriv u)^[i] f y = 0) ∧ (dirDeriv u)^[j] f y ≠ 0 := by
  have hy' : y + (0 : ℂ) • u ∈ Ω := by simpa using hy
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticAt_line hΩ hf hy')]
  have key : ∀ i, iteratedDeriv i (fun s : ℂ => f (y + s • u)) 0 = (dirDeriv u)^[i] f y :=
    fun i => by simpa using iteratedDeriv_line hΩ hf y u i 0 hy'
  simp only [key]

section Null

variable [FiniteDimensional ℂ V]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop]
theorem Splitting.differentiable_ι {u : V} (S : Splitting u E) : Differentiable ℂ S.ι :=
  S.ι.toContinuousLinearMap.differentiable

/-- The points where `g` vanishes to infinite order along the direction `u`. -/
def infiniteOrderSet (g : V → ℂ) (Ω : Set V) (u : V) : Set V :=
  {y | y ∈ Ω ∧ analyticOrderAt (fun s : ℂ => g (y + s • u)) 0 = ⊤}

omit [FiniteDimensional ℂ V] in
/-- **Infinite order along `u`.**  Near every point, the zeros of infinite order along `u` project
to a null set. -/
theorem exists_nhds_null_top {g : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) {u : V}
    (S : Splitting u E) {y₀ : V} (hy₀ : y₀ ∈ Ω) :
    ∃ N ∈ 𝓝 y₀, μ (S.π '' (N ∩ infiniteOrderSet g Ω u)) = 0 := by
  set s₀ : ℂ := ⟪u, y₀⟫_ℂ
  set w₀ : E := S.π y₀
  set Φ : ℂ × E → V := fun p => p.1 • u + S.ι p.2 with hΦdef
  have hΦc : Continuous Φ := by fun_prop
  have hΦ₀ : Φ (s₀, w₀) = y₀ := (S.decomp y₀).symm
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hΦc.continuousAt.preimage_mem_nhds (by rw [hΦ₀]; exact hΩ.mem_nhds hy₀))
  rw [← ball_prod_same] at hball
  have hΦΩ : ∀ s ∈ ball s₀ ε, ∀ w ∈ ball w₀ ε, s • u + S.ι w ∈ Ω := fun s hs w hw =>
    hball (mk_mem_prod hs hw)
  set N : Set V := {y | ⟪u, y⟫_ℂ ∈ ball s₀ ε ∧ S.π y ∈ ball w₀ ε} with hNdef
  have hNo : IsOpen N :=
    (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage S.π.continuous)
  have hy₀N : y₀ ∈ N := ⟨mem_ball_self hε, mem_ball_self hε⟩
  set C : Set E := {w | w ∈ ball w₀ ε ∧ ∀ s ∈ ball s₀ ε, g (s • u + S.ι w) = 0} with hCdef
  have hline : ∀ w ∈ ball w₀ ε, DifferentiableOn ℂ (fun s : ℂ => g (s • u + S.ι w))
      (ball s₀ ε) := fun w hw =>
    hg.comp (by fun_prop) fun s hs => hΦΩ s hs w hw
  -- the projection lies in `C`
  have hA : S.π '' (N ∩ infiniteOrderSet g Ω u) ⊆ C := by
    rintro _ ⟨y, ⟨⟨hys, hyw⟩, _, hord⟩, rfl⟩
    refine ⟨hyw, ?_⟩
    have hdec := S.decomp y
    have hev : ∀ᶠ s in 𝓝 (⟪u, y⟫_ℂ), g (s • u + S.ι (S.π y)) = 0 := by
      have h0 := analyticOrderAt_eq_top.mp hord
      have ht : Tendsto (fun s : ℂ => s - ⟪u, y⟫_ℂ) (𝓝 (⟪u, y⟫_ℂ)) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (⟪u, y⟫_ℂ))).sub_const (⟪u, y⟫_ℂ)
      filter_upwards [ht.eventually h0] with s hs
      have : y + (s - ⟪u, y⟫_ℂ) • u = s • u + S.ι (S.π y) := by
        calc y + (s - ⟪u, y⟫_ℂ) • u = (⟪u, y⟫_ℂ • u + S.ι (S.π y)) + (s - ⟪u, y⟫_ℂ) • u := by
              rw [← hdec]
          _ = s • u + S.ι (S.π y) := by rw [sub_smul]; abel
      rwa [this] at hs
    have hzero := ((hline _ hyw).analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball s₀ ε).isPreconnected hys hev
    intro s hs
    exact hzero hs
  -- `C` is null
  have hC : μ C = 0 := by
    by_cases h : ∃ s ∈ ball s₀ ε, ∃ w ∈ ball w₀ ε, g (s • u + S.ι w) ≠ 0
    · obtain ⟨s, hs, w, hw, hne⟩ := h
      have hfd : DifferentiableOn ℂ (fun w : E => g (s • u + S.ι w)) (ball w₀ ε) :=
        hg.comp (by fun_prop) fun w hw => hΦΩ s hs w hw
      refine measure_mono_null ?_
        (HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero μ isOpen_ball
          (convex_ball w₀ ε) hfd hw hne)
      intro w hwC
      exact ⟨hwC.1, hwC.2 s hs⟩
    · push Not at h
      exfalso
      have hzero : ∀ᶠ z in 𝓝 y₀, g z = 0 := by
        filter_upwards [hNo.mem_nhds hy₀N] with z hz
        rw [S.decomp z]
        exact h _ hz.1 _ hz.2
      exact (hg0 y₀ hy₀).and_eventually hzero |>.exists.elim fun z hz => hz.1 hz.2
  exact ⟨N, hNo.mem_nhds hy₀N, measure_mono_null hA hC⟩

/-- The zeros of `g` of order exactly `j` along `u` that are not transverse regular points. -/
def badStratum (g : V → ℂ) (Ω : Set V) (u : V) (j : ℕ) : Set V :=
  {y | y ∈ Ω ∧ g y = 0 ∧ analyticOrderAt (fun s : ℂ => g (y + s • u)) 0 = j ∧
    y ∉ transverseLocus g u}

/-- **Finite order along `u`.**  Near a zero of order `j < ∞` along `u`, the non-transverse zeros
of the same order project to a null set. -/
theorem exists_nhds_null_nat {g : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {u : V} (hu : ‖u‖ = 1) (S : Splitting u E) {y₀ : V}
    (hy₀ : y₀ ∈ Ω) (hgy₀ : g y₀ = 0) {j : ℕ}
    (hj : analyticOrderAt (fun s : ℂ => g (y₀ + s • u)) 0 = j) :
    ∃ N ∈ 𝓝 y₀, μ (S.π '' (N ∩ badStratum g Ω u j)) = 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨hlow, hj'⟩ := (lineOrder_eq_iff hΩ hg hy₀ u j).mp hj
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd (by simpa using hgy₀) hj'
    · exact h
  -- the hypersurface `{∂ᵤ^{j-1} g = 0}`
  set D : V → ℂ := (dirDeriv u)^[j - 1] g with hDdef
  have hD : DifferentiableOn ℂ D Ω := differentiableOn_iterate_dirDeriv hΩ hg u _
  have hDy₀ : D y₀ = 0 := hlow (j - 1) (by omega)
  have hDj : ∀ y, dirDeriv u D y = (dirDeriv u)^[j] g y := by
    intro y
    have h1 : j = (j - 1) + 1 := by omega
    conv_rhs => rw [h1, Function.iterate_succ_apply']
  have hD' : fderiv ℂ D y₀ u ≠ 0 := by rw [← dirDeriv, hDj]; exact hj'
  have hDc : ContinuousOn (fderiv ℂ D) Ω :=
    (Hironaka.contDiffOn_of_differentiableOn_complex hD hΩ).continuousOn_fderiv_of_isOpen hΩ
      (by simp)
  have hUo : IsOpen {y | y ∈ Ω ∧ fderiv ℂ D y u ≠ 0} := by
    have := (hDc.clm_apply (continuousOn_const (c := u))).isOpen_inter_preimage hΩ
      (isOpen_ne : IsOpen {z : ℂ | z ≠ 0})
    simpa [Set.inter_def] using this
  let PD : RegularPresentation D y₀ :=
    { U := {y | y ∈ Ω ∧ fderiv ℂ D y u ≠ 0}
      isOpen := hUo
      mem := ⟨hy₀, hD'⟩
      m := 1
      m_pos := one_pos
      h := D
      v := fun _ => 1
      h_diff := hD.mono fun y hy => hy.1
      v_diff := differentiableOn_const 1
      h_zero := hDy₀
      dh_ne := fun y hy h0 => hy.2 (by rw [h0]; rfl)
      v_ne := fun _ _ => one_ne_zero
      eq := fun y _ => by simp }
  obtain ⟨N₁, W, k, hN₁o, hy₀N₁, hN₁U, -, hWo, hw₀W, hk, hgraph, hslice, -⟩ :=
    PD.exists_graph_slices hu S hD'
  set w₀ : E := S.π y₀ with hw₀
  have hdec₀ := S.decomp y₀
  have hs₀ : ⟪u, y₀⟫_ℂ = k w₀ := by
    have h := (hslice w₀ (⟪u, y₀⟫_ℂ) (by rw [← hdec₀]; exact hy₀N₁)).mp
      (by rw [← hdec₀]; exact hDy₀)
    exact h.2
  -- coordinates `(z, t) ↦ (k (w₀ + z) + t) u + ι (w₀ + z)`
  set Ψ : E × ℂ → V := fun p => (k (w₀ + p.1) + p.2) • u + S.ι (w₀ + p.1) with hΨdef
  set O : Set (E × ℂ) := {p | w₀ + p.1 ∈ W} with hOdef
  have hOo : IsOpen O := hWo.preimage (by fun_prop)
  have hΨd : DifferentiableOn ℂ Ψ O := by
    have hk' : DifferentiableOn ℂ (fun p : E × ℂ => k (w₀ + p.1)) O :=
      hk.comp (by fun_prop) fun p hp => hp
    exact ((hk'.add differentiableOn_snd).smul_const u).add
      (S.ι.toContinuousLinearMap.differentiable.comp_differentiableOn (by fun_prop))
  have hΨ₀ : Ψ (0, 0) = y₀ := by
    simp only [hΨdef, add_zero]
    rw [← hs₀, ← hdec₀]
  have h0O : ((0 : E), (0 : ℂ)) ∈ O := by simpa [hOdef] using hw₀W
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (hΨd.continuousOn.isOpen_inter_preimage hOo hN₁o) (0, 0) ⟨h0O, by rw [Set.mem_preimage, hΨ₀]; exact hy₀N₁⟩
  rw [← ball_prod_same] at hεsub
  set B : Set (E × ℂ) := ball (0 : E) ε ×ˢ ball (0 : ℂ) ε with hBdef
  have hBO : B ⊆ O := fun p hp => (hεsub hp).1
  have hBN : ∀ p ∈ B, Ψ p ∈ N₁ := fun p hp => (hεsub hp).2
  set F : E × ℂ → ℂ := fun p => g (Ψ p) with hFdef
  have hFd : DifferentiableOn ℂ F B :=
    hg.comp (hΨd.mono hBO) fun p hp => (hN₁U (hBN p hp)).1
  set ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by positivity
  have hρR : ρ < ε := by simp only [ρ]; linarith
  -- the order of `F (0, ·)` at `0` is `j`
  have hF0 : ∀ t : ℂ, F (0, t) = g (y₀ + t • u) := by
    intro t
    simp only [hFdef, hΨdef, add_zero]
    rw [add_smul, ← hs₀]
    conv_rhs => rw [hdec₀]
    abel_nf
    rfl
  set c : ℕ → E → ℂ := fun i => lastCoeff F ρ i with hcdef
  have hex : ∃ i, i ≤ j ∧ ∃ z ∈ ball (0 : E) ε, c i z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdiv := eq_lastQuot_mul_add hρ hρR hFd (j + 1)
    have hev : (fun t : ℂ => g (y₀ + t • u)) =ᶠ[𝓝 0]
        (fun t : ℂ => lastQuot F ρ (j + 1) (0, t)) * ((· - (0 : ℂ)) ^ (j + 1)) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hε] with t ht
      rw [← hF0, hdiv (0, t) ⟨mem_ball_self hε, ht⟩]
      have hsum : ∑ i ∈ Finset.range (j + 1), lastCoeff F ρ i (0, t).1 * (0, t).2 ^ i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have := hcon i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) 0 (mem_ball_self hε)
        simp [hcdef] at this
        simp [this]
      rw [hsum, add_zero]
      simp
    have hQa : AnalyticAt ℂ (fun t : ℂ => lastQuot F ρ (j + 1) (0, t)) 0 := by
      refine DifferentiableOn.analyticAt (s := ball (0 : ℂ) ε) ?_ (ball_mem_nhds 0 hε)
      exact (differentiableOn_lastQuot hρ hρR hFd (j + 1)).comp (by fun_prop)
        fun t ht => ⟨mem_ball_self hε, ht⟩
    have hord := analyticOrderAt_congr hev
    rw [hj, analyticOrderAt_mul hQa (by fun_prop), analyticOrderAt_centeredMonomial] at hord
    have : ((j + 1 : ℕ) : ℕ∞) ≤ (j : ℕ∞) := by
      rw [hord]
      exact le_add_self
    norm_cast at this
    omega
  classical
  set a := Nat.find hex with hadef
  obtain ⟨haj, z₁, hz₁, hcz₁⟩ := Nat.find_spec hex
  have hmin : ∀ i < a, ∀ z ∈ ball (0 : E) ε, c i z = 0 := by
    intro i hi z hz
    have := Nat.find_min hex hi
    push Not at this
    exact this (by omega) z hz
  set Q : E × ℂ → ℂ := lastQuot F ρ a with hQdef
  have hFQ : ∀ p ∈ B, F p = Q p * p.2 ^ a := by
    intro p hp
    rw [eq_lastQuot_mul_add hρ hρR hFd a p hp]
    have hsum : ∑ i ∈ Finset.range a, lastCoeff F ρ i p.1 * p.2 ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [show lastCoeff F ρ i p.1 = c i p.1 from rfl, hmin i (Finset.mem_range.mp hi) p.1 hp.1,
          zero_mul]
    rw [hsum, add_zero]
  have hQ0 : ∀ z, Q (z, 0) = c a z := fun z => by simp [hQdef, lastQuot, hcdef]
  have hQd : DifferentiableOn ℂ Q B := differentiableOn_lastQuot hρ hρR hFd a
  have hca : DifferentiableOn ℂ (c a) (ball (0 : E) ε) := differentiableOn_lastCoeff hρ hρR hFd a
  have hZc : μ (ball (0 : E) ε ∩ c a ⁻¹' {0}) = 0 :=
    HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero μ isOpen_ball
      (convex_ball 0 ε) hca hz₁ hcz₁
  -- the neighbourhood
  set O₁ : Set V := {y | S.π y - w₀ ∈ ball (0 : E) ε} with hO₁def
  have hO₁o : IsOpen O₁ := isOpen_ball.preimage (by fun_prop)
  have hO₁W : ∀ y ∈ O₁, S.π y ∈ W := fun y hy => by
    have := hBO (show (S.π y - w₀, (0 : ℂ)) ∈ B from ⟨hy, mem_ball_self hε⟩)
    simpa [hOdef] using this
  set hfun : V → ℂ := fun y => ⟪u, y⟫_ℂ - k (S.π y) with hhfun
  have hhd : DifferentiableOn ℂ hfun O₁ :=
    ((innerSL ℂ u).differentiable.differentiableOn).sub
      (hk.comp S.π.differentiable.differentiableOn fun y hy => hO₁W y hy)
  set N : Set V := N₁ ∩ (O₁ ∩ hfun ⁻¹' ball (0 : ℂ) ε) with hNdef
  have hNo : IsOpen N := hN₁o.inter (hhd.continuousOn.isOpen_inter_preimage hO₁o isOpen_ball)
  have hy₀N : y₀ ∈ N := by
    refine ⟨hy₀N₁, ?_, ?_⟩
    · show S.π y₀ - w₀ ∈ ball (0 : E) ε
      simp [hw₀, hε]
    · show ⟪u, y₀⟫_ℂ - k (S.π y₀) ∈ ball (0 : ℂ) ε
      rw [← hw₀, hs₀, sub_self]; exact mem_ball_self hε
  have hNB : ∀ y ∈ N, (S.π y - w₀, hfun y) ∈ B := fun y hy => ⟨hy.2.1, hy.2.2⟩
  have hΨy : ∀ y ∈ N, Ψ (S.π y - w₀, hfun y) = y := by
    intro y _
    simp only [hΨdef, hhfun, add_sub_cancel]
    conv_rhs => rw [S.decomp y]
  -- every bad point of the stratum projects into the null set
  have hsub : S.π '' (N ∩ badStratum g Ω u j) ⊆
      (fun z => w₀ + z) '' (ball (0 : E) ε ∩ c a ⁻¹' {0}) := by
    rintro _ ⟨y, ⟨hyN, hyΩ, hgy, hordy, hbad⟩, rfl⟩
    refine ⟨S.π y - w₀, ⟨hyN.2.1, ?_⟩, by simp⟩
    obtain ⟨hlowy, -⟩ := (lineOrder_eq_iff hΩ hg hyΩ u j).mp hordy
    have hDy : D y = 0 := hlowy (j - 1) (by omega)
    have ht : hfun y = 0 := by
      have h := (hslice (S.π y) (⟪u, y⟫_ℂ) (by rw [← S.decomp y]; exact hyN.1)).mp
        (by rw [← S.decomp y]; exact hDy)
      simp [hhfun, ← h.2]
    by_contra hcz
    have hcz' : c a (S.π y - w₀) ≠ 0 := hcz
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · -- `a = 0`: `F (z, 0) = c 0 z ≠ 0`, but it is `g y = 0`
      have h1 := hFQ _ (hNB y hyN)
      rw [show F (S.π y - w₀, hfun y) = g y by simp only [hFdef]; rw [hΨy y hyN], ht, hQ0] at h1
      rw [ha0] at h1 hcz'
      simp only [pow_zero, mul_one] at h1
      exact hcz' (by rw [← h1]; exact hgy)
    · -- `a ≥ 1`: `g = hᵃ v` near `y` with `dh(u) = 1`, so `y` is transverse
      set U' : Set V := N ∩ (fun y' => Q (S.π y' - w₀, hfun y')) ⁻¹' {0}ᶜ with hU'def
      have hcomp : DifferentiableOn ℂ (fun y' => Q (S.π y' - w₀, hfun y')) N :=
        hQd.comp ((S.π.differentiable.differentiableOn.sub_const w₀).prodMk
          (hhd.mono fun y hy => hy.2.1)) fun y hy => hNB y hy
      have hU'o : IsOpen U' := hcomp.continuousOn.isOpen_inter_preimage hNo isOpen_compl_singleton
      have hyU' : y ∈ U' := by
        refine ⟨hyN, ?_⟩
        show Q (S.π y - w₀, hfun y) ≠ 0
        rw [ht, hQ0]; exact hcz'
      have hdh : ∀ y' ∈ O₁, HasFDerivAt hfun
          (innerSL ℂ u - (fderiv ℂ k (S.π y')).comp S.π) y' := by
        intro y' hy'
        have hk' : HasFDerivAt k (fderiv ℂ k (S.π y')) (S.π y') :=
          (hk.differentiableAt (hWo.mem_nhds (hO₁W y' hy'))).hasFDerivAt
        exact (innerSL ℂ u).hasFDerivAt.sub (hk'.comp y' S.π.hasFDerivAt)
      have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
      let P' : RegularPresentation g y :=
        { U := U'
          isOpen := hU'o
          mem := hyU'
          m := a
          m_pos := hapos
          h := hfun
          v := fun y' => Q (S.π y' - w₀, hfun y')
          h_diff := hhd.mono fun y' hy' => hy'.1.2.1
          v_diff := hcomp.mono fun y' hy' => hy'.1
          h_zero := ht
          dh_ne := by
            intro y' hy' h0
            have h1 := (hdh y' hy'.1.2.1).fderiv
            have := congrArg (fun L : V →L[ℂ] ℂ => L u) (h1.symm.trans h0)
            simp [S.π_u] at this
            rw [this, norm_zero] at hu
            exact zero_ne_one hu
          v_ne := fun y' hy' => hy'.2
          eq := by
            intro y' hy'
            have h1 := hFQ _ (hNB y' hy'.1)
            rw [show F (S.π y' - w₀, hfun y') = g y' by simp only [hFdef]; rw [hΨy y' hy'.1]] at h1
            rw [h1, mul_comm] }
      apply hbad
      rw [P'.mem_transverseLocus_iff hyU' hgy u]
      have h1 := (hdh y hyN.2.1).fderiv
      show fderiv ℂ hfun y u ≠ 0
      rw [h1]
      simp only [sub_apply, innerSL_apply_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply, S.π_u, map_zero, sub_zero, huu]
      exact one_ne_zero
  refine ⟨N, hNo.mem_nhds hy₀N, measure_mono_null hsub ?_⟩
  rw [Set.image_add_left, measure_preimage_add]
  exact hZc

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- A set whose points all have neighbourhoods with null image has null image. -/
theorem measure_image_null_of_local {T : Set V} (p : V → E)
    (h : ∀ y ∈ T, ∃ N ∈ 𝓝 y, μ (p '' (N ∩ T)) = 0) : μ (p '' T) = 0 := by
  have : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
  have : SecondCountableTopology V := secondCountable_of_proper
  classical
  choose! N hN hnull using h
  obtain ⟨t, htT, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := N) (s := T) fun y hy => mem_nhdsWithin_of_mem_nhds (hN y hy)
  have hsub : p '' T ⊆ ⋃ y ∈ t, p '' (N y ∩ T) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion₂.mpr ⟨y, hy, x, ⟨hxy, hx⟩, rfl⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff htc).mpr fun y hy => hnull y (htT hy))

/-- **LP4: almost every line parallel to `u` meets the zero set of `g` only at transverse regular
points.**  The non-transverse zeros of `g` in `Ω` project to a null subset of `E`. -/
theorem measure_image_bad_eq_zero {g : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0) {u : V}
    (hu : ‖u‖ = 1) (S : Splitting u E) :
    μ (S.π '' {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u}) = 0 := by
  set T : Set V := {y | y ∈ Ω ∧ g y = 0 ∧ y ∉ transverseLocus g u}
  have hT : T ⊆ (T ∩ infiniteOrderSet g Ω u) ∪ ⋃ j : ℕ, badStratum g Ω u j := by
    intro y hy
    rcases eq_or_ne (analyticOrderAt (fun s : ℂ => g (y + s • u)) 0) ⊤ with htop | hne
    · exact Or.inl ⟨hy, hy.1, htop⟩
    · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
      exact Or.inr (mem_iUnion.mpr ⟨j, hy.1, hy.2.1, hj.symm, hy.2.2⟩)
  refine measure_mono_null (image_mono hT) ?_
  rw [image_union, image_iUnion]
  refine measure_union_null ?_ (measure_iUnion_null fun j => ?_)
  · refine measure_image_null_of_local μ S.π fun y hy => ?_
    obtain ⟨N, hN, hnull⟩ := exists_nhds_null_top μ hΩ hg hg0 S hy.2.1
    exact ⟨N, hN, measure_mono_null (image_mono (inter_subset_inter_right _ inter_subset_right))
      hnull⟩
  · refine measure_image_null_of_local μ S.π fun y hy => ?_
    exact exists_nhds_null_nat μ hΩ hg hu S hy.1 hy.2.1 hy.2.2.1

end Null

end Hironaka.DivisorSingularProjection
