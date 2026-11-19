import Hironaka.Analytic.HiepSliceLemma
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false

/-!
# Normal families of holomorphic functions on open sets of `ℂⁿ`

Montel's theorem in the form used by limiting arguments for weighted L² extensions: a
sequence of holomorphic functions which, near every point, is eventually defined and
uniformly bounded has a subsequence converging pointwise (indeed locally uniformly) to a
holomorphic function.  The ingredients are the Cauchy estimate for the complex derivative
along complex lines, equicontinuity, a diagonal subsequence on a countable dense set, and
the derivative-limit theorem for locally uniformly convergent derivatives.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka

noncomputable section

open Hironaka

variable {n : ℕ}

/-- **Cauchy estimate** in several variables: a holomorphic function bounded by `M` on a
ball of radius `r` has complex derivative of norm at most `M / r` at the centre. -/
theorem _root_.Hironaka.HolomorphicNormalFamilies.norm_fderiv_le_of_forall_norm_le {F : ComplexModel n → ℂ} {x : ComplexModel n}
    {r M : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball x r))
    (hM : ∀ y ∈ ball x r, ‖F y‖ ≤ M) :
    ‖fderiv ℂ F x‖ ≤ M / r := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hFx : HasFDerivAt F (fderiv ℂ F x) x :=
    (hF.differentiableAt (isOpen_ball.mem_nhds hx)).hasFDerivAt
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have key : ∀ r' ∈ Ioo 0 r, ‖fderiv ℂ F x v‖ ≤ M * ‖v‖ / r' := by
    rintro r' ⟨hr'0, hr'r⟩
    set g : ℂ → ℂ := fun z => F (x + z • v)
    have hline : ∀ z : ℂ, HasDerivAt (fun w : ℂ => x + w • v) v z := fun z => by
      simpa using ((hasDerivAt_id z).smul_const v).const_add x
    have hsub : closedBall (0 : ℂ) (r' / ‖v‖) ⊆ (fun w : ℂ => x + w • v) ⁻¹' ball x r := by
      intro z hz
      simp only [mem_closedBall, dist_zero_right] at hz
      simp only [mem_preimage, mem_ball, dist_self_add_left, norm_smul]
      calc ‖z‖ * ‖v‖ ≤ r' / ‖v‖ * ‖v‖ := by gcongr
        _ = r' := div_mul_cancel₀ _ hv'.ne'
        _ < r := hr'r
    have hgd : DifferentiableOn ℂ g ((fun w : ℂ => x + w • v) ⁻¹' ball x r) :=
      hF.comp (fun z _ => (hline z).differentiableAt.differentiableWithinAt) fun z hz => hz
    have hderiv : deriv g 0 = fderiv ℂ F x v := by
      have := hFx.comp_hasDerivAt_of_eq (0 : ℂ) (hline 0) (by simp)
      exact this.deriv
    have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hr'0 hv')
      (hgd.diffContOnCl_ball hsub) fun z hz => hM _ (hsub (sphere_subset_closedBall hz))
    rw [hderiv] at hbound
    calc ‖fderiv ℂ F x v‖ ≤ M / (r' / ‖v‖) := hbound
      _ = M * ‖v‖ / r' := by field_simp
  have hlim : Tendsto (fun r' : ℝ => M * ‖v‖ / r') (𝓝[<] r) (𝓝 (M * ‖v‖ / r)) :=
    ((continuousAt_const.div continuousAt_id hr.ne').tendsto).mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT hr) key)
  calc ‖fderiv ℂ F x v‖ ≤ M * ‖v‖ / r := this
    _ = M / r * ‖v‖ := by ring

/-- A holomorphic function bounded by `M` on `ball x r` is `M / (r / 2)`-Lipschitz on
`ball x (r / 2)`. -/
theorem norm_sub_le_of_forall_norm_le {F : ComplexModel n → ℂ} {x : ComplexModel n} {r M : ℝ}
    (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball x r)) (hM : ∀ y ∈ ball x r, ‖F y‖ ≤ M)
    {y z : ComplexModel n} (hy : y ∈ ball x (r / 2)) (hz : z ∈ ball x (r / 2)) :
    ‖F y - F z‖ ≤ M / (r / 2) * ‖y - z‖ := by
  have hsub : ∀ w ∈ ball x (r / 2), ball w (r / 2) ⊆ ball x r := fun w hw =>
    ball_subset_ball' (by rw [mem_ball] at hw; linarith)
  have hd : ∀ w ∈ ball x (r / 2), DifferentiableAt ℂ F w := fun w hw =>
    hF.differentiableAt (isOpen_ball.mem_nhds (hsub w hw (mem_ball_self (half_pos hr))))
  have hb : ∀ w ∈ ball x (r / 2), ‖fderiv ℂ F w‖ ≤ M / (r / 2) := fun w hw =>
    _root_.Hironaka.HolomorphicNormalFamilies.norm_fderiv_le_of_forall_norm_le (half_pos hr) (hF.mono (hsub w hw))
      fun u hu => hM u (hsub w hw hu)
  exact (convex_ball x (r / 2)).norm_image_sub_le_of_norm_fderiv_le hd hb hz hy

/-- Cauchy estimate for the difference of two holomorphic functions which are `ε`-close. -/
theorem norm_fderiv_sub_le_of_forall_norm_sub_le {F G : ComplexModel n → ℂ} {x : ComplexModel n}
    {r ε : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball x r))
    (hG : DifferentiableOn ℂ G (ball x r)) (hε : ∀ y ∈ ball x r, ‖F y - G y‖ ≤ ε)
    {y : ComplexModel n} (hy : y ∈ ball x (r / 2)) :
    ‖fderiv ℂ F y - fderiv ℂ G y‖ ≤ ε / (r / 2) := by
  have hsub : ball y (r / 2) ⊆ ball x r :=
    ball_subset_ball' (by rw [mem_ball] at hy; linarith)
  have hyr : y ∈ ball x r := hsub (mem_ball_self (half_pos hr))
  rw [← fderiv_sub (hF.differentiableAt (isOpen_ball.mem_nhds hyr))
    (hG.differentiableAt (isOpen_ball.mem_nhds hyr))]
  exact _root_.Hironaka.HolomorphicNormalFamilies.norm_fderiv_le_of_forall_norm_le (half_pos hr) ((hF.sub hG).mono hsub)
    fun u hu => hε u (hsub hu)

/-- A sequence of functions which is eventually bounded at each point of a countable set has a
subsequence converging at each point of that set. -/
theorem exists_strictMono_tendsto_of_eventually_norm_le {α : Type*} {D : Set α}
    (hD : D.Countable) (f : ℕ → α → ℂ) (hb : ∀ d ∈ D, ∃ M : ℝ, ∀ᶠ i in atTop, ‖f i d‖ ≤ M) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ d ∈ D, ∃ c, Tendsto (fun i => f (ψ i) d) atTop (𝓝 c) := by
  choose! M hM using hb
  have : Countable D := hD.to_subtype
  let v : ℕ → D → ℂ := fun i d => if ‖f i d‖ ≤ M d then f i d else 0
  have hK : IsCompact (univ.pi fun d : D => closedBall (0 : ℂ) |M d|) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hv : ∀ i, v i ∈ univ.pi fun d : D => closedBall (0 : ℂ) |M d| := by
    intro i d _
    simp only [v, mem_closedBall, dist_zero_right]
    split_ifs with h
    · exact h.trans (le_abs_self _)
    · simp
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hv
  refine ⟨ψ, hψ, fun d hd => ⟨a ⟨d, hd⟩, ?_⟩⟩
  have h1 : Tendsto (fun i => v (ψ i) ⟨d, hd⟩) atTop (𝓝 (a ⟨d, hd⟩)) :=
    tendsto_pi_nhds.1 hlim ⟨d, hd⟩
  refine h1.congr' ?_
  filter_upwards [hψ.tendsto_atTop.eventually (hM d hd)] with i hi
  simp [v, hi]

/-- An eventually equi-Lipschitz sequence which is Cauchy on a dense set is uniformly Cauchy on
compact sets. -/
theorem uniformCauchySeqOn_of_eventually_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f : ℕ → X → ℂ} {K S D : Set X} (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S)
    (hSD : S ⊆ closure D) {L : ℝ}
    (hL : ∀ᶠ i in atTop, ∀ y ∈ S, ∀ z ∈ S, dist (f i y) (f i z) ≤ L * dist y z)
    (hD : ∀ d ∈ D, CauchySeq fun i => f i d) :
    UniformCauchySeqOn f atTop K := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set δ := ε / (3 * (|L| + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hLδ : |L| * δ < ε / 3 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg L]
  have hcover : K ⊆ ⋃ d ∈ D ∩ S, ball d δ := by
    intro y hy
    obtain ⟨η, hη, hηS⟩ := Metric.isOpen_iff.1 hS y (hKS hy)
    obtain ⟨d, hd, hyd⟩ := Metric.mem_closure_iff.1 (hSD (hKS hy)) (min δ η) (lt_min hδ0 hη)
    refine mem_iUnion₂.2 ⟨d, ⟨hd, hηS ?_⟩, ?_⟩
    · rw [mem_ball, dist_comm]; exact hyd.trans_le (min_le_right _ _)
    · exact hyd.trans_le (min_le_left _ _)
  obtain ⟨t, htDS, htfin, hKt⟩ := hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  have hct : ∀ᶠ p : ℕ × ℕ in atTop, ∀ d ∈ t, dist (f p.1 d) (f p.2 d) < ε / 3 := by
    rw [htfin.eventually_all]
    intro d hd
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hD d (htDS hd).1) (ε / 3) (by positivity)
    exact eventually_atTop_prod_self'.2 ⟨N, fun m hm k hk => hN m hm k hk⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop_prod_self'.1 hct
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hL
  refine ⟨max N₁ N₂, fun m hm k hk y hy => ?_⟩
  obtain ⟨d, hdt, hyd⟩ := mem_iUnion₂.1 (hKt hy)
  have hdS := (htDS hdt).2
  have hyS := hKS hy
  have h1 := hN₂ m (le_of_max_le_right hm) y hyS d hdS
  have h2 := hN₂ k (le_of_max_le_right hk) d hdS y hyS
  have h3 := hN₁ m (le_of_max_le_left hm) k (le_of_max_le_left hk) d hdt
  have hyd' : dist y d < δ := hyd
  have hLd : L * dist y d ≤ |L| * δ :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hyd'.le (abs_nonneg L))
  rw [dist_comm d y] at h2
  calc dist (f m y) (f k y) ≤ dist (f m y) (f m d) + dist (f m d) (f k d) + dist (f k d) (f k y) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- Local step of Montel's theorem: a locally eventually bounded sequence of holomorphic
functions which is Cauchy on a dense subset is uniformly Cauchy near every point. -/
theorem exists_uniformCauchySeqOn_ball_of_eventually_bounded {U D : Set (ComplexModel n)}
    (hU : IsOpen U) {f : ℕ → ComplexModel n → ℂ}
    (hf : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (f i) (ball x r) ∧ ∀ y ∈ ball x r, ‖f i y‖ ≤ M)
    (hUD : U ⊆ closure D) (hD : ∀ d ∈ D, CauchySeq fun i => f i d)
    {x : ComplexModel n} (hx : x ∈ U) :
    ∃ R > 0, ball x R ⊆ U ∧ (∀ᶠ i in atTop, DifferentiableOn ℂ (f i) (ball x R)) ∧
      UniformCauchySeqOn f atTop (ball x R) := by
  obtain ⟨r, hr, M, hev⟩ := hf x hx
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.1 hU x hx
  set R := min r η
  have hR : 0 < R := lt_min hr hη
  have hRr : ball x R ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have hRη : R ≤ η := min_le_right _ _
  have hev' : ∀ᶠ i in atTop,
      DifferentiableOn ℂ (f i) (ball x R) ∧ ∀ y ∈ ball x R, ‖f i y‖ ≤ M :=
    hev.mono fun i hi => ⟨hi.1.mono hRr, fun y hy => hi.2 y (hRr hy)⟩
  refine ⟨R / 4, by positivity, (ball_subset_ball (by linarith)).trans hηU,
    hev'.mono fun i hi => hi.1.mono (ball_subset_ball (by linarith)), ?_⟩
  refine (uniformCauchySeqOn_of_eventually_lipschitz (L := M / (R / 2)) (S := ball x (R / 2))
    (isCompact_closedBall x (R / 4)) isOpen_ball
    (closedBall_subset_ball (by linarith)) ((ball_subset_ball (by linarith : R / 2 ≤ η)).trans
      (hηU.trans hUD)) ?_ hD).mono ball_subset_closedBall
  exact hev'.mono fun i hi y hy z hz => by
    rw [dist_eq_norm, dist_eq_norm]
    exact norm_sub_le_of_forall_norm_le hR hi.1 hi.2 hy hz

/-- **Montel's theorem.**  If near every point of the open set `U` the functions `F i` are
eventually holomorphic and uniformly bounded, a subsequence converges locally uniformly on
`U` to a holomorphic function. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded
    {U : Set (ComplexModel n)} (hU : IsOpen U) (F : ℕ → ComplexModel n → ℂ)
    (hF : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (F i) (ball x r) ∧ ∀ y ∈ ball x r, ‖F i y‖ ≤ M) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel n → ℂ), StrictMono ψ ∧ DifferentiableOn ℂ G U ∧
      TendstoLocallyUniformlyOn (fun i => F (ψ i)) G atTop U := by
  obtain ⟨D, hDU, hDc, hUD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace U).exists_countable_dense_subset
  obtain ⟨ψ, hψ, hψD⟩ := exists_strictMono_tendsto_of_eventually_norm_le hDc F fun d hd => by
    obtain ⟨r, hr, M, h⟩ := hF d (hDU hd)
    exact ⟨M, h.mono fun i hi => hi.2 d (mem_ball_self hr)⟩
  set f : ℕ → ComplexModel n → ℂ := fun i => F (ψ i)
  have hf : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (f i) (ball x r) ∧ ∀ y ∈ ball x r, ‖f i y‖ ≤ M := fun x hx => by
    obtain ⟨r, hr, M, h⟩ := hF x hx
    exact ⟨r, hr, M, hψ.tendsto_atTop.eventually h⟩
  have hfD : ∀ d ∈ D, CauchySeq fun i => f i d := fun d hd =>
    (hψD d hd).choose_spec.cauchySeq
  choose! R hR hRU hRd hRc using fun x (hx : x ∈ U) =>
    exists_uniformCauchySeqOn_ball_of_eventually_bounded hU hf hUD hfD hx
  set G : ComplexModel n → ℂ := fun y => limUnder atTop fun i => f i y
  have hG : ∀ y ∈ U, Tendsto (fun i => f i y) atTop (𝓝 (G y)) := fun y hy =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      ((hRc y hy).cauchySeq (mem_ball_self (hR y hy))))
  have hunif : ∀ x ∈ U, TendstoUniformlyOn f G atTop (ball x (R x)) := fun x hx =>
    (hRc x hx).tendstoUniformlyOn_of_tendsto fun y hy => hG y (hRU x hx hy)
  refine ⟨ψ, G, hψ, fun x hx => ?_, tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx =>
    ⟨ball x (R x), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hR x hx)), hunif x hx⟩⟩
  set ρ := R x
  have hρ : 0 < ρ := hR x hx
  have hder : UniformCauchySeqOn (fun i => fderiv ℂ (f i)) atTop (ball x (ρ / 2)) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hRd x hx)
    obtain ⟨N₂, hN₂⟩ := Metric.uniformCauchySeqOn_iff.1 (hRc x hx) (ε * (ρ / 2) / 2)
      (by positivity)
    refine ⟨max N₁ N₂, fun m hm k hk y hy => ?_⟩
    rw [dist_eq_norm]
    calc ‖fderiv ℂ (f m) y - fderiv ℂ (f k) y‖ ≤ ε * (ρ / 2) / 2 / (ρ / 2) :=
          norm_fderiv_sub_le_of_forall_norm_sub_le hρ (hN₁ m (le_of_max_le_left hm))
            (hN₁ k (le_of_max_le_left hk)) (fun z hz => by
              rw [← dist_eq_norm]
              exact (hN₂ m (le_of_max_le_right hm) k (le_of_max_le_right hk) z hz).le) hy
      _ < ε := by
        have : ε * (ρ / 2) / 2 / (ρ / 2) = ε / 2 := by field_simp
        linarith
  set g' : ComplexModel n → ComplexModel n →L[ℂ] ℂ :=
    fun y => limUnder atTop fun i => fderiv ℂ (f i) y
  have hderU : TendstoUniformlyOn (fun i => fderiv ℂ (f i)) g' atTop (ball x (ρ / 2)) :=
    hder.tendstoUniformlyOn_of_tendsto fun y hy =>
      tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hder.cauchySeq hy))
  have hGx : HasFDerivAt G (g' x) x := by
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (f := f) (f' := fun i => fderiv ℂ (f i))
      (hderU.tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.2 (ball_mem_nhds x (half_pos hρ)))) ?_ ?_
    · filter_upwards [(hRd x hx).prod_mk (ball_mem_nhds x hρ)] with p hp
      exact (hp.1.differentiableAt (isOpen_ball.mem_nhds hp.2)).hasFDerivAt
    · filter_upwards [ball_mem_nhds x hρ] with y hy
      exact hG y (hRU x hx hy)
  exact hGx.differentiableAt.differentiableWithinAt

end

end Hironaka
