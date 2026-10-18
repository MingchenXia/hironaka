/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.DimensionMonotone
import Hironaka.Analytic.GenericSections
import Hironaka.Analytic.AnalyticCodimTwoStratification
import Hironaka.Analytic.RegularPatchNeighborhood

set_option autoImplicit false

/-!
# Compact analytic subsets of `ℂᴺ` are finite

Blueprint `rem:compact-analytic-finite` (Demailly, *Complex analytic and differential geometry*,
II.5.9), step M5 of the route to Remmert's proper mapping theorem (`blueprint/src/remmert.tex`).

* `exists_level_piece_of_param` (maximum principle on a parametrized germ): let `C ⊆ ℂⁿ` carry
  parametrization data `P` with parametrizing sets `S`, and `ℓ` a linear form with `Re ℓ ≤ 0` on
  `C` near `0`.  The canonical coefficient `σ(x) = ∑_{y ∈ fibre x} ℓ(y)` extends holomorphically
  across the discriminant (`GermParametrizationData.exists_extension_coeff_fibrePoly`), has
  `Re σ ≤ 0` near `0` and `σ(0) = 0` (the fibres shrink to `0`), so `Re σ ≡ 0` near `0` by the
  maximum principle; every summand then has real part `0`, and on a local holomorphic section `ℓ`
  has constant real part, hence is constant.  Conclusion: arbitrarily near `0` there is a regular
  point `y` of `C` of dimension `P.dim` near which `ℓ ≡ ℓ(y)` on `C`.
* `exists_level_regularAtDim_germ`: the same for an analytic germ `T` at `0` that is not reduced to
  `{0}`, through its irreducible decomposition (a component of positive dimension exists).
* `exists_level_regularAtDim_of_isMaxOn`: on `ℂᴺ`, if `Re λ` restricted to an analytic set `K` has a
  local maximum at a non-isolated point, some level set `K ∩ {λ = c}` has a regular point of
  positive dimension (monotonicity of dimension, `DimensionMonotone`).
* `regularAtDim_eq_zero_of_isCompact`: a compact analytic subset of `ℂᴺ` has only regular points
  of dimension `0` (descending induction on the number of fixed coordinates, applied to the
  closure of the regular points of positive dimension and the coordinate `z_{j+1}`).
* `finite_of_isCompact`: a compact analytic subset of `ℂᴺ` is finite (points of local dimension `0`
  are isolated, `AnalyticDimensionBasics.not_accPt_of_locDimLE_zero`);
  `isComplexAnalyticSubset_of_isCompact` turns "compact, with local equations at its own points"
  into "analytic", which covers compact analytic subsets of open subsets of `ℂᴺ`.

Sorry-free.
-/

open Set Filter Metric Polynomial
open scoped Topology

noncomputable section

namespace Hironaka.CompactAnalyticFinite

open Hironaka.RegularLocusDense AnalyticGermDecomposition GermParametrization
  GermParametrizationData
  GermComponentDimension RegularPointDimension AnalyticDimensionBasics DimensionMonotone

variable {n : ℕ}

/-! ### The maximum principle on a parametrized germ -/

section Param

variable {C : Set (ComplexModel n)} {P : ParametrizationData C}

/-- The coefficient of `T^{q-1}` of the canonical polynomial is minus the fibre sum. -/
theorem coeff_fibrePoly_pred (S : SetsData P) (ℓ : ComplexModel n → ℂ)
    {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) :
    (fibrePoly S ℓ x).coeff (P.deg - 1) =
      -∑ y ∈ (S.finite_fibre x hx hd).toFinset, ℓ y := by
  rw [fibrePoly_eq S ℓ hx hd, ← card_toFinset_fibre S hx hd]
  exact prod_X_sub_C_coeff_card_pred _ _ (by rw [card_toFinset_fibre S hx hd]; exact P.deg_pos)

/-- Points of `C ∩ Δ` over a small base point are small. -/
theorem exists_norm_lt_of_small (S : SetsData P) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ z ∈ C ∩ polydisc n P.dim S.r₁ S.r₂,
      ‖coordinateProjection n P.dim z‖ < η → ‖z‖ < ε := by
  set ε' := ε / ((n : ℝ) + 2) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hprod : ((n : ℝ) + 1) * ε' < ε := by
    have h2 : ε' * ((n : ℝ) + 2) = ε := by rw [hε']; field_simp
    nlinarith
  obtain ⟨η, hη, hηs⟩ := S.small ε' hε'0
  refine ⟨min η ε', lt_min hη hε'0, fun z hz hzη => ?_⟩
  have hpoly : z ∈ polydisc n P.dim ε' ε' :=
    ⟨hzη.trans_le (min_le_right _ _),
      fun k hk => hηs z hz (hzη.trans_le (min_le_left _ _)) k hk⟩
  have h := polydisc_subset_ball (n := n) hε'0 hpoly
  rw [mem_ball_zero_iff] at h
  linarith

/-- **A holomorphic function with real part `0` near a point is constant near it.** -/
theorem eventually_eq_of_re_eq_zero {d : ℕ} {φ : ComplexModel d → ℂ} {x₀ : ComplexModel d}
    (hφ : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ φ x) (hre : ∀ᶠ x in 𝓝 x₀, (φ x).re = 0) :
    ∀ᶠ x in 𝓝 x₀, φ x = φ x₀ := by
  have hre0 : (φ x₀).re = 0 := hre.self_of_nhds
  have hexp : ∀ᶠ x in 𝓝 x₀, Complex.exp (φ x) = Complex.exp (φ x₀) := by
    refine Complex.eventually_eq_of_isLocalMax_norm (hφ.mono fun x hx => hx.cexp) ?_
    filter_upwards [hre] with x hx
    simp [Complex.norm_exp, hx, hre0]
  have hc : ContinuousAt φ x₀ := hφ.self_of_nhds.continuousAt
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖φ x - φ x₀‖ < 1 := by
    have h := hc.eventually (Metric.ball_mem_nhds (φ x₀) one_pos)
    filter_upwards [h] with x hx
    rwa [dist_eq_norm] at hx
  filter_upwards [hexp, hnear] with x hx hn
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hx
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    have h2 : ‖φ x - φ x₀‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [hk, add_sub_cancel_left, norm_mul, Complex.norm_intCast, norm_mul, norm_mul,
        Complex.norm_I, Complex.norm_real, Complex.norm_two, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      ring
    have h3 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.two_le_pi]
    nlinarith [abs_nonneg (k : ℝ)]
  rw [hk, hk0]
  simp

/-- **The maximum principle on a parametrized germ.**  If `Re ℓ ≤ 0` on `C ∩ Δ` near `0`, then
arbitrarily near `0` there is a regular point `y` of `C ∩ Δ` of dimension `P.dim` and an open `W ∋ y`
on which `ℓ ≡ ℓ(y)` along `C ∩ Δ`. -/
theorem exists_level_piece_of_param (S : SetsData P) (ℓ : ComplexModel n →L[ℂ] ℂ) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hle : ∀ z ∈ C ∩ polydisc n P.dim S.r₁ S.r₂, ‖z‖ < ρ → (ℓ z).re ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ComplexModel n, ‖y‖ < ε ∧ ∃ W : Set (ComplexModel n), IsOpen W ∧ y ∈ W ∧
      W ⊆ ball 0 ε ∧ (∀ z ∈ C ∩ polydisc n P.dim S.r₁ S.r₂ ∩ W, ℓ z = ℓ y) ∧
      RegularAtDim (n := n) (M := ComplexModel n)
        (C ∩ polydisc n P.dim S.r₁ S.r₂ ∩ W) y P.dim := by
  classical
  set π := coordinateProjection n P.dim with hπ
  set Δ := polydisc n P.dim S.r₁ S.r₂ with hΔ
  -- the extended canonical coefficient `-H`
  have hM : ∀ z ∈ Δ, ‖ℓ z‖ ≤ ‖ℓ‖ * P.rad := fun z hz => by
    refine (ℓ.le_opNorm z).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (mem_ball_zero_iff.1 (S.polydisc_subset hz)).le
  obtain ⟨F, hF⟩ := exists_extension_coeff_fibrePoly S ℓ
    (mul_nonneg (norm_nonneg _) P.rad_pos.le) hM (P.deg - 1)
  set H : ComplexModel P.dim → ℂ := fun x => -F x with hH
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.eventually_nhds_iff_ball.1 hF
  obtain ⟨η₁, hη₁, hη₁s⟩ := exists_norm_lt_of_small S hρ
  set r := min (min r₀ η₁) (min S.r₁ P.rad) with hr
  have hr0 : 0 < r := lt_min (lt_min hr₀ hη₁) (lt_min S.r₁_pos P.rad_pos)
  have hrr₀ : r ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hrη₁ : r ≤ η₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hrr₁ : r ≤ S.r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrrad : r ≤ P.rad := (min_le_right _ _).trans (min_le_right _ _)
  have hdiff : ∀ x ∈ ball (0 : ComplexModel P.dim) r, DifferentiableAt ℂ H x := fun x hx =>
    (hr₀s x (ball_subset_ball hrr₀ hx)).1.neg
  -- on the good set, `H` is the fibre sum
  have hHsum : ∀ x (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0), ‖x‖ < r₀ →
      H x = ∑ y ∈ (S.finite_fibre x hx hd).toFinset, ℓ y := fun x hx hd hxr => by
    have h := (hr₀s x (mem_ball_zero_iff.2 hxr)).2 hd
    simp only [hH, h, coeff_fibrePoly_pred S ℓ hx hd, neg_neg]
  -- points of the fibre over `x`
  have hfib : ∀ x (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0),
      ∀ y ∈ (S.finite_fibre x hx hd).toFinset, y ∈ C ∩ Δ ∧ π y = x := fun x hx hd y hy => by
    have h : y ∈ C ∩ Δ ∩ π ⁻¹' {x} := (Set.Finite.mem_toFinset (S.finite_fibre x hx hd)).1 hy
    exact ⟨h.1, h.2⟩
  -- `Re H ≤ 0` off the discriminant
  have hreD : ∀ x ∈ ball (0 : ComplexModel P.dim) r, P.disc x ≠ 0 → (H x).re ≤ 0 := by
    intro x hx hd
    have hxn := mem_ball_zero_iff.1 hx
    rw [hHsum x (hxn.trans_le hrr₁) hd (hxn.trans_le hrr₀), Complex.re_sum]
    refine Finset.sum_nonpos fun y hy => ?_
    obtain ⟨hyC, hyx⟩ := hfib x (hxn.trans_le hrr₁) hd y hy
    exact hle y hyC (hη₁s y hyC (by rw [hyx]; exact hxn.trans_le hrη₁))
  -- density of the complement of the discriminant
  have hdense : ball (0 : ComplexModel P.dim) r ⊆
      closure (ball (0 : ComplexModel P.dim) r \ P.disc ⁻¹' {0}) :=
    RiemannExtension.dense_compl_zeroSet isOpen_ball (convex_ball _ _).isPreconnected
      (P.differentiableOn_disc.mono (ball_subset_ball hrrad)) (mem_ball_self hr0)
      P.disc_not_eventually_zero
  -- `Re H ≤ 0` on the ball
  have hre : ∀ x ∈ ball (0 : ComplexModel P.dim) r, (H x).re ≤ 0 := by
    intro x hx
    have hcl := hdense hx
    have := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have hc : ContinuousAt (fun x => (H x).re) x :=
      Complex.continuous_re.continuousAt.comp (hdiff x hx).continuousAt
    exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun y (hy : y ∈ ball (0 : ComplexModel P.dim) r \ P.disc ⁻¹' {0}) =>
        hreD y hy.1 hy.2)
  -- `H 0 = 0`: the fibres shrink to `0`
  have hH0 : H 0 = 0 := by
    have hcl := hdense (mem_ball_self hr0)
    have := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto H (𝓝[ball (0 : ComplexModel P.dim) r \ P.disc ⁻¹' {0}] 0) (𝓝 (H 0)) :=
      (hdiff 0 (mem_ball_self hr0)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[ball (0 : ComplexModel P.dim) r \ P.disc ⁻¹' {0}] 0) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro δ hδ
      set c : ℝ := (P.deg : ℝ) * ‖ℓ‖ + 1 with hc
      have hc0 : 0 < c := by positivity
      obtain ⟨η, hη, hηs⟩ := exists_norm_lt_of_small S (div_pos hδ hc0)
      refine ⟨η, hη, fun x hx hxd => ?_⟩
      rw [dist_zero_right] at hxd ⊢
      have hxn := mem_ball_zero_iff.1 hx.1
      have hd : P.disc x ≠ 0 := hx.2
      rw [hHsum x (hxn.trans_le hrr₁) hd (hxn.trans_le hrr₀)]
      have hb : ∀ y ∈ (S.finite_fibre x (hxn.trans_le hrr₁) hd).toFinset,
          ‖ℓ y‖ ≤ ‖ℓ‖ * (δ / c) := fun y hy => by
        obtain ⟨hyC, hyx⟩ := hfib x (hxn.trans_le hrr₁) hd y hy
        refine (ℓ.le_opNorm y).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (hηs y hyC (by rw [hyx]; exact hxd)).le
      calc ‖∑ y ∈ (S.finite_fibre x (hxn.trans_le hrr₁) hd).toFinset, ℓ y‖
          ≤ ∑ y ∈ (S.finite_fibre x (hxn.trans_le hrr₁) hd).toFinset, ‖ℓ‖ * (δ / c) :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
        _ = (P.deg : ℝ) * ‖ℓ‖ * (δ / c) := by
            rw [Finset.sum_const, card_toFinset_fibre S (hxn.trans_le hrr₁) hd, nsmul_eq_mul, mul_assoc]
        _ < δ := by
            have h3 : (P.deg : ℝ) * ‖ℓ‖ * (δ / c) = ((P.deg : ℝ) * ‖ℓ‖) / c * δ := by ring
            have h4 : ((P.deg : ℝ) * ‖ℓ‖) / c < 1 := by
              rw [div_lt_one hc0]; linarith
            rw [h3]
            nlinarith
    exact tendsto_nhds_unique h1 h2
  -- the maximum principle: `Re H ≡ 0` near `0`
  have hmax : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), Complex.exp (H x) = Complex.exp (H 0) := by
    refine Complex.eventually_eq_of_isLocalMax_norm ?_ ?_
    · filter_upwards [ball_mem_nhds (0 : ComplexModel P.dim) hr0] with x hx
      exact (hdiff x hx).cexp
    · filter_upwards [ball_mem_nhds (0 : ComplexModel P.dim) hr0] with x hx
      simp only [Function.comp_apply, Complex.norm_exp, hH0, Complex.zero_re, Real.exp_zero]
      exact Real.exp_le_one_iff.2 (hre x hx)
  have hre0 : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), (H x).re = 0 := by
    filter_upwards [hmax] with x hx
    have h := congrArg (fun z => ‖z‖) hx
    simp only [Complex.norm_exp, hH0, Complex.zero_re, Real.exp_zero] at h
    exact Real.exp_eq_one_iff _ |>.1 h
  obtain ⟨r₁', hr₁', hr₁'s⟩ := Metric.eventually_nhds_iff_ball.1 hre0
  -- every fibre point over a good base point near `0` has `Re ℓ = 0`
  obtain ⟨ηε, hηε, hηεs⟩ := exists_norm_lt_of_small S hε
  set r₂ := min (min r r₁') ηε with hr₂
  have hr₂0 : 0 < r₂ := lt_min (lt_min hr0 hr₁') hηε
  have hr₂r : r₂ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hr₂r₁' : r₂ ≤ r₁' := (min_le_left _ _).trans (min_le_right _ _)
  have hr₂ε : r₂ ≤ ηε := min_le_right _ _
  have hzero : ∀ x ∈ ball (0 : ComplexModel P.dim) r₂, ∀ (hd : P.disc x ≠ 0),
      ∀ y ∈ C ∩ Δ, π y = x → (ℓ y).re = 0 := by
    intro x hx hd y hyC hyx
    have hxn := mem_ball_zero_iff.1 hx
    have hxr := hxn.trans_le hr₂r
    have hsum := hr₁'s x (ball_subset_ball hr₂r₁' hx)
    rw [hHsum x (hxr.trans_le hrr₁) hd (hxr.trans_le hrr₀), Complex.re_sum] at hsum
    have hnp : ∀ y' ∈ (S.finite_fibre x (hxr.trans_le hrr₁) hd).toFinset, (ℓ y').re ≤ 0 :=
      fun y' hy' => by
        obtain ⟨hy'C, hy'x⟩ := hfib x (hxr.trans_le hrr₁) hd y' hy'
        exact hle y' hy'C (hη₁s y' hy'C (by rw [hy'x]; exact hxr.trans_le hrη₁))
    have hymem : y ∈ (S.finite_fibre x (hxr.trans_le hrr₁) hd).toFinset :=
      (Set.Finite.mem_toFinset _).2 ⟨hyC, hyx⟩
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hsum y hymem
  -- a good base point and a point above it
  have hfreq : ∃ᶠ x in 𝓝 (0 : ComplexModel P.dim), P.disc x ≠ 0 :=
    Filter.not_eventually.mp P.disc_not_eventually_zero
  obtain ⟨x₀, hx₀b, hd₀⟩ := (Filter.frequently_iff.mp hfreq) (ball_mem_nhds _ hr₂0)
  have hx₀n := mem_ball_zero_iff.1 hx₀b
  obtain ⟨y₀, hy₀⟩ := nonempty_fibre S ((hx₀n.trans_le hr₂r).trans_le hrr₁) hd₀
  have hy₀C : y₀ ∈ C ∩ Δ := hy₀.1
  have hy₀x : π y₀ = x₀ := hy₀.2
  have hy₀ε : ‖y₀‖ < ε := hηεs y₀ hy₀C (by rw [hy₀x]; exact hx₀n.trans_le hr₂ε)
  -- the local holomorphic section through `y₀`
  obtain ⟨U, V, g, hUo, hVo, hx₀U, hy₀V, -, hUd, hgd, hgπ, hgC, hgsec⟩ :=
    S.local_graph y₀ hy₀C (by rw [hy₀x]; exact hd₀)
  rw [hy₀x] at hx₀U
  have hgy₀ : g x₀ = y₀ := by
    have h := (hgsec y₀ hy₀V hy₀C.1).2
    rwa [hy₀x] at h
  set U₁ := U ∩ ball (0 : ComplexModel P.dim) r₂ with hU₁
  have hU₁o : IsOpen U₁ := hUo.inter isOpen_ball
  have hx₀U₁ : x₀ ∈ U₁ := ⟨hx₀U, hx₀b⟩
  have hφd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ (fun x => ℓ (g x)) x := by
    filter_upwards [hUo.mem_nhds hx₀U] with x hx
    exact ℓ.differentiableAt.comp x (hgd.differentiableAt (hUo.mem_nhds hx))
  have hφre : ∀ᶠ x in 𝓝 x₀, (ℓ (g x)).re = 0 := by
    filter_upwards [hU₁o.mem_nhds hx₀U₁] with x hx
    exact hzero x hx.2 (hUd hx.1).2 (g x) (hgC x hx.1) (hgπ x hx.1)
  have hφc := eventually_eq_of_re_eq_zero hφd hφre
  obtain ⟨U₂, hU₂s, hU₂o, hx₀U₂⟩ := _root_.mem_nhds_iff.1 hφc
  -- the open set `W`
  set W := V ∩ π ⁻¹' U₂ ∩ ball (0 : ComplexModel n) ε with hW
  have hWo : IsOpen W := (hVo.inter (hU₂o.preimage π.continuous)).inter isOpen_ball
  have hy₀W : y₀ ∈ W := ⟨⟨hy₀V, by rw [mem_preimage, hy₀x]; exact hx₀U₂⟩,
    mem_ball_zero_iff.2 hy₀ε⟩
  refine ⟨y₀, hy₀ε, W, hWo, hy₀W, inter_subset_right, ?_, ?_⟩
  · rintro z ⟨hzCΔ, ⟨hzV, hzU₂⟩, -⟩
    obtain ⟨-, hgz⟩ := hgsec z hzV hzCΔ.1
    have h := hU₂s hzU₂
    simp only [mem_ofPred_eq] at h
    rw [← hgz, h, hgy₀]
  · refine regularAtDim_of_inter_eq hWo hy₀W ?_ (S.regular y₀ hy₀C (by rw [hy₀x]; exact hd₀))
    rw [inter_assoc C, inter_assoc C, inter_assoc, inter_self]

end Param

/-! ### Analytic germs -/

/-- **The maximum principle on an analytic germ.**  Let `T` be an analytic germ at `0 ∈ ℂⁿ` that is
not reduced to `{0}`, and `ξ` a linear form with `Re ξ ≤ 0` on `T` near `0`.  Then every
neighbourhood of `0` contains a point `y` and a set `B ⊆ T` on which `ξ ≡ ξ(y)`, with `y` a regular
point of `B` of positive dimension. -/
theorem exists_level_regularAtDim_germ {T : Set (ComplexModel n)} (hT : IsAnalyticGerm T)
    (hacc : ∀ O ∈ 𝓝 (0 : ComplexModel n), ∃ z ∈ O ∩ T, z ≠ 0) (ξ : ComplexModel n →L[ℂ] ℂ)
    (hmax : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ T → (ξ z).re ≤ 0) {O : Set (ComplexModel n)}
    (hO : O ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ y ∈ O, ∃ B : Set (ComplexModel n), B ⊆ T ∧ (∀ z ∈ B, ξ z = ξ y) ∧
      ∃ d, 0 < d ∧ RegularAtDim (n := n) (M := ComplexModel n) B y d := by
  classical
  obtain ⟨r, A, hAirr, hAT, hTA, -⟩ := exists_irreducible_decomposition_euclidean hT
  choose L P hS using fun i => exists_parametrization (hAirr i)
  have S : ∀ i, SetsData (P i) := fun i => (hS i).some
  -- some component has positive dimension
  have hpos : ∃ i, 0 < (P i).dim := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ i, ∀ w ∈ (L i) ⁻¹' A i ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂, w = 0 := by
      intro i w hw
      have hd0 : (P i).dim = 0 := Nat.le_zero.1 (hcon i)
      have hsing : Subsingleton (ComplexModel (P i).dim) := by
        rw [hd0]; infer_instance
      refine norm_le_zero_iff.1 (le_of_forall_pos_lt_add fun ε hε => ?_)
      obtain ⟨η, hη, hηs⟩ := exists_norm_lt_of_small (S i) hε
      have h0 : ‖coordinateProjection n (P i).dim w‖ = 0 := by
        rw [Subsingleton.elim (coordinateProjection n (P i).dim w) 0, norm_zero]
      have := hηs w hw (by rw [h0]; exact hη)
      linarith
    have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ T → z = 0 := by
      have hpd : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n),
          (L i).symm z ∈ polydisc n (P i).dim (S i).r₁ (S i).r₂ := fun i => by
        have hc : Tendsto (L i).symm (𝓝 0) (𝓝 0) := by
          simpa using ((L i).symm : ComplexModel n →L[ℂ] ComplexModel n).continuous.tendsto 0
        exact hc.eventually ((isOpen_polydisc _ _ _ _).mem_nhds
          (zero_mem_polydisc (S i).r₁_pos (S i).r₂_pos))
      filter_upwards [Filter.eventuallyEq_set.mp hTA, Filter.eventually_all.2 hpd] with z hz hzp hzT
      obtain ⟨i, hzi⟩ := mem_iUnion.mp (hz.mp hzT)
      have h := hsub i ((L i).symm z) ⟨by simpa using hzi, hzp i⟩
      simpa using congrArg (L i) h
    obtain ⟨z, ⟨hzO, hzT⟩, hz0⟩ := hacc _ hev
    exact hz0 (hzO hzT)
  obtain ⟨i, hi⟩ := hpos
  set C := (L i) ⁻¹' A i with hC
  set ℓ : ComplexModel n →L[ℂ] ℂ := ξ.comp ((L i) : ComplexModel n →L[ℂ] ComplexModel n) with hℓ
  -- a ball on which `A i ⊆ T`, `Re ξ ≤ 0` and `O` hold, read through `L i`
  have hev : ∀ᶠ w in 𝓝 (0 : ComplexModel n), L i w ∈ A i → L i w ∈ T ∧ (ξ (L i w)).re ≤ 0 ∧
      L i w ∈ O := by
    have hc : Tendsto (L i) (𝓝 0) (𝓝 0) := by
      simpa using ((L i) : ComplexModel n →L[ℂ] ComplexModel n).continuous.tendsto 0
    have h := hc.eventually ((hAT i).and (hmax.and hO))
    filter_upwards [h] with w hw hwA
    obtain ⟨h1, h2, h3⟩ := hw
    have hT' : L i w ∈ T := h1 hwA
    exact ⟨hT', h2 hT', h3⟩
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hle : ∀ z ∈ C ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂, ‖z‖ < ρ → (ℓ z).re ≤ 0 :=
    fun z hz hzρ => (hρs z (mem_ball_zero_iff.2 hzρ) hz.1).2.1
  obtain ⟨y₀, -, W, -, -, hWρ, hconst, hreg⟩ := exists_level_piece_of_param (S i) ℓ hρ hle hρ
  have hy₀ : y₀ ∈ C ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂ ∩ W := hreg.2.1
  refine ⟨L i y₀, (hρs y₀ (hWρ hy₀.2) hy₀.1.1).2.2,
    (L i).symm ⁻¹' (C ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂ ∩ W), ?_, ?_, (P i).dim, hi, ?_⟩
  · intro z hz
    have h := (hρs _ (hWρ hz.2) hz.1.1).1
    simpa using h
  · intro z hz
    have h := hconst _ hz
    simp only [hℓ, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  · rw [regularAtDim_preimage_iff, ContinuousLinearEquiv.symm_apply_apply]
    exact hreg

/-! ### Level sets in `ℂⁿ` -/

/-- **A local maximum of `Re ξ` at a non-isolated point** of an analytic subset `K ⊆ ℂⁿ` forces a
level set `K ∩ {ξ = c}` with a regular point of positive dimension. -/
theorem exists_level_regularAtDim_of_isMaxOn {K : Set (ComplexModel n)}
    (hK : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) K) {p : ComplexModel n}
    (hacc : ∀ O ∈ 𝓝 p, ∃ z ∈ O ∩ K, z ≠ p) (ξ : ComplexModel n →L[ℂ] ℂ)
    (hmax : ∀ᶠ z in 𝓝 p, z ∈ K → (ξ z).re ≤ (ξ p).re) :
    ∃ c : ℂ, ∃ x : ComplexModel n, ∃ d, 0 < d ∧
      RegularAtDim (n := n) (M := ComplexModel n) (K ∩ {w | ξ w = c}) x d := by
  set T : Set (ComplexModel n) := {w | w + p ∈ K} with hTdef
  have hT : IsAnalyticGerm T := by
    have h := AnalyticDescendingChain.isAnalyticGerm_chartGerm hK p
    have hset : AnalyticDescendingChain.chartGerm (n := n) K p = T := by
      ext w
      simp [AnalyticDescendingChain.chartGerm, complexChartAt, chartAt_self_eq, hTdef]
    rwa [hset] at h
  have htr : Tendsto (fun w : ComplexModel n => w + p) (𝓝 0) (𝓝 p) :=
    (continuous_add_const p).tendsto' 0 p (zero_add p)
  have hacc' : ∀ O ∈ 𝓝 (0 : ComplexModel n), ∃ z ∈ O ∩ T, z ≠ 0 := by
    intro O hO
    have hc : Tendsto (fun z : ComplexModel n => z - p) (𝓝 p) (𝓝 0) :=
      (continuous_sub_right p).tendsto' p 0 (sub_self p)
    obtain ⟨z, ⟨hzO, hzK⟩, hzp⟩ := hacc _ (hc hO)
    refine ⟨z - p, ⟨hzO, by simpa [hTdef] using hzK⟩, sub_ne_zero.2 hzp⟩
  have hmax' : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ T → (ξ w).re ≤ 0 := by
    filter_upwards [htr.eventually hmax] with w hw hwT
    have h := hw hwT
    rw [map_add, Complex.add_re] at h
    linarith
  obtain ⟨y, -, B, hBT, hBξ, d, hd, hreg⟩ := exists_level_regularAtDim_germ hT hacc' ξ hmax' univ_mem
  set c := ξ y + ξ p with hc
  have hK' : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) (K ∩ {w | ξ w = c}) :=
    hK.inter (GenericSections.isComplexAnalyticSubset_level ξ c)
  have hreg' : RegularAtDim (n := n) (M := ComplexModel n) {z | z - p ∈ B} (y + p) d := by
    rw [AnalyticLocalStatement.regularAtDim_translate_iff, add_sub_cancel_right]
    exact hreg
  have hsub : {z | z - p ∈ B} ⊆ K ∩ {w | ξ w = c} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have h := hBT hz
      simpa [hTdef] using h
    · show ξ z = c
      have h := hBξ _ hz
      rw [map_sub] at h
      rw [hc, ← h]
      ring
  obtain ⟨x, -, k, hdk, hx⟩ := locDimGE_of_regularAtDim_subset hK' hsub hreg' univ univ_mem
  exact ⟨c, x, k, lt_of_lt_of_le hd hdk, hx⟩

/-! ### Compact analytic subsets of `ℂⁿ` -/

/-- **Descending induction on the fixed coordinates**: a compact analytic subset of `ℂⁿ` whose
first `j` coordinates are constant (`j + t = n`) has no regular point of positive dimension. -/
theorem regularAtDim_eq_zero_aux (t : ℕ) : ∀ j, j + t = n → ∀ (K : Set (ComplexModel n))
    (c : Fin n → ℂ), IsComplexAnalyticSubset (n := n) (M := ComplexModel n) K → IsCompact K →
    (∀ z ∈ K, ∀ i : Fin n, i.1 < j → z i = c i) →
    ∀ x k, RegularAtDim (n := n) (M := ComplexModel n) K x k → k = 0 := by
  induction t with
  | zero =>
    intro j hj K c _ _ hfix x k hx
    rw [add_zero] at hj
    subst hj
    by_contra hk
    obtain ⟨z, ⟨-, hzK⟩, hzx⟩ :=
      GenericSections.exists_ne_mem_of_regularAtDim_pos hx (Nat.pos_of_ne_zero hk) univ_mem
    exact hzx (PiLp.ext fun i => (hfix z hzK i i.2).trans (hfix x hx.2.1 i i.2).symm)
  | succ t ih =>
    intro j hj K c hK hc hfix x k hx
    by_contra hk
    have hjn : j < n := by omega
    set i₀ : Fin n := ⟨j, hjn⟩ with hi₀
    set ξ : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj i₀ with hξ
    set Kp := AnalyticCodimTwoStratification.regularStratumHull (n := n) (M := ComplexModel n) K
      (fun k => 0 < k) with hKpdef
    have hKp : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) Kp :=
      AnalyticCodimTwoStratification.isComplexAnalyticSubset_regularStratumHull hK _
    have hKpK : Kp ⊆ K := AnalyticCodimTwoStratification.regularStratumHull_subset hK _
    have hKpc : IsCompact Kp := hc.of_isClosed_subset hKp.isClosed hKpK
    have hR : ∀ {y : ComplexModel n} {k' : ℕ}, 0 < k' →
        RegularAtDim (n := n) (M := ComplexModel n) K y k' → y ∈ Kp :=
      fun hk' hy => subset_closure (mem_iUnion₂.2 ⟨_, hk', hy⟩)
    obtain ⟨p, hpKp, hpmax⟩ := hKpc.exists_isMaxOn ⟨x, hR (Nat.pos_of_ne_zero hk) hx⟩
      (Complex.continuous_re.comp ξ.continuous).continuousOn
    -- `p` is not isolated in `Kp`
    have hacc : ∀ O ∈ 𝓝 p, ∃ z ∈ O ∩ Kp, z ≠ p := by
      intro O hO
      obtain ⟨r, hrO, hrR⟩ := mem_closure_iff_nhds.1 hpKp O hO
      obtain ⟨k', hk', hr⟩ := mem_iUnion₂.1 hrR
      by_cases hrp : r = p
      · subst hrp
        have hev := RegularPatchNeighborhood.eventually_regularAtDim hr
        obtain ⟨z, ⟨⟨hzO, hzreg⟩, hzK⟩, hzp⟩ :=
          GenericSections.exists_ne_mem_of_regularAtDim_pos hr hk' (inter_mem hO hev)
        exact ⟨z, ⟨hzO, hR hk' (hzreg hzK)⟩, hzp⟩
      · exact ⟨r, ⟨hrO, subset_closure hrR⟩, hrp⟩
    obtain ⟨c', x', d, hd, hx'⟩ := exists_level_regularAtDim_of_isMaxOn hKp hacc ξ
      (Eventually.of_forall fun z hz => hpmax hz)
    have hK' : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) (Kp ∩ {w | ξ w = c'}) :=
      hKp.inter (GenericSections.isComplexAnalyticSubset_level ξ c')
    have hK'c : IsCompact (Kp ∩ {w | ξ w = c'}) :=
      hKpc.inter_right (isClosed_eq ξ.continuous continuous_const)
    have hfix' : ∀ z ∈ Kp ∩ {w | ξ w = c'}, ∀ i : Fin n, i.1 < j + 1 →
        z i = Function.update c i₀ c' i := by
      rintro z ⟨hzKp, hzξ⟩ i hi
      by_cases hii : i = i₀
      · subst hii
        rw [Function.update_self]
        exact hzξ
      · rw [Function.update_of_ne hii]
        have hij : i.1 < j := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
          · exact h
          · exact absurd (Fin.ext h) hii
        exact hfix z (hKpK hzKp) i hij
    have := ih (j + 1) (by omega) _ _ hK' hK'c hfix' x' d hx'
    omega

/-- **A compact analytic subset of `ℂⁿ` has only regular points of dimension `0`.** -/
theorem regularAtDim_eq_zero_of_isCompact {K : Set (ComplexModel n)}
    (hK : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) K) (hc : IsCompact K)
    {x : ComplexModel n} {k : ℕ} (hx : RegularAtDim (n := n) (M := ComplexModel n) K x k) :
    k = 0 :=
  regularAtDim_eq_zero_aux n 0 (zero_add n) K 0 hK hc
    (fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)) x k hx

/-- **Compact analytic subsets of `ℂⁿ` are finite** (`rem:compact-analytic-finite`). -/
theorem finite_of_isCompact {K : Set (ComplexModel n)}
    (hK : IsComplexAnalyticSubset (n := n) (M := ComplexModel n) K) (hc : IsCompact K) :
    K.Finite := by
  have hdisc : DiscreteTopology K := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    have h0 : LocDimLE (n := n) (M := ComplexModel n) K x 0 :=
      ⟨univ, univ_mem, fun y _ k hy => (regularAtDim_eq_zero_of_isCompact hK hc hy).le⟩
    have h := not_accPt_of_locDimLE_zero hK hx h0
    rw [AccPt, not_neBot] at h
    exact h
  exact hc.finite ⟨hdisc⟩

/-- A compact set with local equations at each of its points is analytic. -/
theorem isComplexAnalyticSubset_of_isCompact {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {K : Set M}
    (hc : IsCompact K) (h : ∀ x ∈ K, Nonempty (ComplexAnalyticPresentationAt (n := N) K x)) :
    IsComplexAnalyticSubset (n := N) K := by
  intro x
  by_cases hx : x ∈ K
  · exact h x hx
  · exact PureDimension.nonempty_presentation_of_not_mem hc.isClosed subset_rfl hx

/-- **Compact analytic subsets of open subsets of `ℂⁿ` are finite**: a compact `K ⊆ ℂⁿ` with
local holomorphic equations at each of its points (e.g. a compact analytic subset of an open
`Ω ⊆ ℂⁿ`, read in `ℂⁿ`) is finite. -/
theorem finite_of_isCompact_of_presentation {K : Set (ComplexModel n)} (hc : IsCompact K)
    (h : ∀ x ∈ K, Nonempty (ComplexAnalyticPresentationAt (n := n) (M := ComplexModel n) K x)) :
    K.Finite :=
  finite_of_isCompact (isComplexAnalyticSubset_of_isCompact hc h) hc

end Hironaka.CompactAnalyticFinite
