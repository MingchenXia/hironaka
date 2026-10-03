/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermParametrizationDense
import Hironaka.Analytic.GermParametrizationFunctions
import Hironaka.Analytic.AnalyticProjectionWeierstrass
import Hironaka.Analytic.GermParametrizationSets
import Mathlib.Topology.MetricSpace.Sequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.HolomorphicCoefficientPolynomials
import Hironaka.Analytic.HolomorphicZeroSetThin
set_option autoImplicit false

/-!
# The key analytic step of Cartan's theorem at a point

Demailly, *Complex analytic and differential geometry*, proof of II.4.29 (second inclusion of
(4.30)): "As `A` is closed, any point `z ∈ A ∩ π⁻¹(z')` with `z'` near `x'` has to be in a small
neighbourhood of one of the points `y ∈ A ∩ π⁻¹(x')`.  Choose `c` such that `u` separates all
points in the fiber.  Then, for a root `u(z'')` of `W_{u,x}(z'; T - u(x''))`, the point `z` must
be in a neighbourhood of `y = x` [...].  From this, we infer that every polynomial `P(z'; T)`
such that `P(z'; u(z'')) = 0` on `(A, x)` is a multiple of `W_{u,x}(z'; T - u(x''))`, because the
roots of the latter polynomial are simple for `z'` in the dense set `(Δ' ∖ S, x')`."

For `P : ParametrizationData A` with good radii `(r₁, r₂)`, a point `x` of the polydisc `Δ` and
the separation hypothesis "no point `y ≠ x` of `closure (A ∩ Δ)` over `π x` has `u(y) = u(x)`":

* `exists_near_of_separates` (properness): points of `A ∩ Δ` with `π z` near `π x` and `u(z)`
  near `u(x)` are near `x` (Bolzano--Weierstrass);
* `eventually_eq_zero_of_vanishing` (the key step, pointwise form): if the monic polynomial
  `ω(w; T) = T^a + ∑_{j<a} ω_j(w) T^j` (`ω_j(0) = 0`) divides `W(π x + w; u(x) + T)` for `w` near
  `0`, and `∑_{j<a} f_j(π z - π x) (u(z) - u(x))^j` vanishes on `A` near `x`, then every `f_j`
  vanishes near `0`.  Off the discriminant locus the roots of `ω(w; ·)` are `a` distinct
  values `τ`, each giving the point `graphPoint (π x + w) (u(x) + τ)` of `A` near `x`; a
  polynomial of degree `< a` vanishing at them is zero, and the discriminant locus is thin.
-/

open Set Filter Metric Polynomial
open scoped Topology

namespace Hironaka.CartanKeyLemma

open RegularLocusDense GermParametrizationData GermParametrizationFunctions

noncomputable section

variable {n : ℕ} {A : Set (ComplexModel n)}

/-- **Properness and separation**: points of `A ∩ Δ` whose projection is near `π x` and whose
`u`-value is near `u(x)` are near `x`, provided `u` separates `x` from the other points of
`closure (A ∩ Δ)` over `π x`. -/
theorem exists_near_of_separates (P : ParametrizationData A) {r₁ r₂ : ℝ}
    (hR : P.GoodRadii r₁ r₂) {x : ComplexModel n} (hx : x ∈ polydisc n P.dim r₁ r₂)
    (hsep : ∀ y ∈ closure (A ∩ polydisc n P.dim r₁ r₂),
      coordinateProjection n P.dim y = coordinateProjection n P.dim x →
      fibreForm P.dim P.coef y = fibreForm P.dim P.coef x → y = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ z ∈ A ∩ polydisc n P.dim r₁ r₂,
      ‖coordinateProjection n P.dim z - coordinateProjection n P.dim x‖ < η →
      ‖fibreForm P.dim P.coef z - fibreForm P.dim P.coef x‖ < η → ‖z - x‖ < ε := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ ν : ℕ, ∃ z ∈ A ∩ polydisc n P.dim r₁ r₂,
      ‖coordinateProjection n P.dim z - coordinateProjection n P.dim x‖ < 1 / ((ν : ℝ) + 1) ∧
      ‖fibreForm P.dim P.coef z - fibreForm P.dim P.coef x‖ < 1 / ((ν : ℝ) + 1) ∧
      ε ≤ ‖z - x‖ := fun ν => by
    obtain ⟨z, hz, h1, h2, h3⟩ := hcon (1 / ((ν : ℝ) + 1)) (by positivity)
    exact ⟨z, hz, h1, h2, h3⟩
  choose z hz h1 h2 h3 using hseq
  have hbdd : Bornology.IsBounded (A ∩ polydisc n P.dim r₁ r₂) :=
    (isBounded_ball (x := (0 : ComplexModel n)) (r := P.rad)).subset
      (inter_subset_right.trans hR.polydisc_subset)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd hz
  have hsmall : Tendsto (fun ν : ℕ => 1 / ((φ ν : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun ν => by positivity) (fun ν => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    gcongr
    exact hφ.id_le ν
  -- the projection
  have hπ : coordinateProjection n P.dim a = coordinateProjection n P.dim x := by
    have hA : Tendsto (fun ν => coordinateProjection n P.dim (z (φ ν))) atTop
        (𝓝 (coordinateProjection n P.dim a)) :=
      ((coordinateProjection n P.dim).continuous.tendsto a).comp hlim
    have hB : Tendsto (fun ν => coordinateProjection n P.dim (z (φ ν))) atTop
        (𝓝 (coordinateProjection n P.dim x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun ν => norm_nonneg _) (fun ν => (h1 (φ ν)).le) hsmall
    exact tendsto_nhds_unique hA hB
  -- the linear form
  have hxb : coordinateProjection n P.dim x ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hx.1.trans_le hR.r₁_le)
  have hcont : ContinuousAt (fibreForm P.dim P.coef) a := by
    refine (ParametrizationData.continuousOn_fibreForm P).continuousAt ?_
    refine (isOpen_ball.preimage (coordinateProjection n P.dim).continuous).mem_nhds ?_
    show coordinateProjection n P.dim a ∈ ball 0 P.rad
    rw [hπ]
    exact hxb
  have hu : fibreForm P.dim P.coef a = fibreForm P.dim P.coef x := by
    have hA : Tendsto (fun ν => fibreForm P.dim P.coef (z (φ ν))) atTop
        (𝓝 (fibreForm P.dim P.coef a)) := hcont.tendsto.comp hlim
    have hB : Tendsto (fun ν => fibreForm P.dim P.coef (z (φ ν))) atTop
        (𝓝 (fibreForm P.dim P.coef x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun ν => norm_nonneg _) (fun ν => (h2 (φ ν)).le) hsmall
    exact tendsto_nhds_unique hA hB
  -- the distance
  have hdist : ε ≤ ‖a - x‖ := by
    have hA : Tendsto (fun ν => ‖z (φ ν) - x‖) atTop (𝓝 ‖a - x‖) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto a).comp hlim
    exact ge_of_tendsto hA (Eventually.of_forall fun ν => h3 (φ ν))
  have hax := hsep a ha hπ hu
  rw [hax, sub_self, norm_zero] at hdist
  exact absurd hdist (not_le.2 hε)

/-- The discriminant does not vanish identically near any point of the ball. -/
theorem not_eventually_disc_eq_zero (P : ParametrizationData A) {x' : ComplexModel P.dim}
    (hx' : x' ∈ ball (0 : ComplexModel P.dim) P.rad) :
    ¬ ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), P.disc (x' + w) = 0 := by
  intro h
  have h' : ∀ᶠ y in 𝓝 x', P.disc y = 0 := by
    rw [← map_add_left_nhds_zero x', eventually_map]
    exact h
  have := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero isOpen_ball
    (convex_ball (0 : ComplexModel P.dim) P.rad).isPreconnected P.differentiableOn_disc hx' h'
  exact P.disc_not_eventually_zero (this 0 (mem_ball_self P.rad_pos))

/-- The polynomial `T^a + ∑_{j<a} ω_j(w) T^j` is monic of degree `a`. -/
theorem monicPoly_monic {E : Type*} (a : ℕ) (ω : ℕ → E → ℂ) (w : E) :
    (monicPoly a ω w).Monic ∧ (monicPoly a ω w).natDegree = a :=
  AnalyticProjectionWeierstrass.monic_X_pow_add_sum a fun k => ω k w

/-- **The key step at a point** (pointwise form). -/
theorem eventually_eq_zero_of_vanishing (P : ParametrizationData A) {r₁ r₂ : ℝ}
    (hR : P.GoodRadii r₁ r₂) {x : ComplexModel n} (hx : x ∈ polydisc n P.dim r₁ r₂)
    (hsep : ∀ y ∈ closure (A ∩ polydisc n P.dim r₁ r₂),
      coordinateProjection n P.dim y = coordinateProjection n P.dim x →
      fibreForm P.dim P.coef y = fibreForm P.dim P.coef x → y = x)
    {a : ℕ} {ω : ℕ → ComplexModel P.dim → ℂ} (hωc : ∀ j < a, ContinuousAt (ω j) 0)
    (hω0 : ∀ j < a, ω j 0 = 0)
    (hdvd : ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), monicPoly a ω w ∣
      (monicPoly P.deg P.w (coordinateProjection n P.dim x + w)).comp
        (X + C (fibreForm P.dim P.coef x)))
    {f : ℕ → ComplexModel P.dim → ℂ} (hfc : ∀ j < a, ∀ᶠ w in 𝓝 0, ContinuousAt (f j) w)
    (hF : ∀ᶠ z in 𝓝 x, z ∈ A → ∑ j ∈ Finset.range a,
      f j (coordinateProjection n P.dim z - coordinateProjection n P.dim x) *
        (fibreForm P.dim P.coef z - fibreForm P.dim P.coef x) ^ j = 0) :
    ∀ j < a, ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), f j w = 0 := by
  classical
  set x' := coordinateProjection n P.dim x with hx'
  set u₀ := fibreForm P.dim P.coef x with hu₀
  have hx'r₁ : ‖x'‖ < r₁ := hx.1
  -- the neighbourhood of `x` on which the sum vanishes on `A`
  obtain ⟨εF, hεF, hεFs⟩ := Metric.eventually_nhds_iff.1 hF
  obtain ⟨η, hη, hnear⟩ := exists_near_of_separates P hR hx hsep hεF
  -- smallness of the roots of `ω(w; ·)`
  set ε := min η 1 with hεdef
  have hε0 : 0 < ε := lt_min hη one_pos
  have hcoef : ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), ∀ j < a, ‖ω j w‖ * a < ε ^ a := by
    refine (eventually_all_finset (Finset.range a)).2 (fun j hj => ?_) |>.mono
      fun w hw j hj => hw j (Finset.mem_range.2 hj)
    have hj' := Finset.mem_range.1 hj
    refine ((hωc j hj').norm.mul continuousAt_const).eventually_lt continuousAt_const ?_
    simp [hω0 j hj', pow_pos hε0]
  have hball : ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), ‖x' + w‖ < r₁ := by
    have hc : ContinuousAt (fun w : ComplexModel P.dim => ‖x' + w‖) 0 :=
      (continuous_norm.comp (continuous_const.add continuous_id)).continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hx'r₁)
  have hsmallw : ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), ‖w‖ < η :=
    (continuous_norm.continuousAt (x := (0 : ComplexModel P.dim))).eventually_lt
      continuousAt_const (by simpa using hη)
  have hall : ∀ᶠ w in 𝓝 (0 : ComplexModel P.dim), (∀ j < a, ‖ω j w‖ * a < ε ^ a) ∧
      ‖x' + w‖ < r₁ ∧ ‖w‖ < η ∧ (monicPoly a ω w ∣
        (monicPoly P.deg P.w (x' + w)).comp (X + C u₀)) ∧
      ∀ j < a, ContinuousAt (f j) w :=
    hcoef.and (hball.and (hsmallw.and (hdvd.and
      (((eventually_all_finset (Finset.range a)).2 fun j hj =>
        hfc j (Finset.mem_range.1 hj)).mono fun w hw j hj => hw j (Finset.mem_range.2 hj)))))
  obtain ⟨ε₀, hε₀, hε₀s⟩ := Metric.eventually_nhds_iff_ball.1 hall
  -- off the discriminant locus all `f_j` vanish
  have hoff : ∀ w ∈ ball (0 : ComplexModel P.dim) ε₀, P.disc (x' + w) ≠ 0 →
      ∀ j < a, f j w = 0 := by
    intro w hw hδ
    obtain ⟨hcw, hr₁w, hηw, hdvdw, -⟩ := hε₀s w hw
    have hxwb : x' + w ∈ ball (0 : ComplexModel P.dim) P.rad :=
      mem_ball_zero_iff.2 (hr₁w.trans_le hR.r₁_le)
    set p := monicPoly a ω w with hp
    set V := (monicPoly P.deg P.w (x' + w)).comp (X + C u₀) with hV
    obtain ⟨hpm, hpdeg⟩ := monicPoly_monic a ω w
    have hVm : V.Monic := (monicPoly_monic P.deg P.w (x' + w)).1.comp (monic_X_add_C u₀)
      (by rw [natDegree_X_add_C]; exact one_ne_zero)
    have hVeval : ∀ τ, V.eval τ = monicEval P.deg P.w (x' + w) (τ + u₀) := fun τ => by
      rw [hV, eval_comp, eval_add, eval_X, eval_C, eval_monicPoly]
    -- simple roots of `V`
    have hVsimple : ∀ τ, V.rootMultiplicity τ ≤ 1 := by
      intro τ
      by_contra hτ
      push Not at hτ
      obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hVm.ne_zero).1 hτ
      have hroot : monicEval P.deg P.w (x' + w) (τ + u₀) = 0 := by
        rw [← hVeval]; exact hr
      apply P.simple (x' + w) hxwb hδ (τ + u₀) hroot
      have hder : derivative V = (derivative (monicPoly P.deg P.w (x' + w))).comp (X + C u₀) := by
        rw [hV, derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul]
      have hfun : monicEval P.deg P.w (x' + w) =
          fun t => (monicPoly P.deg P.w (x' + w)).eval t := funext fun t => (eval_monicPoly _ _ _ t).symm
      rw [hfun, Polynomial.deriv]
      have := hd
      rw [IsRoot, hder, eval_comp, eval_add, eval_X, eval_C] at this
      exact this
    -- `p` has `a` distinct roots
    have hpnodup : p.roots.Nodup := by
      rw [Multiset.nodup_iff_count_le_one]
      intro τ
      rw [count_roots]
      exact (rootMultiplicity_le_rootMultiplicity_of_dvd hVm.ne_zero hdvdw τ).trans (hVsimple τ)
    have hcard : p.roots.toFinset.card = a := by
      rw [Multiset.toFinset_card_of_nodup hpnodup, IsAlgClosed.card_roots_eq_natDegree, hpdeg]
    -- every root gives a point of `A` near `x`
    have hρ : ∀ τ ∈ p.roots.toFinset, ∑ j ∈ Finset.range a, f j w * τ ^ j = 0 := by
      intro τ hτ
      rw [Multiset.mem_toFinset, mem_roots hpm.ne_zero, IsRoot.def] at hτ
      have hτV : V.eval τ = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvdw hτ
      have hroot : monicEval P.deg P.w (x' + w) (τ + u₀) = 0 := by rw [← hVeval]; exact hτV
      have hτsmall : ‖τ‖ < ε := by
        have h0 : τ ^ a + ∑ k ∈ Finset.range a, ω k w * τ ^ k = 0 := by
          rw [← hτ, eval_monicPoly, monicEval]
        exact HolomorphicCoefficientPolynomials.norm_lt_of_weierstrass_root hε0 (min_le_right _ _)
          hcw h0
      have hzA := hR.graphPoint_mem hr₁w hδ hroot
      set z := P.graphPoint (x' + w) (τ + u₀) with hz
      have hπz : coordinateProjection n P.dim z = x' + w := P.coordinateProjection_graphPoint _ _
      have huz : fibreForm P.dim P.coef z = τ + u₀ := P.fibreForm_graphPoint hxwb hδ hroot
      have hzx : ‖z - x‖ < εF := by
        refine hnear z hzA ?_ ?_
        · rw [hπz, add_sub_cancel_left]; exact hηw
        · rw [huz, add_sub_cancel_right]; exact hτsmall.trans_le (min_le_left _ _)
      have := hεFs (by rw [dist_eq_norm]; exact hzx) hzA.1
      rw [hπz, huz, add_sub_cancel_left, add_sub_cancel_right] at this
      exact this
    -- a polynomial of degree `< a` with `a` roots is zero
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · intro j hj; omega
    set ρ : ℂ[X] := ∑ j ∈ Finset.range a, C (f j w) * X ^ j with hρdef
    have hρdeg : ρ.natDegree < p.roots.toFinset.card := by
      rw [hcard]
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (Finset.range a) _ fun j hj =>
        (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_pred_of_lt (Finset.mem_range.1 hj)))
        (Nat.pred_lt_self ha0)
    have hρ0 : ρ = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' ρ _
      (fun τ hτ => by
        rw [hρdef, eval_finsetSum]
        simpa [eval_mul, eval_C, eval_pow, eval_X] using hρ τ hτ) hρdeg
    intro j hj
    have := congrArg (fun q : ℂ[X] => q.coeff j) hρ0
    simp only [hρdef, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hj)] at this
  -- density of the complement of the discriminant locus
  have hdiscOn : DifferentiableOn ℂ (fun w => P.disc (x' + w)) (ball (0 : ComplexModel P.dim) ε₀) := by
    intro w hw
    have hxwb : x' + w ∈ ball (0 : ComplexModel P.dim) P.rad :=
      mem_ball_zero_iff.2 ((hε₀s w hw).2.1.trans_le hR.r₁_le)
    exact ((P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hxwb)).comp w
      ((differentiableAt_const _).add differentiableAt_id)).differentiableWithinAt
  have hcl := RiemannExtension.dense_compl_zeroSet isOpen_ball
    (convex_ball (0 : ComplexModel P.dim) ε₀).isPreconnected hdiscOn (mem_ball_self hε₀)
    (not_eventually_disc_eq_zero P (mem_ball_zero_iff.2 (hx'r₁.trans_le hR.r₁_le)))
  intro j hj
  refine Filter.eventually_of_mem (ball_mem_nhds 0 hε₀) fun w hw => ?_
  by_contra hne
  have hcw : ContinuousAt (f j) w := (hε₀s w hw).2.2.2.2 j hj
  have hev : ∀ᶠ w' in 𝓝 w, f j w' ≠ 0 := hcw.eventually_ne hne
  obtain ⟨w', hw'ne, hw'b, hw'δ⟩ := mem_closure_iff_nhds.1 (hcl hw) _ hev
  exact hw'ne (hoff w' hw'b hw'δ j hj)

end

end Hironaka.CartanKeyLemma
