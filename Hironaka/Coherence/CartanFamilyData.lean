/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermParametrizationDense
import Hironaka.Analytic.GermParametrizationFunctions
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.AnalyticGermDecomposition
import Hironaka.Analytic.GermAlgebraicParametrization
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.HolomorphicGermRing
import Hironaka.Analytic.HolomorphicZeroSetThin
set_option autoImplicit false

/-!
# Parametrization data with exposed fields, and density for each primitive element

Inputs of Cartan's theorem for an irreducible germ (steps 3--4). The tree proves
`GermParametrizationData.nonempty_parametrizationData` and `GermParametrizationData.nonempty_localParametrization`
in `Nonempty` form, which hides the facts Cartan's argument needs about the data it constructs. This module restates
them:

* `exists_radius_parametrizationData`: for an `AlgebraicParametrization` (e.g. one with a
  prescribed primitive element, `CartanPrescribedPrimitive`) and every small radius `ρ` there is
  `ParametrizationData` with `dim = d`, `rad = ρ` and the same constant coefficients `c` of
  the primitive element (same construction as `nonempty_parametrizationData`, so that finitely
  many primitive elements share one ball);
* `exists_dense`: `A ∩ Δ₀ ⊆ closure (A ∩ Δ₀ ∩ {δ ≠ 0})` on a small polydisc `Δ₀` (the density
  step of `nonempty_localParametrization`, Demailly II.4.19 a)).

The proofs are those of the tree, with the conclusions exposed.
-/

open Set Filter Metric Polynomial
open scoped Topology

namespace Hironaka.CartanFamilyData

open RegularLocusDense AnalyticGermDecomposition GermAlgebraicParametrization
open GermParametrizationData GermParametrizationFunctions

noncomputable section

variable {n : ℕ} {A : Set (ComplexModel n)}

/-- **Density of the part over the complement of the discriminant locus** (Demailly II.4.19 a)),
with the polydisc exposed. -/
theorem exists_dense (P : ParametrizationData A) (S : SetsData P) :
    ∃ ρ₀ > 0, A ∩ polydisc n P.dim ρ₀ S.r₂ ⊆
      closure (A ∩ polydisc n P.dim ρ₀ S.r₂ ∩
        coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) := by
  classical
  set N := P.deg * (n - P.dim) + 1 with hN
  have hcan : ∀ i : ℕ, ∃ F : ℕ → ComplexModel P.dim → ℂ,
      (∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1), DifferentiableAt ℂ (F j) x ∧
        (P.disc x ≠ 0 → F j x = (fibrePoly S (form n P.dim i) x).coeff j)) ∧
      ∀ᶠ z in 𝓝 0, z ∈ A → ∑ j ∈ Finset.range (P.deg + 1),
        F j (coordinateProjection n P.dim z) * form n P.dim i z ^ j = 0 := fun i =>
    exists_canonical S (form n P.dim i)
      (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) S.r₂_pos.le) fun z hz =>
      norm_form_le fun k hk => (hz.2 k hk).le
  choose F hFb hFz using hcan
  have hdisc : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), DifferentiableAt ℂ P.disc x :=
    eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun x hx =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hx)
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1
    ((eventually_all_finset (Finset.range N)).2 fun i _ => hFz i)
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := Metric.eventually_nhds_iff_ball.1
    (((eventually_all_finset (Finset.range N)).2 fun i _ => hFb i).and hdisc)
  obtain ⟨K, hK0, hK⟩ := exists_bound_forms (n := n) P.dim N
  set M := ∑ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ := by positivity
    linarith
  have hformM : ∀ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ ≤ M := fun i hi => by
    have := Finset.single_le_sum (f := fun i => ∑ k : Fin n, ‖formCoef P.dim i k‖)
      (fun i _ => by positivity) hi
    linarith
  have hcardN : n - P.dim ≤ (Finset.range N).card := by
    rw [Finset.card_range, hN]
    exact Nat.le_succ_of_le (Nat.le_mul_of_pos_left _ P.deg_pos)
  set s := ε / (2 * (K * M + 1)) with hs
  have hKM : 0 ≤ K * M := by nlinarith
  have hs0 : 0 < s := by positivity
  have hKMs : K * (M * s) < ε := by
    have h1 : (K * M + 1) * s = ε / 2 := by
      rw [hs]; field_simp
    nlinarith
  obtain ⟨η, hη, hηs⟩ := S.small s hs0
  set ρ₀ := min (min S.r₁ ρ₁) (min η s) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min (lt_min S.r₁_pos hρ₁) (lt_min hη hs0)
  have hρ₀r₁ : ρ₀ ≤ S.r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀ρ₁ : ρ₀ ≤ ρ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀η : ρ₀ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₀s : ρ₀ ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : polydisc n P.dim ρ₀ S.r₂ ⊆ polydisc n P.dim S.r₁ S.r₂ := polydisc_mono hρ₀r₁
  -- the canonical defining functions vanish on `A ∩ Δ₀`
  have hvanish : ∀ z ∈ A ∩ polydisc n P.dim ρ₀ S.r₂, ∀ i ∈ Finset.range N,
      ∑ j ∈ Finset.range (P.deg + 1),
        F i j (coordinateProjection n P.dim z) * form n P.dim i z ^ j = 0 := by
    intro z hz i hi
    refine hεs z ?_ i hi hz.1
    have hsmall := hηs z ⟨hz.1, hsub hz.2⟩ (lt_of_lt_of_le hz.2.1 hρ₀η)
    have hMs : s ≤ M * s := le_mul_of_one_le_left hs0.le hM1
    have hbd := hK (Finset.range N) subset_rfl hcardN z (M * s) (by positivity)
      (fun i hi => (norm_form_le fun k hk => (hsmall k hk).le).trans
        (mul_le_mul_of_nonneg_right (hformM i hi) hs0.le))
      ((hz.2.1.le.trans hρ₀s).trans hMs)
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt hbd hKMs
  -- density
  have hdense : A ∩ polydisc n P.dim ρ₀ S.r₂ ⊆
      closure (A ∩ polydisc n P.dim ρ₀ S.r₂ ∩
        coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) := by
    intro y hy
    rw [Metric.mem_closure_iff]
    intro e he
    set δ := e / (2 * (K + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hKδ : K * δ < e := by
      have h1 : (K + 1) * δ = e / 2 := by
        rw [hδ]; field_simp
      nlinarith
    set y' := coordinateProjection n P.dim y with hy'
    have hy'ρ₀ : ‖y'‖ < ρ₀ := hy.2.1
    have hy'b : y' ∈ ball (0 : ComplexModel P.dim) ρ₁ := by
      rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hy'ρ₀ hρ₀ρ₁
    have hFy := (hρ₁s y' hy'b).1
    have hcont : ∀ i ∈ Finset.range N, ∀ᶠ x in 𝓝 y',
        ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖ < δ ^ P.deg := by
      intro i hi
      have hc : ContinuousAt
          (fun x => ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖) y' :=
        (DifferentiableAt.fun_sum fun j hj => (hFy i hi j hj).1.mul_const _).continuousAt.norm
      refine hc.eventually_lt continuousAt_const ?_
      rw [hvanish y hy i hi, norm_zero]
      positivity
    have hnear : ∀ᶠ x in 𝓝 y', (∀ i ∈ Finset.range N,
        ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖ < δ ^ P.deg) ∧
        dist x y' < δ :=
      ((eventually_all_finset _).2 hcont).and (ball_mem_nhds y' hδ0)
    have hdiscOn : DifferentiableOn ℂ P.disc (ball (0 : ComplexModel P.dim) ρ₀) := fun x hx =>
      ((hρ₁s x (ball_subset_ball hρ₀ρ₁ hx)).2).differentiableWithinAt
    have hcl := RiemannExtension.dense_compl_zeroSet isOpen_ball
      (convex_ball (0 : ComplexModel P.dim) ρ₀).isPreconnected hdiscOn (mem_ball_self hρ₀0)
      P.disc_not_eventually_zero (mem_ball_zero_iff.2 hy'ρ₀)
    obtain ⟨x, ⟨hxF, hxy⟩, hxb, hxd⟩ := mem_closure_iff_nhds.1 hcl _ hnear
    have hxρ₀ : ‖x‖ < ρ₀ := mem_ball_zero_iff.1 hxb
    have hxr₁ : ‖x‖ < S.r₁ := lt_of_lt_of_le hxρ₀ hρ₀r₁
    have hxd' : P.disc x ≠ 0 := hxd
    set Tx := (S.finite_fibre x hxr₁ hxd').toFinset with hTx
    have hroot : ∀ i, ∃ b, i ∈ Finset.range N →
        b ∈ Tx ∧ ‖form n P.dim i y - form n P.dim i b‖ < δ := by
      intro i
      by_cases hi : i ∈ Finset.range N
      · by_contra hcon
        push Not at hcon
        have hge : δ ^ P.deg ≤ ‖∑ j ∈ Finset.range (P.deg + 1),
            F i j x * form n P.dim i y ^ j‖ := by
          have hsum : ∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j
              = ∑ j ∈ Finset.range (P.deg + 1),
                (fibrePoly S (form n P.dim i) x).coeff j * form n P.dim i y ^ j :=
            Finset.sum_congr rfl fun j hj => by
              rw [((hρ₁s x (ball_subset_ball hρ₀ρ₁ hxb)).1 i hi j hj).2 hxd']
          rw [hsum, sum_coeff_fibrePoly S _ hxr₁ hxd', norm_prod, ← card_toFinset_fibre S hxr₁ hxd',
            ← Finset.prod_const]
          exact Finset.prod_le_prod (fun _ _ => hδ0.le) fun b hb => (hcon b).2 hb
        exact absurd (hxF i hi) (not_lt.2 hge)
      · exact ⟨0, fun h => absurd h hi⟩
    choose b hb using hroot
    obtain ⟨b₀, hb₀, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.range N) (t := Tx) (f := b) (n := n - P.dim) (fun i hi => (hb i hi).1)
      (by rw [card_toFinset_fibre S hxr₁ hxd', Finset.card_range, hN]; omega)
    obtain ⟨⟨hb₀A, hb₀Δ⟩, hb₀π⟩ := (Set.Finite.mem_toFinset _).1 hb₀
    have hb₀π' : coordinateProjection n P.dim b₀ = x := hb₀π
    have hbd := hK _ (Finset.filter_subset _ _) hcard.le (y - b₀) δ hδ0.le
      (fun i hi => by
        have hi' := Finset.mem_filter.1 hi
        rw [map_sub, ← hi'.2]
        exact (hb i hi'.1).2.le)
      (by rw [map_sub, norm_sub_rev, ← dist_eq_norm, hb₀π']; exact hxy.le)
    refine ⟨b₀, ⟨⟨hb₀A, ?_, hb₀Δ.2⟩, ?_⟩, ?_⟩
    · rw [hb₀π']; exact hxρ₀
    · show P.disc (coordinateProjection n P.dim b₀) ≠ 0
      rw [hb₀π']; exact hxd'
    · rw [dist_eq_norm]; exact lt_of_le_of_lt hbd hKδ
  exact ⟨ρ₀, hρ₀0, hdense⟩

/-- **Parametrization data on every small ball**, with `dim = d` and the coefficients of the
primitive element of the given algebraic data. -/
theorem exists_radius_parametrizationData (hA : IsAnalyticGerm A) [(vanishingIdeal A).IsPrime]
    {d : ℕ} (P : AlgebraicParametrization (vanishingIdeal A) d) :
    ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ → ∃ PD : ParametrizationData A, PD.dim = d ∧ PD.rad = ρ ∧
      (∀ k (x : ComplexModel PD.dim), PD.coef k x = P.coef k) ∧
      PD.s = fun k => (P.coordPoly k).natDegree := by
  have hd := (eventually_differentiableAt_coeffFun P.minpoly P.minpoly.natDegree).and <|
    (eventually_all.2 fun k => eventually_differentiableAt_coeffFun (P.B k)
      P.minpoly.natDegree).and <|
    (eventually_all.2 fun k => eventually_differentiableAt_coeffFun (P.coordPoly k)
      (P.coordPoly k).natDegree).and <|
    (eventually_differentiableAt_rep P.disc).and <|
    (eventually_recover P).and <| (eventually_subst P).and (eventually_simple P)
  have hn := (eventually_w_eq_zero P).and <| (eventually_disc_mul_eq P).and <|
    (eventually_e_eq_zero P).and (eventually_complete P hA)
  obtain ⟨r₁, hr₁, H₁⟩ := Metric.eventually_nhds_iff_ball.1 hd
  obtain ⟨r₂, hr₂, H₂⟩ := Metric.eventually_nhds_iff_ball.1 hn
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun ρ hρ hρle => ?_⟩
  have h₁ : ∀ x ∈ ball (0 : ComplexModel d) ρ, _ := fun x hx =>
    H₁ x (ball_subset_ball (hρle.trans (min_le_left _ _)) hx)
  have h₂ : ∀ z ∈ ball (0 : ComplexModel n) ρ, _ := fun z hz =>
    H₂ z (ball_subset_ball (hρle.trans (min_le_right _ _)) hz)
  exact ⟨{
    dim := d
    dim_le := P.le
    deg := P.minpoly.natDegree
    deg_pos := P.natDegree_minpoly_pos
    rad := ρ
    rad_pos := hρ
    w := wFun P
    differentiableOn_w := fun j x hx => ((h₁ x hx).1 j).differentiableWithinAt
    w_zero := fun j _ => coeffFun_zero P.isWeierstrass_minpoly.2 j
    disc := discFun P
    differentiableOn_disc := fun x hx => (h₁ x hx).2.2.2.1.differentiableWithinAt
    disc_not_eventually_zero := fun h => P.disc_ne_zero (by
      rw [← mk_rep P.disc, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
      exact h)
    coef := fun k _ => P.coef k
    differentiableOn_coef := fun k => differentiableOn_const _
    b := bFun P
    differentiableOn_b := fun k j x hx => ((h₁ x hx).2.1 k j).differentiableWithinAt
    s := fun k => (P.coordPoly k).natDegree
    e := fun k => if d ≤ k.1 then eFun P k else fun _ _ => 0
    differentiableOn_e := fun k j x hx => by
      split_ifs
      · exact ((h₁ x hx).2.2.1 k j).differentiableWithinAt
      · exact differentiableWithinAt_const _
    e_zero := fun k j hj => by
      split_ifs with hk
      · exact coeffFun_zero (P.isWeierstrass_coordPoly k hk).2 j
      · rfl
    w_eq_zero := fun z hzA hz => (h₂ z hz).1 hzA
    disc_mul_eq := fun z hzA hz => (h₂ z hz).2.1 hzA
    e_eq_zero := fun z hzA hz k hk => by
      dsimp only
      rw [if_pos hk]
      exact (h₂ z hz).2.2.1 hzA k hk
    recover := fun x hx => (h₁ x hx).2.2.2.2.1
    subst := fun x hx hδ t ht k hk => by
      rw [if_pos hk]
      exact (h₁ x hx).2.2.2.2.2.1 hδ t ht k hk
    simple := fun x hx => (h₁ x hx).2.2.2.2.2.2
    complete := fun z hz => (h₂ z hz).2.2.2
    prime := prime_of_isPrime
    base := base_of P
    exists_eqn_of_not_le := exists_eqn_of_not_le P }, rfl, rfl, fun _ _ => rfl, rfl⟩

end

end Hironaka.CartanFamilyData
