/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermComponentDimension

import Hironaka.Analytic.GermComponentGeometricDimension

set_option autoImplicit false

/-! # Actual Noether base and geometric dimensions

The actual conversion retains its base dimension rather than forgetting
it in a nonempty output.  The subvariety consumer internally constructs
the parametrization and identifies its dimension geometrically.
-/

open Hironaka

noncomputable section
open Set Filter Metric Topology
namespace Hironaka.ActualNoetherGeometricDimension
open RegularLocusDense AnalyticGermDecomposition GermAlgebraicParametrization
open GermParametrizationData GermParametrizationFunctions AnalyticLocalStatement
open AnalyticDescendingChain

variable {n : ℕ} {A : Set (ComplexModel n)}

/-- Actual algebraic data produce true pointwise data with the SAME internally
assigned base dimension, including all pointwise defining properties. -/
theorem exists_parametrizationData_dim (hA : IsAnalyticGerm A) [(vanishingIdeal A).IsPrime]
    {d : ℕ} (P : AlgebraicParametrization (vanishingIdeal A) d) :
    ∃ D : ParametrizationData A, D.dim = d := by
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
  have h₁ : ∀ x ∈ ball (0 : ComplexModel d) (min r₁ r₂), _ := fun x hx =>
    H₁ x (ball_subset_ball (min_le_left _ _) hx)
  have h₂ : ∀ z ∈ ball (0 : ComplexModel n) (min r₁ r₂), _ := fun z hz =>
    H₂ z (ball_subset_ball (min_le_right _ _) hz)
  exact ⟨{
    dim := d
    dim_le := P.le
    deg := P.minpoly.natDegree
    deg_pos := P.natDegree_minpoly_pos
    rad := min r₁ r₂
    rad_pos := lt_min hr₁ hr₂
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
    exists_eqn_of_not_le := exists_eqn_of_not_le P }, rfl⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Natural actual local branches and their Noether position internally
produce the equality of the base dimension with the geometric dimension. -/
theorem base_dim_eq_subvariety_dim
    (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M} {r : ℕ}
    {A : Fin r → Set (ComplexModel n)} (hA : ∀ i, IsIrreducibleGerm (A i))
    (hcover : chartGerm (n := n) V.carrier x =ᶠ[𝓝 0] (⋃ i, A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j)) (i : Fin r)
    {L : ComplexModel n ≃L[ℂ] ComplexModel n} {d : ℕ}
    (hN : IsNoetherNormalization (vanishingIdeal (L ⁻¹' A i)) d) :
    d = V.dim := by
  have hprime : (vanishingIdeal (A i)).IsPrime :=
    (isIrreducibleGerm_iff_isPrime (hA i).1).mp (hA i)
  let : (vanishingIdeal (A i)).IsPrime := hprime
  have htrans : (vanishingIdeal (L ⁻¹' A i)).IsPrime := by
    rw [← GermParametrization.map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  let : (vanishingIdeal (L ⁻¹' A i)).IsPrime := htrans
  obtain ⟨AP⟩ := GermParametrization.exists_algebraicParametrization hN
  obtain ⟨D, hdim⟩ := exists_parametrizationData_dim
    (GermParametrization.isAnalyticGerm_preimage L (hA i).1) AP
  obtain ⟨S⟩ := nonempty_setsData D
  exact hdim.symm.trans
    (GermComponentDimension.dim_eq_of_parametrizationData V hA hcover hpw i D S)

end Hironaka.ActualNoetherGeometricDimension
