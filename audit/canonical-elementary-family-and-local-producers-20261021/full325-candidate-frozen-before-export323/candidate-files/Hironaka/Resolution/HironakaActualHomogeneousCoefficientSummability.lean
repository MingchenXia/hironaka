/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMonomialDivisionBounds
import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Actual coefficient mass from degree-band analytic majorants

Exact original coefficient bands and genuine polynomial/multilinear norm
bounds produce whole-series absolute summability at one positive radius.
The separate original Taylor dictionary is an explicit prerequisite.
Blueprint: `hironaka-actual-homogeneous-coefficient-summability-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualHomogeneousCoefficientSummability
noncomputable section
open HironakaActualMonomialDivisionBounds
variable {n : ℕ}

/-- Genuine summable degree-band bounds produce actual whole coefficient mass. -/
theorem finite_mass_of_degree_band_majorants (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (P : ℕ → MvPowerSeries (Fin n) ℂ)
    (hP : ∀ k,HasFiniteCoefficientMass ρ (P k))
    (hcoeff : ∀ a : Fin n →₀ ℕ,MvPowerSeries.coeff a F=MvPowerSeries.coeff a (P a.degree))
    (b : ℕ → ℝ) (hb : Summable b) (hbound : ∀ k,coefficientMass ρ (P k)≤b k) :
    HasFiniteCoefficientMass ρ F := by
  let v : (Fin n →₀ ℕ) → ℝ := fun a => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a
  let s : ℕ → Set (Fin n →₀ ℕ) := fun k => {a | a.degree=k}
  have hpos (a : Fin n →₀ ℕ) : 0≤radiusMonomial ρ a :=
    Finset.prod_nonneg fun i _ => pow_nonneg (le_of_lt (hρ i)) _
  have hv (a : Fin n →₀ ℕ) : 0≤v a := mul_nonneg (norm_nonneg _) (hpos a)
  have heq (k : ℕ) (a : s k) : v a.val=‖MvPowerSeries.coeff a.val (P k)‖*radiusMonomial ρ a.val := by
    dsimp only [v]
    rw [hcoeff,a.property]
  have hpart : ∀ a : Fin n →₀ ℕ,∃! k,a∈s k := fun a =>
    ⟨a.degree,rfl,fun _ h => h.symm⟩
  change Summable v
  apply (summable_partition hv hpart).mpr
  refine ⟨?_,?_⟩
  · intro k
    have h := (hP k).comp_injective (Subtype.val_injective (p := fun a : Fin n →₀ ℕ => a∈s k))
    exact h.congr fun a => (heq k a).symm
  · have hband (k : ℕ) : (∑' a : s k,v a.val)≤b k := by
      calc
        _ = ∑' a : s k,‖MvPowerSeries.coeff a.val (P k)‖*radiusMonomial ρ a.val := tsum_congr (heq k)
        _ ≤ coefficientMass ρ (P k) :=
          tsum_comp_le_tsum_of_inj (hP k) (fun a => mul_nonneg (norm_nonneg _) (hpos a)) Subtype.val_injective
        _ ≤ _ := hbound k
    exact Summable.of_nonneg_of_le (fun k => tsum_nonneg fun a : s k => hv a.val) hband hb

private theorem polynomial_finite_mass (ρ : Fin n → ℝ) (P : MvPolynomial (Fin n) ℂ) :
    HasFiniteCoefficientMass ρ (P : MvPowerSeries (Fin n) ℂ) := by
  apply summable_of_ne_finset_zero (s := P.support)
  intro a ha
  have hc : MvPolynomial.coeff a P=0 := by simpa only [MvPolynomial.mem_support_iff,not_not] using ha
  rw [MvPolynomial.coeff_coe,hc,norm_zero,zero_mul]

/-- Actual positive multilinear radius and finite coordinate band bounds PRODUCE one coefficient radius. -/
theorem exists_uniform_radius_of_multilinear_bands {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ E ℂ) (hp : 0<p.radius)
    (P : ℕ → MvPolynomial (Fin n) ℂ)
    (hbound : ∀ r : ℝ,0<r → ∀ k : ℕ,
      coefficientMass (fun _ : Fin n => r) (P k : MvPowerSeries (Fin n) ℂ)≤
        (n : ℝ)^k*‖p k‖*r^k) :
    ∃ r : ℝ,0<r ∧ ∀ F : MvPowerSeries (Fin n) ℂ,
      (∀ a : Fin n →₀ ℕ,MvPowerSeries.coeff a F=MvPolynomial.coeff a (P a.degree)) →
        HasFiniteCoefficientMass (fun _ : Fin n => r) F := by
  obtain ⟨s,hs,hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hs0 : 0<s := by exact_mod_cast hs
  let r : NNReal := s/(n+1)
  have hden : 0<(n+1 : NNReal) := by positivity
  have hr : 0<r := div_pos hs0 hden
  have hnr : (n : NNReal)*r≤s := by
    dsimp only [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    exact (mul_le_mul_of_nonneg_right (show (n : NNReal)≤n+1 from le_add_of_nonneg_right zero_le_one) s.property).trans_eq (mul_comm _ _)
  have hnorm := p.summable_norm_mul_pow ((ENNReal.coe_le_coe.mpr hnr).trans_lt hsR)
  have hmajor : Summable (fun k : ℕ => (n : ℝ)^k*‖p k‖*(r : ℝ)^k) := by
    apply hnorm.congr
    intro k
    simp only [NNReal.coe_mul,NNReal.coe_natCast,mul_pow]
    ring
  have hr0 : (0 : ℝ)<r := by exact_mod_cast hr
  refine ⟨r,hr0,?_⟩
  intro F hcoeff
  apply finite_mass_of_degree_band_majorants (fun _ : Fin n => (r : ℝ)) (fun _ => hr0) F
    (fun k => (P k : MvPowerSeries (Fin n) ℂ))
    (fun k => polynomial_finite_mass _ (P k))
    (fun a => by rw [MvPolynomial.coeff_coe];exact hcoeff a)
    (fun k => (n : ℝ)^k*‖p k‖*(r : ℝ)^k) hmajor
  exact hbound r hr0

end
end Hironaka.HironakaActualHomogeneousCoefficientSummability
