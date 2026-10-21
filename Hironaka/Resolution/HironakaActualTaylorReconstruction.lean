/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMultilinearTaylorCoordinates
import Hironaka.Resolution.HironakaActualPolydiscEvaluationAlgebra

/-!
# Actual convergent original Taylor evaluation reconstructs the original function

True polynomial evaluation and actual absolutely convergent degree regrouping
connect the original Taylor coefficients to the genuine analytic multilinear
sum. The original function's holomorphy internally produces every dictionary,
positive coefficient radius and actual local reconstruction equation.
Blueprint: `hironaka-actual-taylor-reconstruction-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped BigOperators Topology
namespace Hironaka.HironakaActualTaylorReconstruction
noncomputable section
open HolGerm HironakaActualMonomialDivisionBounds
  HironakaActualPolydiscHolomorphicEvaluation HironakaActualOriginalFormalTaylor
  HironakaActualMultilinearTaylorCoordinates
variable {n : ℕ}

/-- Actual evaluation of the true finite formal coercion is the original polynomial evaluation. -/
theorem evaluation_polynomial (P : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) :
    actualSeriesEvaluation (P : MvPowerSeries (Fin n) ℂ) z=MvPolynomial.eval z P := by
  unfold actualSeriesEvaluation
  rw [tsum_eq_sum (s := P.support) (fun a ha => by
    have hc : MvPolynomial.coeff a P=0 := by simpa only [MvPolynomial.mem_support_iff,not_not] using ha
    rw [MvPolynomial.coeff_coe,hc,zero_mul]),MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro a _
  rw [MvPolynomial.coeff_coe]
  congr 1
  exact (a.prod_fintype (fun i k => (z i)^k) (fun i => pow_zero (z i))).symm

/-- Actual absolute summability justifies regrouping into the SAME genuine homogeneous coordinate polynomials. -/
theorem evaluation_eq_sum_homogeneous_bands (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (P : ℕ → MvPolynomial (Fin n) ℂ)
    (hcoeff : ∀ a : Fin n →₀ ℕ,MvPowerSeries.coeff a F=MvPolynomial.coeff a (P a.degree))
    (hhom : ∀ k,(P k).IsHomogeneous k) (z : Fin n → ℂ) (hz : z∈closedPolydisc ρ) :
    actualSeriesEvaluation F z=∑' k : ℕ,MvPolynomial.eval z (P k) := by
  let v : (Fin n →₀ ℕ) → ℂ := fun a => MvPowerSeries.coeff a F*∏ i,(z i)^(a i)
  have hv : Summable v := (summable_polydisc_evaluation ρ F hF z hz).2.1
  calc
    actualSeriesEvaluation F z=∑' k : ℕ,∑' a : Finsupp.degree ⁻¹' {k},v a.val :=
      (hv.hasSum.tsum_fiberwise Finsupp.degree).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro k
      have heq (a : (Finsupp.degree : (Fin n →₀ ℕ) → ℕ) ⁻¹' {k}) :
          v a.val=MvPolynomial.coeff a.val (P k)*∏ i,(z i)^(a.val i) := by
        have hak : a.val.degree=k := a.property
        dsimp only [v]
        rw [hcoeff,hak]
      calc
        _ = ∑' a : (Finsupp.degree : (Fin n →₀ ℕ) → ℕ) ⁻¹' {k},
            MvPolynomial.coeff a.val (P k)*∏ i,(z i)^(a.val i) := tsum_congr heq
        _ = ∑' a : Fin n →₀ ℕ,MvPolynomial.coeff a (P k)*∏ i,(z i)^(a i) := by
          apply tsum_subtype_eq_of_support_subset
            (f := fun a : Fin n →₀ ℕ => MvPolynomial.coeff a (P k)*∏ i,(z i)^(a i))
            (s := (Finsupp.degree : (Fin n →₀ ℕ) → ℕ) ⁻¹' {k})
          intro a ha
          change a.degree=k
          by_contra hne
          exact ha (by dsimp only; rw [(hhom k).coeff_eq_zero hne,zero_mul])
        _ = actualSeriesEvaluation (P k : MvPowerSeries (Fin n) ℂ) z := by
          simp only [actualSeriesEvaluation,MvPolynomial.coeff_coe]
        _ = _ := evaluation_polynomial (P k) z

/-- Original local holomorphy ALONE produces positive-radius Taylor mass and actual local function reconstruction. -/
theorem originalTaylor_evaluation_eventually (n : ℕ) (f : ComplexModel (0+n) → ℂ)
    (hf : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ f z) :
    ∃ r : ℝ,0<r ∧ HasFiniteCoefficientMass (fun _ : Fin n => r)
      (originalTaylorAlgHom n (HolGerm.mk f hf)) ∧
      ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),
        actualSeriesEvaluation (originalTaylorAlgHom n (HolGerm.mk f hf))
          (fun i : Fin n => z (i.natAdd 0))=f z := by
  have hanalytic : AnalyticAt ℂ f 0 := by
    obtain ⟨U,hUf,hU,h0⟩ := eventually_nhds_iff.mp hf
    exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU
      (fun z hz => (hUf z hz).differentiableWithinAt) h0
  obtain ⟨p,hp⟩ := hanalytic
  obtain ⟨r,hr,hMass⟩ := exists_originalTaylor_finiteMass n (HolGerm.mk f hf)
  have hcoords : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),∀ i : Fin n,‖z (i.natAdd 0)‖≤r := by
    apply eventually_all.mpr
    intro i
    have hO : IsOpen {z : ComplexModel (0+n) | ‖z (i.natAdd 0)‖<r} :=
      isOpen_lt (EuclideanSpace.proj (𝕜 := ℂ) (i.natAdd 0)).continuous.norm continuous_const
    have hevent : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),‖z (i.natAdd 0)‖<r :=
      hO.mem_nhds (by simpa using hr)
    exact hevent.mono fun z hz => hz.le
  refine ⟨r,hr,hMass,?_⟩
  filter_upwards [hcoords,hp.eventually_hasSum] with z hz hsum
  have hEval := evaluation_eq_sum_homogeneous_bands (fun _ : Fin n => r)
    (originalTaylorAlgHom n (HolGerm.mk f hf)) hMass
    (fun k => multilinearCoordinatePolynomial (p k))
    (fun a => originalTaylor_coefficient_eq_multilinearCoordinatePolynomial n f hf p hp a)
    (fun k => multilinearCoordinatePolynomial_homogeneous (p k))
    (fun i : Fin n => z (i.natAdd 0)) hz
  simp_rw [multilinearCoordinatePolynomial_eval] at hEval
  exact hEval.trans (by simpa only [zero_add] using hsum.tsum_eq)

end
end Hironaka.HironakaActualTaylorReconstruction
