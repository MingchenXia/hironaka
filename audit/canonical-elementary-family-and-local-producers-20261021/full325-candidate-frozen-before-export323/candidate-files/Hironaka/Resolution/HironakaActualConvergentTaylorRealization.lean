/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualTaylorReconstruction
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Uniqueness
/-!
# Arbitrary actual convergent coefficients realize their exact original Taylor germ

Actual coefficient mass produces genuine scalar-line expansions of the literal
homogeneous bands. True one-variable uniqueness and polynomial extensionality
prove whole near-zero evaluation injectivity. The actual holomorphic evaluation
then defines an original germ whose existing original Taylor image is exactly
the input series, using only the natural input absolute summability.

Blueprint: `hironaka-actual-convergent-taylor-realization-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped BigOperators Topology
namespace Hironaka.HironakaActualConvergentTaylorRealization
noncomputable section
open HolGerm HironakaActualMonomialDivisionBounds
  HironakaActualPolydiscHolomorphicEvaluation HironakaActualPolydiscEvaluationAlgebra
  HironakaActualOriginalFormalTaylor HironakaActualMultilinearTaylorCoordinates
  HironakaActualTaylorReconstruction
variable {n : ℕ}

def degreePolynomial (F : MvPowerSeries (Fin n) ℂ) (k : ℕ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.homogeneousComponent k (MvPowerSeries.truncTotal (k+1) F)

theorem degreePolynomial_coeff (F : MvPowerSeries (Fin n) ℂ) (k : ℕ) (a : Fin n →₀ ℕ) :
    MvPolynomial.coeff a (degreePolynomial F k)=if a.degree=k then MvPowerSeries.coeff a F else 0 := by
  rw [degreePolynomial,MvPolynomial.coeff_homogeneousComponent]
  split_ifs with ha
  · exact MvPowerSeries.coeff_truncTotal F (by omega)
  · rfl

private theorem degreePolynomial_homogeneous (F : MvPowerSeries (Fin n) ℂ) (k : ℕ) :
    (degreePolynomial F k).IsHomogeneous k := MvPolynomial.homogeneousComponent_isHomogeneous _ _

private theorem degreePolynomial_eval_fibre (F : MvPowerSeries (Fin n) ℂ) (k : ℕ) (z : Fin n → ℂ) :
    MvPolynomial.eval z (degreePolynomial F k)=
      ∑' a : (Finsupp.degree : (Fin n →₀ ℕ) → ℕ) ⁻¹' {k},
        MvPowerSeries.coeff a.val F*∏ i,(z i)^(a.val i) := by
  rw [← evaluation_polynomial]
  unfold actualSeriesEvaluation
  have hsub := tsum_subtype_eq_of_support_subset
    (f := fun a : Fin n →₀ ℕ => MvPolynomial.coeff a (degreePolynomial F k)*∏ i,(z i)^(a i))
    (s := (Finsupp.degree : (Fin n →₀ ℕ) → ℕ) ⁻¹' {k}) (by
      intro a ha
      by_contra hne
      change a.degree≠k at hne
      exact ha (by
        change MvPolynomial.coeff a (degreePolynomial F k)*_ = 0
        rw [degreePolynomial_coeff,if_neg hne,zero_mul]))
  simp only [MvPolynomial.coeff_coe]
  rw [← hsub]
  apply tsum_congr
  intro a
  have hak : a.val.degree=k := a.property
  rw [degreePolynomial_coeff,if_pos hak]

private theorem degreePolynomial_eval_smul (F : MvPowerSeries (Fin n) ℂ) (k : ℕ)
    (z : Fin n → ℂ) (t : ℂ) :
    MvPolynomial.eval (t • z) (degreePolynomial F k)=t^k*MvPolynomial.eval z (degreePolynomial F k) := by
  rw [← evaluation_polynomial,← evaluation_polynomial]
  unfold actualSeriesEvaluation
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,Finset.prod_mul_distrib,MvPolynomial.coeff_coe]
  by_cases ha : a.degree=k
  · have he : (∏ i : Fin n,t^(a i))=t^k := by
      rw [Finset.prod_pow_eq_pow_sum,← Finsupp.degree_eq_sum,ha]
    rw [he]
    ring
  · rw [degreePolynomial_coeff,if_neg ha]
    simp

def scalarLineSeries (F : MvPowerSeries (Fin n) ℂ) (z : Fin n → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun k => ContinuousMultilinearMap.mkPiRing ℂ (Fin k) (MvPolynomial.eval z (degreePolynomial F k))

theorem scalarLine_hasFPowerSeriesOnBall (ρ : Fin n → ℝ) (_hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (z : Fin n → ℂ) (hz : z∈closedPolydisc ρ) :
    HasFPowerSeriesOnBall (fun t : ℂ => actualSeriesEvaluation F (t • z)) (scalarLineSeries F z) 0 1 := by
  have hsum (w : Fin n → ℂ) (hw : w∈closedPolydisc ρ) :
      HasSum (fun k => MvPolynomial.eval w (degreePolynomial F k)) (actualSeriesEvaluation F w) := by
    have h := (summable_polydisc_evaluation ρ F hF w hw).2.1.hasSum.tsum_fiberwise Finsupp.degree
    exact h.congr_fun fun k => degreePolynomial_eval_fibre F k w
  have hn : Summable (fun k => ‖scalarLineSeries F z k‖*(1 : ℝ)^k) := by
    simpa only [scalarLineSeries,ContinuousMultilinearMap.norm_mkPiRing,one_pow,mul_one]
      using (hsum z hz).summable.norm
  refine ⟨?_,by norm_num,?_⟩
  · exact (scalarLineSeries F z).le_radius_of_summable (r := 1) hn
  · intro t ht
    have ht' : ‖t‖<1 := by
      rw [← ENNReal.coe_one,Metric.eball_coe] at ht
      simpa using ht
    have htz : t • z∈closedPolydisc ρ := by
      intro i
      change ‖t*z i‖≤ρ i
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)).trans (by simpa using hz i)
    have h := hsum (t • z) htz
    simpa only [zero_add,scalarLineSeries,ContinuousMultilinearMap.mkPiRing_apply,
      Fin.prod_const,smul_eq_mul,degreePolynomial_eval_smul] using h

theorem scalarLine_hasFPowerSeriesAt (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (z : Fin n → ℂ) (hz : z∈closedPolydisc ρ) :
    HasFPowerSeriesAt (fun t : ℂ => actualSeriesEvaluation F (t • z)) (scalarLineSeries F z) 0 :=
  (scalarLine_hasFPowerSeriesOnBall ρ hρ F hF z hz).hasFPowerSeriesAt

/-- Actual local zero evaluation kills the entire original convergent series. -/
theorem eq_zero_of_evaluation_eventually_zero (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (hzero : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),actualSeriesEvaluation F z=0) : F=0 := by
  have heval (z : Fin n → ℂ) (hz : z∈closedPolydisc ρ) (k : ℕ) :
      MvPolynomial.eval z (degreePolynomial F k)=0 := by
    have ht : Tendsto (fun t : ℂ => t • z) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℂ => t • z) := by fun_prop
      simpa only [zero_smul] using hc.tendsto 0
    have hq := (scalarLine_hasFPowerSeriesAt ρ hρ F hF z hz).eq_zero_of_eventually (ht.eventually hzero)
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1)) hq
    change (scalarLineSeries F z k) (fun _ => 1)=0 at hc
    simpa only [scalarLineSeries,ContinuousMultilinearMap.mkPiRing_apply,Finset.prod_const_one,one_smul] using hc
  have hP (k : ℕ) : degreePolynomial F k=0 := by
    apply MvPolynomial.funext_set (fun i : Fin n => Metric.ball (0 : ℂ) (ρ i))
      (fun i => infinite_of_mem_nhds (0 : ℂ) (Metric.ball_mem_nhds _ (hρ i)))
    intro z hz
    rw [map_zero]
    exact heval z (fun i => by
      have hi := hz i (mem_univ i)
      exact (show ‖z i‖<ρ i by simpa using hi).le) k
  apply MvPowerSeries.ext
  intro a
  have ha := congrArg (MvPolynomial.coeff a) (hP a.degree)
  simpa [degreePolynomial_coeff] using ha

/-- Two genuine convergent series with arbitrary input radii and equal local evaluations coincide. -/
theorem eq_of_evaluation_eventually_eq (ρ η : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (hη : ∀ i,0<η i)
    (F G : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (hG : HasFiniteCoefficientMass η G)
    (heq : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ),actualSeriesEvaluation F z=actualSeriesEvaluation G z) : F=G := by
  let r : Fin n → ℝ := fun i => min (ρ i) (η i)
  have hr (i : Fin n) : 0<r i := lt_min (hρ i) (hη i)
  have hFr := HironakaActualVertexSmallRadius.finiteCoefficientMass_mono r ρ hr
    (fun i => min_le_left _ _) F hF
  have hGr := HironakaActualVertexSmallRadius.finiteCoefficientMass_mono r η hr
    (fun i => min_le_right _ _) G hG
  have hneg : HasFiniteCoefficientMass r (-G) := by
    simpa only [HasFiniteCoefficientMass,map_neg,norm_neg] using hGr
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluation_eventually_zero r hr (F-G)
    (by simpa only [sub_eq_add_neg] using HironakaActualAnalyticVertexPerturbation.finiteCoefficientMass_add r hr F (-G) hFr hneg)
  filter_upwards [heq,(evaluation_zero_neighbourhood r hr F hFr).1] with z hz hzU
  have hzR : z∈closedPolydisc r := fun i => (hzU i).le
  rw [sub_eq_add_neg,evaluation_add r F (-G) hFr hneg z hzR]
  have hN : actualSeriesEvaluation (-G) z= -actualSeriesEvaluation G z := by
    simp only [actualSeriesEvaluation,map_neg,neg_mul,tsum_neg]
  rw [hN,hz,add_neg_cancel]

/-- The genuine original Euclidean coordinate tuple as an actual continuous linear map. -/
def originalCoordinates : ComplexModel (0+n) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => EuclideanSpace.proj (i.natAdd 0)

private def originalCoordinateVector (z : Fin n → ℂ) : ComplexModel (0+n) :=
  WithLp.toLp 2 (fun i : Fin (0+n) => z ⟨i.val,by have := i.isLt;omega⟩)

private theorem originalCoordinateVector_continuous : Continuous (originalCoordinateVector (n := n)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin (0+n) => ℂ)).comp
    (continuous_pi fun i : Fin (0+n) => continuous_apply (⟨i.val,by have := i.isLt;omega⟩ : Fin n))

private theorem originalCoordinates_vector (z : Fin n → ℂ) :
    originalCoordinates (originalCoordinateVector z)=z := by
  ext i
  simp [originalCoordinates,originalCoordinateVector]

private theorem originalCoordinateVector_zero : originalCoordinateVector (0 : Fin n → ℂ)=0 := by
  ext i
  rfl

/-- The unchanged actual evaluation in the original Euclidean germ coordinates. -/
def evaluationFunction (F : MvPowerSeries (Fin n) ℂ) : ComplexModel (0+n) → ℂ :=
  fun z => actualSeriesEvaluation F (originalCoordinates z)

/-- Actual mass produces a genuine original holomorphic representative, without a Taylor certificate. -/
theorem evaluationFunction_holomorphic (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),DifferentiableAt ℂ (evaluationFunction F) z := by
  have hO : IsOpen (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ) := by
    have he : HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ=⋂ i : Fin n,{z : Fin n → ℂ | ‖z i‖<ρ i} := by
      ext z
      simp only [HironakaActualPolydiscHolomorphicEvaluation.openPolydisc,mem_ofPred_eq,mem_iInter]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const
  have ht : Tendsto (originalCoordinates (n := n)) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (originalCoordinates (n := n)).continuous.tendsto 0
  filter_upwards [ht.eventually (evaluation_zero_neighbourhood ρ hρ F hF).1] with z hz
  exact ((evaluation_differentiableOn ρ F hF).differentiableAt (hO.mem_nhds hz)).comp z
    (originalCoordinates (n := n)).differentiableAt

/-- The actual evaluated original holomorphic germ of the entire input series. -/
def evaluationGerm (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) : HolGerm (ComplexModel (0+n)) :=
  HolGerm.mk (evaluationFunction F) (evaluationFunction_holomorphic ρ hρ F hF)

/-- The ORIGINAL Taylor algebra image of arbitrary actual convergent coefficients is exactly those coefficients. -/
theorem originalTaylor_evaluationGerm (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    originalTaylorAlgHom n (evaluationGerm ρ hρ F hF)=F := by
  obtain ⟨r,hr,hMass,heq⟩ := originalTaylor_evaluation_eventually n (evaluationFunction F)
    (evaluationFunction_holomorphic ρ hρ F hF)
  have ht : Tendsto (originalCoordinateVector (n := n)) (𝓝 0) (𝓝 0) := by
    simpa only [originalCoordinateVector_zero] using originalCoordinateVector_continuous.tendsto (0 : Fin n → ℂ)
  apply eq_of_evaluation_eventually_eq (fun _ => r) ρ (fun _ => hr) hρ
    (originalTaylorAlgHom n (evaluationGerm ρ hρ F hF)) F hMass hF
  filter_upwards [ht.eventually heq] with z hz
  change actualSeriesEvaluation (originalTaylorAlgHom n (evaluationGerm ρ hρ F hF))
    (originalCoordinates (originalCoordinateVector z))=
      actualSeriesEvaluation F (originalCoordinates (originalCoordinateVector z)) at hz
  simpa only [originalCoordinates_vector] using hz

end
end Hironaka.HironakaActualConvergentTaylorRealization
