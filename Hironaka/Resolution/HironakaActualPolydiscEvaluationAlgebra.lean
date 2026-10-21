/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPolydiscHolomorphicEvaluation
import Hironaka.Resolution.HironakaActualVertexSmallRadius

/-!
# Actual convergent evaluation algebra and common-radius holomorphic vertex division

True absolute Cauchy products prove literal multiplicative evaluation.
The SAME finite monic deg-lex family then internally produces one radius
and genuine holomorphic quotient/remainder functions with the entire
formal and pointwise division identities. Initial coefficient mass is
explicit; the original holomorphic-germ Taylor-radius dictionary is separate.
Blueprint: `hironaka-actual-polydisc-evaluation-algebra-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualPolydiscEvaluationAlgebra
noncomputable section
open HironakaActualMonomialDivisionBounds HironakaActualPolydiscHolomorphicEvaluation
  HironakaActualAnalyticVertexPerturbation HironakaActualVertexNeumannDivision
  HironakaActualVertexSmallRadius HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision HironakaActualFormalVertexDivision
variable {n : ℕ}

/-- Every literal single monomial retains its actual original complex value. -/
theorem evaluation_monomial (a : Fin n →₀ ℕ) (c : ℂ) (z : Fin n → ℂ) :
    actualSeriesEvaluation (MvPowerSeries.monomial a c) z=c*∏ i,(z i)^(a i) := by
  unfold actualSeriesEvaluation
  rw [tsum_eq_single a]
  · rw [MvPowerSeries.coeff_monomial_same]
  · intro b hb
    rw [MvPowerSeries.coeff_monomial_ne hb,zero_mul]

/-- Addition of actual summable coefficient series retains actual evaluation on the whole closed polydisc. -/
theorem evaluation_add (ρ : Fin n → ℝ) (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G)
    (z : Fin n → ℂ) (hz : z ∈ closedPolydisc ρ) :
    actualSeriesEvaluation (F+G) z=actualSeriesEvaluation F z+actualSeriesEvaluation G z := by
  unfold actualSeriesEvaluation
  simp_rw [map_add,add_mul]
  exact ((summable_polydisc_evaluation ρ F hF z hz).2.1).tsum_add
    ((summable_polydisc_evaluation ρ G hG z hz).2.1)

/-- Every genuine finite sum commutes with the actual convergent evaluation. -/
theorem evaluation_finset_sum {ι : Type} (s : Finset ι) (ρ : Fin n → ℝ)
    (F : ι → MvPowerSeries (Fin n) ℂ) (hF : ∀ i ∈ s,HasFiniteCoefficientMass ρ (F i))
    (z : Fin n → ℂ) (hz : z ∈ closedPolydisc ρ) :
    actualSeriesEvaluation (∑ i ∈ s,F i) z=∑ i ∈ s,actualSeriesEvaluation (F i) z := by
  unfold actualSeriesEvaluation
  simp_rw [map_sum,Finset.sum_mul]
  exact Summable.tsum_finsetSum fun i hi => (summable_polydisc_evaluation ρ (F i) (hF i hi) z hz).2.1

/-- True formal convolution evaluates to the product of actual absolutely convergent functions. -/
theorem evaluation_mul (ρ : Fin n → ℝ) (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G)
    (z : Fin n → ℂ) (hz : z ∈ closedPolydisc ρ) :
    actualSeriesEvaluation (F*G) z=actualSeriesEvaluation F z*actualSeriesEvaluation G z := by
  let f := fun a : Fin n →₀ ℕ => MvPowerSeries.coeff a F*∏ i,(z i)^(a i)
  let g := fun a : Fin n →₀ ℕ => MvPowerSeries.coeff a G*∏ i,(z i)^(a i)
  obtain ⟨hFn,hFs,_⟩ := summable_polydisc_evaluation ρ F hF z hz
  obtain ⟨hGn,hGs,_⟩ := summable_polydisc_evaluation ρ G hG z hz
  have hPair : Summable (fun p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) => f p.1*g p.2) :=
    summable_mul_of_summable_norm (f := f) (g := g) hFn hGn
  have hCauchy : (∑' a,f a)*(∑' a,g a)=∑' a : Fin n →₀ ℕ,
      ∑ p ∈ Finset.antidiagonal a,f p.1*g p.2 :=
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (f := f) (g := g) hFs hGs hPair
  have hterm (a : Fin n →₀ ℕ) :
      MvPowerSeries.coeff a (F*G)*(∏ i,(z i)^(a i))=∑ p ∈ Finset.antidiagonal a,f p.1*g p.2 := by
    rw [MvPowerSeries.coeff_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have he : p.1+p.2=a := Finset.mem_antidiagonal.mp hp
    dsimp only [f,g]
    rw [←he]
    simp only [Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]
    ring
  change (∑' a : Fin n →₀ ℕ,MvPowerSeries.coeff a (F*G)*(∏ i,(z i)^(a i)))=(∑' a,f a)*(∑' a,g a)
  rw [hCauchy]
  exact tsum_congr hterm

private theorem monomial_finite_mass (ρ : Fin n → ℝ) (a : Fin n →₀ ℕ) (c : ℂ) :
    HasFiniteCoefficientMass ρ (MvPowerSeries.monomial a c) := by
  apply summable_of_ne_finset_zero (s := {a})
  intro b hb
  have hba : b≠a := by simpa only [Finset.mem_singleton] using hb
  simp [MvPowerSeries.coeff_monomial,hba]

/-- ONE internally produced radius supplies actual convergent holomorphic division for EVERY source numerator. -/
theorem exists_actual_holomorphic_vertex_division (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n)) I)
    (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (hB : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I,
      HasFiniteCoefficientMass η (B.series a-MvPowerSeries.monomial a.val 1)) :
    ∃ ρ : Fin n → ℝ,(∀ i,0<ρ i) ∧ (∀ i,ρ i≤η i) ∧
      ∀ F : MvPowerSeries (Fin n) ℂ,HasFiniteCoefficientMass η F →
        ∃ (H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I → MvPowerSeries (Fin n) ℂ)
          (S : MvPowerSeries (Fin n) ℂ),
          (∀ a,HasFiniteCoefficientMass ρ (H a)) ∧ HasFiniteCoefficientMass ρ S ∧
          F=(∑ a,B.series a*H a)+S ∧ S=actualFormalRemainder (MonomialOrder.degLex (σ := Fin n)) I F ∧
          (∀ a,DifferentiableOn ℂ (actualSeriesEvaluation (B.series a))
            (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ) ∧
            DifferentiableOn ℂ (actualSeriesEvaluation (H a))
              (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ)) ∧
          DifferentiableOn ℂ (actualSeriesEvaluation S)
            (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ) ∧
          ∀ z ∈ closedPolydisc ρ,actualSeriesEvaluation F z=
            (∑ a,actualSeriesEvaluation (B.series a) z*actualSeriesEvaluation (H a) z)+actualSeriesEvaluation S z := by
  obtain ⟨ρ,hρ,hle,hBρ,hsmall⟩ := exists_actual_vertex_small_radius I B η hη hB
  have hFull (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) :
      HasFiniteCoefficientMass ρ (B.series a) := by
    have h := finiteCoefficientMass_add ρ hρ _ _ (hBρ a) (monomial_finite_mass ρ a.val 1)
    simpa only [sub_add_cancel] using h
  refine ⟨ρ,hρ,hle,?_⟩
  intro F hF
  have hFρ := finiteCoefficientMass_mono ρ η hρ hle F hF
  obtain ⟨H,S,hH,hS,hdiv,hcan,_howner,_hnormal,_hSbound,_hHbound⟩ :=
    exists_absolute_vertex_division (MonomialOrder.degLex (σ := Fin n)) I B ρ hρ hBρ hsmall F hFρ
  refine ⟨H,S,hH,hS,hdiv,hcan,?_,evaluation_differentiableOn ρ S hS,?_⟩
  · intro a
    exact ⟨evaluation_differentiableOn ρ _ (hFull a),evaluation_differentiableOn ρ _ (hH a)⟩
  · intro z hz
    have hProd (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) :
        HasFiniteCoefficientMass ρ (B.series a*H a) := finiteCoefficientMass_mul ρ hρ _ _ (hFull a) (hH a)
    calc
      actualSeriesEvaluation F z=actualSeriesEvaluation ((∑ a,B.series a*H a)+S) z := congrArg (fun K => actualSeriesEvaluation K z) hdiv
      _ = actualSeriesEvaluation (∑ a,B.series a*H a) z+actualSeriesEvaluation S z :=
        evaluation_add ρ _ S (finiteCoefficientMass_sum Finset.univ ρ hρ _ fun a _ => hProd a) hS z hz
      _ = (∑ a,actualSeriesEvaluation (B.series a*H a) z)+actualSeriesEvaluation S z := by
        rw [evaluation_finset_sum Finset.univ ρ _ (fun a _ => hProd a) z hz]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact evaluation_mul ρ _ _ (hFull a) (hH a) z hz

end
end Hironaka.HironakaActualPolydiscEvaluationAlgebra
