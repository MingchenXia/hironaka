/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMonomialDivisionBounds
import Hironaka.Manifold.HolomorphicContDiff

/-!
# Actual holomorphic evaluations from genuine absolute coefficient mass

The literal monomial sums converge uniformly on the original closed
polydisc. A genuine several-variable Weierstrass argument proves
holomorphy, including for the actual owner quotients and remainder.
No Taylor-radius or perturbed division convergence is assumed proved.
Blueprint: `hironaka-actual-polydisc-holomorphic-evaluation-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Metric Classical
open scoped Topology BigOperators ContDiff
namespace Hironaka.HironakaActualPolydiscHolomorphicEvaluation
noncomputable section
open HironakaActualMonomialDivisionBounds
variable {n : ℕ}

/-- The original coordinate closed polydisc. -/
def closedPolydisc (ρ : Fin n → ℝ) : Set (Fin n → ℂ) := {z | ∀ i,‖z i‖≤ρ i}

/-- The original coordinate open polydisc. -/
def openPolydisc (ρ : Fin n → ℝ) : Set (Fin n → ℂ) := {z | ∀ i,‖z i‖<ρ i}

/-- The literal sum of the unchanged actual complex monomials. -/
def actualSeriesEvaluation (F : MvPowerSeries (Fin n) ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑' a : Fin n →₀ ℕ,MvPowerSeries.coeff a F*∏ i,(z i)^(a i)

private theorem term_bound (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) (z : Fin n → ℂ) (hz : z ∈ closedPolydisc ρ) :
    ‖MvPowerSeries.coeff a F*∏ i,(z i)^(a i)‖≤‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a := by
  simp only [norm_mul,norm_prod,norm_pow,radiusMonomial]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) _)

/-- Finite actual mass gives genuine uniform convergence and the entire closed-polydisc norm bound. -/
theorem evaluation_uniform_and_bound (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) :
    TendstoUniformlyOn (fun s : Finset (Fin n →₀ ℕ) =>
      fun z : Fin n → ℂ => ∑ a ∈ s,MvPowerSeries.coeff a F*∏ i,(z i)^(a i))
      (actualSeriesEvaluation F) atTop (closedPolydisc ρ) ∧
      ∀ z ∈ closedPolydisc ρ,‖actualSeriesEvaluation F z‖≤coefficientMass ρ F := by
  refine ⟨tendstoUniformlyOn_tsum hF (term_bound ρ F),?_⟩
  intro z hz
  obtain ⟨hNorm,_hSum,hBound⟩ := summable_polydisc_evaluation ρ F hF z hz
  exact (norm_tsum_le_tsum_norm hNorm).trans hBound

private theorem openPolydisc_isOpen (ρ : Fin n → ℝ) : IsOpen (openPolydisc ρ) := by
  have h : openPolydisc ρ=⋂ i : Fin n,{z : Fin n → ℂ | ‖z i‖<ρ i} := by
    ext z
    simp only [openPolydisc,mem_ofPred_eq,mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem monomial_differentiable (F : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    Differentiable ℂ (fun z : Fin n → ℂ => MvPowerSeries.coeff a F*∏ i,(z i)^(a i)) := by
  have hp (s : Finset (Fin n)) : Differentiable ℂ (fun z : Fin n → ℂ => ∏ i ∈ s,(z i)^(a i)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using differentiable_const (1 : ℂ)
    | @insert i s hi ih =>
      convert! ((differentiable_apply i).pow (a i)).mul ih using 1
      funext z
      simp only [Finset.prod_insert hi,Pi.mul_apply,Pi.pow_apply]
  exact (hp Finset.univ).const_mul _

private theorem countable_uniform_holomorphic_sum {ι : Type} [Countable ι]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {f : ι → E → ℂ} {u : ι → ℝ} (hu : Summable u)
    (hd : ∀ i,DifferentiableOn ℂ (f i) U) (hb : ∀ i,∀ z ∈ U,‖f i z‖≤u i) :
    DifferentiableOn ℂ (fun z => ∑' i,f i z) U := by
  let := Encodable.ofCountable ι
  let e : ι → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  let s : ℕ → Finset ι := fun N => (Finset.range N).preimage e he.injOn
  have hs : Tendsto s atTop atTop := (tendsto_finset_preimage_atTop_atTop he).comp tendsto_finset_range
  have hm := tendstoUniformlyOn_tsum hu hb
  have hm' : TendstoUniformlyOn (fun N z => ∑ i ∈ s N,f i z) (fun z => ∑' i,f i z) atTop U :=
    fun V hV => hs.eventually (hm V hV)
  intro z hz
  obtain ⟨R,hR,hBall⟩ := Metric.isOpen_iff.mp hU z hz
  apply DifferentiableAt.differentiableWithinAt
  apply Hironaka.differentiableAt_of_tendstoUniformlyOn_ball (g := fun N z => ∑ i ∈ s N,f i z) hR
  · exact Eventually.of_forall fun N => (DifferentiableOn.fun_sum (u := s N) fun i _ => hd i).mono hBall
  · exact hm'.mono hBall

/-- Actual finite mass produces complex differentiability, without any output holomorphy input. -/
theorem evaluation_differentiableOn (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) :
    DifferentiableOn ℂ (actualSeriesEvaluation F) (openPolydisc ρ) := by
  let : Countable (Fin n →₀ ℕ) := .of_equiv (Fin n → ℕ) Finsupp.equivFunOnFinite.symm
  apply countable_uniform_holomorphic_sum (openPolydisc_isOpen ρ) hF
  · intro a
    exact (monomial_differentiable F a).differentiableOn
  · intro a z hz
    exact term_bound ρ F a z (fun i => (hz i).le)

/-- The produced actual function is complex smooth on the same genuine open polydisc. -/
theorem evaluation_contDiffOn (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) :
    ContDiffOn ℂ ∞ (actualSeriesEvaluation F) (openPolydisc ρ) :=
  Hironaka.contDiffOn_of_differentiableOn_complex (evaluation_differentiableOn ρ F hF) (openPolydisc_isOpen ρ)

/-- Positive radii give an actual neighbourhood of zero with the produced holomorphic function. -/
theorem evaluation_zero_neighbourhood (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    openPolydisc ρ ∈ 𝓝 (0 : Fin n → ℂ) ∧ DifferentiableAt ℂ (actualSeriesEvaluation F) 0 ∧
      ContDiffAt ℂ ∞ (actualSeriesEvaluation F) 0 := by
  have hz : (0 : Fin n → ℂ) ∈ openPolydisc ρ := fun i => by simpa using hρ i
  have hU := (openPolydisc_isOpen ρ).mem_nhds hz
  exact ⟨hU,(evaluation_differentiableOn ρ F hF).differentiableAt hU,
    (evaluation_contDiffOn ρ F hF).contDiffAt hU⟩

/-- Literal actual owner quotients and remainder are holomorphic with the genuine same-radius bounds. -/
theorem monomialOwner_evaluations_holomorphic (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    (∀ a : HironakaActualFormalInitialDiagram.actualInitialVertices m I,
      DifferentiableOn ℂ (actualSeriesEvaluation (monomialOwnerQuotient m I a F)) (openPolydisc ρ) ∧
      ∀ z ∈ closedPolydisc ρ,radiusMonomial ρ a.val*‖actualSeriesEvaluation (monomialOwnerQuotient m I a F) z‖≤coefficientMass ρ F) ∧
    DifferentiableOn ℂ (actualSeriesEvaluation (monomialOwnerRemainder m I F)) (openPolydisc ρ) ∧
      ∀ z ∈ closedPolydisc ρ,‖actualSeriesEvaluation (monomialOwnerRemainder m I F) z‖≤coefficientMass ρ F := by
  refine ⟨?_,?_,?_⟩
  · intro a
    have hQ := monomialOwnerQuotient_summable m I ρ hρ F hF a
    refine ⟨evaluation_differentiableOn ρ _ hQ,?_⟩
    intro z hz
    exact (mul_le_mul_of_nonneg_left ((evaluation_uniform_and_bound ρ _ hQ).2 z hz)
      (le_of_lt (Finset.prod_pos fun i _ => pow_pos (hρ i) _))).trans
        (monomialOwnerQuotient_bound m I ρ hρ F hF a)
  · exact evaluation_differentiableOn ρ _ (monomialOwnerRemainder_summable m I ρ hρ F hF)
  · intro z hz
    exact ((evaluation_uniform_and_bound ρ _ (monomialOwnerRemainder_summable m I ρ hρ F hF)).2 z hz).trans
      (monomialOwnerRemainder_bound m I ρ hρ F hF)

end
end Hironaka.HironakaActualPolydiscHolomorphicEvaluation
