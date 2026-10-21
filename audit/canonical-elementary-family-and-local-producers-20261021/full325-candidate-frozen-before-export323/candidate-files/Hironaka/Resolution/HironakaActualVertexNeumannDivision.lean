/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticVertexPerturbation
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.Units
/-!
# Genuine Banach inversion of the actual vertex-tail map and convergent canonical remainders

Weighted actual coefficients identify the absolute coefficient domain with a
complete complex l1 space. The SAME computed actual finite tail map becomes a
bounded endomorphism. Its explicit numerical tail constant < 1 produces an
actual Neumann inverse, owner-supported quotient convergence, the whole ideal
canonical remainder, and convergence of the canonical reduced vertex series.
The concrete small-tail bound is a natural analytic norm premise; no inverse,
output-convergence or prepared-family certificate is supplied. Producing an
appropriate radius from original holomorphic data remains a separate bridge.

Blueprint: `hironaka-actual-vertex-neumann-division-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualVertexNeumannDivision
noncomputable section
open HironakaActualMonomialDivisionBounds HironakaActualAnalyticVertexPerturbation
  HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
  HironakaActualReducedFormalStandardBasis
variable {n : ℕ}

abbrev CoefficientBanachSpace (n : ℕ) := lp (fun _ : Fin n →₀ ℕ => ℂ) 1

private theorem radius_pos (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (a : Fin n →₀ ℕ) :
    0<radiusMonomial ρ a := Finset.prod_pos fun i _ => pow_pos (hρ i) _

private theorem radius_cast_ne (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (a : Fin n →₀ ℕ) :
    (radiusMonomial ρ a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (radius_pos ρ hρ a))

/-- Literal inverse weighting of an actual complex Banach coefficient vector. -/
def seriesOfLp (ρ : Fin n → ℝ) : CoefficientBanachSpace n →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun x := fun a => x a/(radiusMonomial ρ a : ℂ)
  map_add' x y := by
    ext a
    change (x a+y a)/(radiusMonomial ρ a : ℂ)=x a/(radiusMonomial ρ a : ℂ)+y a/(radiusMonomial ρ a : ℂ)
    exact add_div _ _ _
  map_smul' c x := by
    ext a
    change (c*x a)/(radiusMonomial ρ a : ℂ)=c*(x a/(radiusMonomial ρ a : ℂ))
    ring

private theorem decoded_term (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (x : CoefficientBanachSpace n) (a : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff a (seriesOfLp ρ x)‖*radiusMonomial ρ a=‖x a‖ := by
  change ‖x a/(radiusMonomial ρ a : ℂ)‖*radiusMonomial ρ a=‖x a‖
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (radius_pos ρ hρ a)]
  exact div_mul_cancel₀ _ (ne_of_gt (radius_pos ρ hρ a))

theorem seriesOfLp_finiteMass (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (x : CoefficientBanachSpace n) : HasFiniteCoefficientMass ρ (seriesOfLp ρ x) := by
  have hx : Summable (fun a : Fin n →₀ ℕ => ‖x a‖) := by
    simpa using (lp.memℓp x).summable (by norm_num : 0<(1 : ENNReal).toReal)
  simpa only [HasFiniteCoefficientMass,decoded_term ρ hρ x] using hx

theorem seriesOfLp_mass (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (x : CoefficientBanachSpace n) : coefficientMass ρ (seriesOfLp ρ x)=‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0<(1 : ENNReal).toReal)]
  simp only [coefficientMass,decoded_term ρ hρ x,ENNReal.toReal_one,Real.rpow_one,div_one]

/-- Literal weighted coefficients of a source with natural absolute coefficient summability. -/
def lpOfSeries (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) : CoefficientBanachSpace n :=
  ⟨fun a => MvPowerSeries.coeff a F*(radiusMonomial ρ a : ℂ), by
    apply (memℓp_gen_iff (by norm_num : 0<(1 : ENNReal).toReal)).mpr
    simpa only [HasFiniteCoefficientMass,ENNReal.toReal_one,Real.rpow_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (radius_pos ρ hρ _)] using hF⟩

theorem seriesOfLp_lpOfSeries (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    seriesOfLp ρ (lpOfSeries ρ hρ F hF)=F := by
  ext a
  change MvPowerSeries.coeff a F*(radiusMonomial ρ a : ℂ)/(radiusMonomial ρ a : ℂ)=MvPowerSeries.coeff a F
  exact mul_div_cancel_right₀ _ (radius_cast_ne ρ hρ a)

theorem lpOfSeries_norm (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ‖lpOfSeries ρ hρ F hF‖=coefficientMass ρ F := by
  rw [←seriesOfLp_mass ρ hρ,seriesOfLp_lpOfSeries]

private theorem perturbation_constant_nonneg (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) : 0≤vertexPerturbationConstant m I B ρ :=
  Finset.sum_nonneg fun a _ => div_nonneg (coefficientMass_nonneg ρ hρ _) (le_of_lt (radius_pos ρ hρ a.val))

private def vertexPerturbationLp (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) :
    CoefficientBanachSpace n →ₗ[ℂ] CoefficientBanachSpace n where
  toFun x := lpOfSeries ρ hρ (vertexPerturbationMap m I B (seriesOfLp ρ x))
    (vertexPerturbation_summable m I B ρ hρ _ (seriesOfLp_finiteMass ρ hρ x) hB)
  map_add' x y := by
    apply lp.ext
    funext a
    change MvPowerSeries.coeff a (vertexPerturbationMap m I B (seriesOfLp ρ (x+y)))*(radiusMonomial ρ a : ℂ)=
      MvPowerSeries.coeff a (vertexPerturbationMap m I B (seriesOfLp ρ x))*(radiusMonomial ρ a : ℂ)+
      MvPowerSeries.coeff a (vertexPerturbationMap m I B (seriesOfLp ρ y))*(radiusMonomial ρ a : ℂ)
    rw [map_add,map_add,map_add,add_mul]
  map_smul' c x := by
    apply lp.ext
    funext a
    change MvPowerSeries.coeff a (vertexPerturbationMap m I B (seriesOfLp ρ (c • x)))*(radiusMonomial ρ a : ℂ)=
      c*(MvPowerSeries.coeff a (vertexPerturbationMap m I B (seriesOfLp ρ x))*(radiusMonomial ρ a : ℂ))
    rw [map_smul,map_smul,map_smul]
    simp only [smul_eq_mul,mul_assoc]

private theorem vertexPerturbationLp_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (x : CoefficientBanachSpace n) :
    ‖vertexPerturbationLp m I B ρ hρ hB x‖≤vertexPerturbationConstant m I B ρ*‖x‖ := by
  change ‖lpOfSeries ρ hρ (vertexPerturbationMap m I B (seriesOfLp ρ x))
    (vertexPerturbation_summable m I B ρ hρ _ (seriesOfLp_finiteMass ρ hρ x) hB)‖≤_
  rw [lpOfSeries_norm,←seriesOfLp_mass ρ hρ x]
  exact vertexPerturbation_bound m I B ρ hρ _ (seriesOfLp_finiteMass ρ hρ x) hB

/-- The SAME literal actual vertex-tail operator on the genuine complete complex coefficient space. -/
def vertexPerturbationCLM (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) :
    CoefficientBanachSpace n →L[ℂ] CoefficientBanachSpace n :=
  (vertexPerturbationLp m I B ρ hρ hB).mkContinuous (vertexPerturbationConstant m I B ρ)
    (vertexPerturbationLp_bound m I B ρ hρ hB)

theorem vertexPerturbationCLM_norm_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) :
    ‖vertexPerturbationCLM m I B ρ hρ hB‖≤vertexPerturbationConstant m I B ρ :=
  ContinuousLinearMap.opNorm_le_bound _ (perturbation_constant_nonneg m I B ρ hρ)
    (vertexPerturbationLp_bound m I B ρ hρ hB)


private theorem seriesOfLp_perturbation (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (x : CoefficientBanachSpace n) :
    seriesOfLp ρ (vertexPerturbationCLM m I B ρ hρ hB x)=
      vertexPerturbationMap m I B (seriesOfLp ρ x) := by
  exact seriesOfLp_lpOfSeries ρ hρ _
    (vertexPerturbation_summable m I B ρ hρ _ (seriesOfLp_finiteMass ρ hρ x) hB)

theorem exists_neumann_vertex_solution (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (hsmall : vertexPerturbationConstant m I B ρ<1)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∃ U : MvPowerSeries (Fin n) ℂ, HasFiniteCoefficientMass ρ U ∧
      U+vertexPerturbationMap m I B U=F ∧
      coefficientMass ρ U≤coefficientMass ρ F/(1-vertexPerturbationConstant m I B ρ) := by
  let T := vertexPerturbationCLM m I B ρ hρ hB
  have hT : ‖-T‖<1 := by
    rw [norm_neg]
    exact lt_of_le_of_lt (vertexPerturbationCLM_norm_le m I B ρ hρ hB) hsmall
  let u : (CoefficientBanachSpace n →L[ℂ] CoefficientBanachSpace n)ˣ := Units.oneSub (-T) hT
  let xF := lpOfSeries ρ hρ F hF
  let x : CoefficientBanachSpace n := (↑u⁻¹ : CoefficientBanachSpace n →L[ℂ] CoefficientBanachSpace n) xF
  have hu : (u : CoefficientBanachSpace n →L[ℂ] CoefficientBanachSpace n)=1+T := by
    dsimp [u]
    rw [Units.val_oneSub,sub_neg_eq_add]
  have hx : x+T x=xF := by
    have hh := congrArg (fun A : CoefficientBanachSpace n →L[ℂ] CoefficientBanachSpace n => A xF) (Units.mul_inv u)
    rw [hu] at hh
    simpa only [mul_apply_eq_comp,add_apply,one_apply_eq_self] using hh
  let U := seriesOfLp ρ x
  have hUeq : U+vertexPerturbationMap m I B U=F := by
    have hh := congrArg (seriesOfLp ρ) hx
    rw [map_add,seriesOfLp_perturbation,seriesOfLp_lpOfSeries] at hh
    exact hh
  refine ⟨U,seriesOfLp_finiteMass ρ hρ x,hUeq,?_⟩
  have hxbound : ‖x‖≤coefficientMass ρ F+vertexPerturbationConstant m I B ρ*‖x‖ := by
    calc
      ‖x‖ = ‖xF-T x‖ := congrArg norm ((eq_sub_iff_add_eq).mpr hx)
      _ ≤ ‖xF‖+‖T x‖ := norm_sub_le _ _
      _ ≤ coefficientMass ρ F+vertexPerturbationConstant m I B ρ*‖x‖ :=
        add_le_add (le_of_eq (lpOfSeries_norm ρ hρ F hF)) (vertexPerturbationLp_bound m I B ρ hρ hB x)
  change coefficientMass ρ (seriesOfLp ρ x)≤_
  rw [seriesOfLp_mass ρ hρ]
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith


/-- Actual owner quotients and canonical remainder, with OUTPUT absolute convergence and bounds. -/
theorem exists_absolute_vertex_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (hsmall : vertexPerturbationConstant m I B ρ<1)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∃ (H : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ) (S : MvPowerSeries (Fin n) ℂ),
      (∀ a, HasFiniteCoefficientMass ρ (H a)) ∧ HasFiniteCoefficientMass ρ S ∧
      F=(∑ a, B.series a*H a)+S ∧ S=HironakaActualFormalVertexDivision.actualFormalRemainder m I F ∧
      (∀ (a : actualInitialVertices m I) (β : Fin n →₀ ℕ),
        HironakaActualFormalVertexDivision.actualDivisionOwner m I (β+a.val)≠some a → MvPowerSeries.coeff β (H a)=0) ∧
      (∀ c∈actualInitialDiagram m I, MvPowerSeries.coeff c S=0) ∧
      coefficientMass ρ S≤coefficientMass ρ F/(1-vertexPerturbationConstant m I B ρ) ∧
      (∀ a, radiusMonomial ρ a.val*coefficientMass ρ (H a)≤
        coefficientMass ρ F/(1-vertexPerturbationConstant m I B ρ)) := by
  obtain ⟨U,hU,hUeq,hUbound⟩ := exists_neumann_vertex_solution m I B ρ hρ hB hsmall F hF
  let H := fun a : actualInitialVertices m I => monomialOwnerQuotient m I a U
  let S := monomialOwnerRemainder m I U
  have hdivision : F=(∑ a, B.series a*H a)+S := by
    rw [←hUeq]
    exact vertexPerturbation_reconstruction m I B U
  have hSnormal : ∀ c∈actualInitialDiagram m I, MvPowerSeries.coeff c S=0 :=
    monomialOwnerRemainder_diagram m I U
  have hSmem : F-S∈I := by
    rw [hdivision,add_sub_cancel_right]
    exact Ideal.sum_mem I (fun a _ => I.mul_mem_right _ (B.mem a))
  refine ⟨H,S,(fun a => monomialOwnerQuotient_summable m I ρ hρ U hU a),
    monomialOwnerRemainder_summable m I ρ hρ U hU,hdivision,
    actualFormalRemainder_unique m I F S hSmem hSnormal,?_,hSnormal,
    (monomialOwnerRemainder_bound m I ρ hρ U hU).trans hUbound,?_⟩
  · intro a β howner
    change (if HironakaActualFormalVertexDivision.actualDivisionOwner m I (β+a.val)=some a
      then MvPowerSeries.coeff (β+a.val) U else 0)=0
    exact if_neg howner
  · intro a
    exact (monomialOwnerQuotient_bound m I ρ hρ U hU a).trans hUbound

theorem actualFormalRemainder_summable_of_tail_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (hsmall : vertexPerturbationConstant m I B ρ<1)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    HasFiniteCoefficientMass ρ (HironakaActualFormalVertexDivision.actualFormalRemainder m I F) := by
  obtain ⟨H,S,hH,hS,hdivision,hcanonical,howner,hnormal,hbound,hbounds⟩ :=
    exists_absolute_vertex_division m I B ρ hρ hB hsmall F hF
  exact hcanonical ▸ hS

private theorem finiteCoefficientMass_monomial (ρ : Fin n → ℝ) (a : Fin n →₀ ℕ) (c : ℂ) :
    HasFiniteCoefficientMass ρ (MvPowerSeries.monomial a c) := by
  apply summable_of_ne_finset_zero (s := {a})
  intro b hb
  have hba : b≠a := by simpa only [Finset.mem_singleton] using hb
  simp [MvPowerSeries.coeff_monomial,hba]

private theorem finiteCoefficientMass_neg (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) : HasFiniteCoefficientMass ρ (-F) := by
  simpa only [HasFiniteCoefficientMass,map_neg,norm_neg] using hF

theorem actualReducedVertexSeries_summable_of_tail_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1))
    (hsmall : vertexPerturbationConstant m I B ρ<1) (a : actualInitialVertices m I) :
    HasFiniteCoefficientMass ρ (actualReducedVertexSeries m I a) := by
  have hM : HasFiniteCoefficientMass ρ (MvPowerSeries.monomial a.val (1 : ℂ)) :=
    finiteCoefficientMass_monomial ρ a.val 1
  have hR : HasFiniteCoefficientMass ρ
      (HironakaActualFormalVertexDivision.actualFormalRemainder m I (MvPowerSeries.monomial a.val (1 : ℂ))) :=
    actualFormalRemainder_summable_of_tail_bound m I B ρ hρ hB hsmall
      (MvPowerSeries.monomial a.val (1 : ℂ)) hM
  unfold actualReducedVertexSeries
  rw [sub_eq_add_neg]
  exact finiteCoefficientMass_add ρ hρ (MvPowerSeries.monomial a.val (1 : ℂ))
    (-(HironakaActualFormalVertexDivision.actualFormalRemainder m I (MvPowerSeries.monomial a.val (1 : ℂ))))
    hM (finiteCoefficientMass_neg ρ _ hR)

end
end Hironaka.HironakaActualVertexNeumannDivision
