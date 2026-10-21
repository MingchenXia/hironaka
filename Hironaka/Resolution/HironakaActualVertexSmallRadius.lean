/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualVertexNeumannDivision
import Hironaka.Resolution.HironakaActualDegLexPositiveWeights
/-!
# Actual common small radius for the prescribed deg-lex vertex family

Ordinary weighted coefficient summability decays under a literal anisotropic
radius. Genuine bounded deg-lex positive weights and actual monicity produce
the strict tail support gap internally. The concrete t=1/(c_eta+2) then gives
ONE positive smaller radius with computed actual tail constant < 1, before all
vertices; the actual Neumann theorem yields canonical reduced vertex convergence.
No caller-selected weight, small-norm, inverse or convergence certificate is
assumed. Initial fixed-family tail coefficient mass at a positive radius is the
natural norm-domain input; its original holomorphic Taylor dictionary remains
separate.

Blueprint: `hironaka-actual-vertex-small-radius-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualVertexSmallRadius
noncomputable section
open HironakaActualMonomialDivisionBounds HironakaActualAnalyticVertexPerturbation
  HironakaActualVertexNeumannDivision HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
variable {n : ℕ}

/-- A genuine coordinatewise anisotropic decrease of the actual positive polyradius. -/
def anisotropicRadius (η : Fin n → ℝ) (w : Fin n → ℕ) (t : ℝ) : Fin n → ℝ := fun i => η i*t^(w i)

private theorem radius_pos (η : Fin n → ℝ) (hη : ∀ i,0<η i) (a : Fin n →₀ ℕ) :
    0<radiusMonomial η a := Finset.prod_pos fun i _ => pow_pos (hη i) _

private theorem anisotropic_pos (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (w : Fin n → ℕ) (t : ℝ) (ht : 0<t) : ∀ i,0<anisotropicRadius η w t i :=
  fun i => mul_pos (hη i) (pow_pos ht _)

private theorem anisotropic_le (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (w : Fin n → ℕ) (t : ℝ) (ht : 0<t) (ht1 : t<1) : ∀ i,anisotropicRadius η w t i≤η i := by
  intro i
  change η i*t^(w i)≤η i
  exact mul_le_of_le_one_right (le_of_lt (hη i)) (pow_le_one₀ (le_of_lt ht) (le_of_lt ht1))

theorem radiusMonomial_anisotropic (η : Fin n → ℝ) (w : Fin n → ℕ) (t : ℝ)
    (a : Fin n →₀ ℕ) :
    radiusMonomial (anisotropicRadius η w t) a=radiusMonomial η a*t^(Finsupp.weight w a) := by
  simp only [radiusMonomial,anisotropicRadius,mul_pow,←pow_mul,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,Finsupp.weight_eq_sum,smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

private theorem radius_mono (ρ η : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (hle : ∀ i,ρ i≤η i)
    (a : Fin n →₀ ℕ) : radiusMonomial ρ a≤radiusMonomial η a :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (le_of_lt (hρ i)) _)
    (fun i _ => pow_le_pow_left₀ (le_of_lt (hρ i)) (hle i) _)

theorem finiteCoefficientMass_mono (ρ η : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (hle : ∀ i,ρ i≤η i) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass η F) : HasFiniteCoefficientMass ρ F := by
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
    (fun a => mul_le_mul_of_nonneg_left (radius_mono ρ η hρ hle a) (norm_nonneg _)) hF

theorem coefficientMass_shrink_of_weight_gap (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (w : Fin n → ℕ) (t : ℝ) (ht : 0<t) (ht1 : t<1) (k : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass η F)
    (hgap : ∀ a : Fin n →₀ ℕ, MvPowerSeries.coeff a F≠0 → k<Finsupp.weight w a) :
    coefficientMass (anisotropicRadius η w t) F≤t^(k+1)*coefficientMass η F := by
  have hρ := anisotropic_pos η hη w t ht
  have hFρ := finiteCoefficientMass_mono _ η hρ (anisotropic_le η hη w t ht ht1) F hF
  have hterm (a : Fin n →₀ ℕ) :
      ‖MvPowerSeries.coeff a F‖*radiusMonomial (anisotropicRadius η w t) a≤
        t^(k+1)*(‖MvPowerSeries.coeff a F‖*radiusMonomial η a) := by
    by_cases ha : MvPowerSeries.coeff a F=0
    · simp [ha]
    · rw [radiusMonomial_anisotropic]
      have hp := pow_le_pow_of_le_one (le_of_lt ht) (le_of_lt ht1) (Nat.succ_le_of_lt (hgap a ha))
      calc
        _ = (‖MvPowerSeries.coeff a F‖*radiusMonomial η a)*t^(Finsupp.weight w a) := by ring
        _ ≤ (‖MvPowerSeries.coeff a F‖*radiusMonomial η a)*t^(k+1) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos η hη a)))
        _ = _ := by ring
  calc
    _ ≤ ∑' a : Fin n →₀ ℕ, t^(k+1)*(‖MvPowerSeries.coeff a F‖*radiusMonomial η a) :=
      Summable.tsum_le_tsum hterm hFρ (hF.mul_left _)
    _ = _ := tsum_mul_left

theorem vertexPerturbationConstant_shrink_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass η (B.series a-MvPowerSeries.monomial a.val 1))
    (w : Fin n → ℕ)
    (hgap : ∀ (a : actualInitialVertices m I) (β : Fin n →₀ ℕ),
      MvPowerSeries.coeff β (B.series a-MvPowerSeries.monomial a.val 1)≠0 →
        Finsupp.weight w a.val<Finsupp.weight w β)
    (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    vertexPerturbationConstant m I B (anisotropicRadius η w t)≤t*vertexPerturbationConstant m I B η := by
  unfold vertexPerturbationConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply (div_le_iff₀ (radius_pos _ (anisotropic_pos η hη w t ht) a.val)).mpr
  calc
    _ ≤ t^(Finsupp.weight w a.val+1)*coefficientMass η (B.series a-MvPowerSeries.monomial a.val 1) :=
      coefficientMass_shrink_of_weight_gap η hη w t ht ht1 _ _ (hB a) (hgap a)
    _ = _ := by
      rw [radiusMonomial_anisotropic,pow_succ]
      field_simp [ne_of_gt (radius_pos η hη a.val)]


private theorem actual_tail_later (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (a : actualInitialVertices m I) (β : Fin n →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff β (B.series a-MvPowerSeries.monomial a.val 1)≠0) :
    m.toSyn a.val<m.toSyn β := by
  by_cases hba : β=a.val
  · subst β
    exact False.elim (hcoeff (by simp only [map_sub,B.monic,MvPowerSeries.coeff_monomial,ite_true,sub_self]))
  · have hBcoeff : MvPowerSeries.coeff β (B.series a)≠0 := by
      simpa only [map_sub,MvPowerSeries.coeff_monomial,if_neg hba,sub_zero] using hcoeff
    have hnot : ¬m.toSyn β<m.toSyn a.val := fun h => hBcoeff (B.lower a β h)
    exact lt_of_le_of_ne (le_of_not_gt hnot) (fun h => hba (m.toSyn.injective h.symm))

private theorem exists_vertex_small_radius_of_weight_gap (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass η (B.series a-MvPowerSeries.monomial a.val 1))
    (w : Fin n → ℕ)
    (hgap : ∀ (a : actualInitialVertices m I) (β : Fin n →₀ ℕ),
      MvPowerSeries.coeff β (B.series a-MvPowerSeries.monomial a.val 1)≠0 →
        Finsupp.weight w a.val<Finsupp.weight w β) :
    ∃ ρ : Fin n → ℝ, (∀ i,0<ρ i) ∧ (∀ i,ρ i≤η i) ∧
      (∀ a : actualInitialVertices m I,
        HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) ∧
      vertexPerturbationConstant m I B ρ<1 := by
  let c := vertexPerturbationConstant m I B η
  have hc : 0≤c := Finset.sum_nonneg fun a _ =>
    div_nonneg (coefficientMass_nonneg η hη _) (le_of_lt (radius_pos η hη a.val))
  have hden : 0<c+2 := by linarith
  let t : ℝ := 1/(c+2)
  have ht : 0<t := one_div_pos.mpr hden
  have hprod : t*(c+2)=1 := div_mul_cancel₀ _ (ne_of_gt hden)
  have ht1 : t<1 := by nlinarith [mul_nonneg (le_of_lt ht) hc]
  have htc : t*c<1 := by nlinarith
  let ρ := anisotropicRadius η w t
  have hρ : ∀ i,0<ρ i := anisotropic_pos η hη w t ht
  have hle : ∀ i,ρ i≤η i := anisotropic_le η hη w t ht ht1
  refine ⟨ρ,hρ,hle,(fun a => finiteCoefficientMass_mono ρ η hρ hle _ (hB a)),?_⟩
  exact lt_of_le_of_lt (vertexPerturbationConstant_shrink_le m I B η hη hB w hgap t ht ht1) htc


/-- Actual monicity and genuine bounded deg-lex separation PRODUCE strict tail weights. -/
theorem exists_actual_vertex_tail_weights (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n)) I) :
    ∃ w : Fin n → ℕ,(∀ i,0<w i) ∧
      ∀ (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) (β : Fin n →₀ ℕ),
        MvPowerSeries.coeff β (B.series a-MvPowerSeries.monomial a.val 1)≠0 →
          Finsupp.weight w a.val<Finsupp.weight w β := by
  let D := (actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I).sup Finsupp.degree
  obtain ⟨w,hw,horder⟩ := HironakaActualDegLexPositiveWeights.exists_positive_weights_of_bounded_degLex n D
  refine ⟨w,hw,?_⟩
  intro a β hcoeff
  exact horder a.val β (Finset.le_sup a.property)
    (actual_tail_later (MonomialOrder.degLex (σ := Fin n)) I B a β hcoeff)

/-- ONE actual smaller radius, with internally derived computed perturbation constant < 1. -/
theorem exists_actual_vertex_small_radius (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n)) I)
    (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (hB : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I,
      HasFiniteCoefficientMass η (B.series a-MvPowerSeries.monomial a.val 1)) :
    ∃ ρ : Fin n → ℝ, (∀ i,0<ρ i) ∧ (∀ i,ρ i≤η i) ∧
      (∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I,
        HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) ∧
      vertexPerturbationConstant (MonomialOrder.degLex (σ := Fin n)) I B ρ<1 := by
  obtain ⟨w,hw,hgap⟩ := exists_actual_vertex_tail_weights I B
  exact exists_vertex_small_radius_of_weight_gap (MonomialOrder.degLex (σ := Fin n)) I B η hη hB w hgap

/-- The canonical reduced series of the SAME whole ideal converge on one internally chosen radius. -/
theorem exists_actual_reduced_vertices_finite_mass (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n)) I)
    (η : Fin n → ℝ) (hη : ∀ i,0<η i)
    (hB : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I,
      HasFiniteCoefficientMass η (B.series a-MvPowerSeries.monomial a.val 1)) :
    ∃ ρ : Fin n → ℝ, (∀ i,0<ρ i) ∧ (∀ i,ρ i≤η i) ∧
      ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I,
        HasFiniteCoefficientMass ρ
          (HironakaActualReducedFormalStandardBasis.actualReducedVertexSeries
            (MonomialOrder.degLex (σ := Fin n)) I a) := by
  obtain ⟨ρ,hρ,hle,hBρ,hsmall⟩ := exists_actual_vertex_small_radius I B η hη hB
  exact ⟨ρ,hρ,hle,fun a => actualReducedVertexSeries_summable_of_tail_bound
    (MonomialOrder.degLex (σ := Fin n)) I B ρ hρ hBρ hsmall a⟩

end
end Hironaka.HironakaActualVertexSmallRadius
