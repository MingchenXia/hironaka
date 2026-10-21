/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMonomialDivisionBounds
import Hironaka.Resolution.HironakaActualReducedBasisDivision
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Actual complex absolute coefficient convolution and finite vertex perturbation

Ordinary Archimedean Cauchy products preserve the absolute coefficient domain
and have the expected product bound. For the SAME actual monic vertex family,
the literal finite tail operator is complex-linear, preserves that domain,
and has its explicit sharp sum-of-tail-ratios bound. Its whole reconstruction
identity is independent of convergence. No output-convergence, small-radius,
Neumann inversion or prepared-family certificate is assumed.

Blueprint: `hironaka-actual-analytic-vertex-perturbation-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualAnalyticVertexPerturbation
noncomputable section
open HironakaActualMonomialDivisionBounds HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision
variable {n : ℕ}

private theorem radius_pos (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (a : Fin n →₀ ℕ) :
    0<radiusMonomial ρ a := Finset.prod_pos fun i _ => pow_pos (hρ i) _

private theorem radius_add (ρ : Fin n → ℝ) (a b : Fin n →₀ ℕ) :
    radiusMonomial ρ (a+b)=radiusMonomial ρ a*radiusMonomial ρ b := by
  simp only [radiusMonomial,Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]

theorem coefficientMass_nonneg (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) : 0≤coefficientMass ρ F :=
  tsum_nonneg fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a))

private theorem add_term_le (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff a (F+G)‖*radiusMonomial ρ a≤
      ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a+
      ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a := by
  rw [map_add,←add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (le_of_lt (radius_pos ρ hρ a))

theorem finiteCoefficientMass_add (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G) :
    HasFiniteCoefficientMass ρ (F+G) :=
  Summable.of_nonneg_of_le
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
    (add_term_le ρ hρ F G) (hF.add hG)

theorem coefficientMass_add_le (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G) :
    coefficientMass ρ (F+G)≤coefficientMass ρ F+coefficientMass ρ G := by
  calc
    _ ≤ ∑' a : Fin n →₀ ℕ, (‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a+
        ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) :=
      Summable.tsum_le_tsum (add_term_le ρ hρ F G) (finiteCoefficientMass_add ρ hρ F G hF hG) (hF.add hG)
    _ = _ := hF.tsum_add hG

private theorem mul_term_le (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff a (F*G)‖*radiusMonomial ρ a≤
      ∑ p ∈ Finset.antidiagonal a,
        (‖MvPowerSeries.coeff p.1 F‖*radiusMonomial ρ p.1)*
        (‖MvPowerSeries.coeff p.2 G‖*radiusMonomial ρ p.2) := by
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ (∑ p ∈ Finset.antidiagonal a, ‖MvPowerSeries.coeff p.1 F*MvPowerSeries.coeff p.2 G‖)*
        radiusMonomial ρ a :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (le_of_lt (radius_pos ρ hρ a))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.mem_antidiagonal.mp hp,radius_add,norm_mul]
      ring

theorem finiteCoefficientMass_mul (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G) :
    HasFiniteCoefficientMass ρ (F*G) := by
  have hPair : Summable (fun p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) =>
      (‖MvPowerSeries.coeff p.1 F‖*radiusMonomial ρ p.1)*
      (‖MvPowerSeries.coeff p.2 G‖*radiusMonomial ρ p.2)) :=
    Summable.mul_of_nonneg (f := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)
      (g := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) hF hG
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
    (mul_term_le ρ hρ F G) (summable_sum_mul_antidiagonal_of_summable_mul
      (f := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)
      (g := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) hPair)

theorem coefficientMass_mul_le (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F G : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (hG : HasFiniteCoefficientMass ρ G) :
    coefficientMass ρ (F*G)≤coefficientMass ρ F*coefficientMass ρ G := by
  have hPair : Summable (fun p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) =>
      (‖MvPowerSeries.coeff p.1 F‖*radiusMonomial ρ p.1)*
      (‖MvPowerSeries.coeff p.2 G‖*radiusMonomial ρ p.2)) :=
    Summable.mul_of_nonneg (f := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)
      (g := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) hF hG
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
    (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (radius_pos ρ hρ a)))
  calc
    _ ≤ ∑' a : Fin n →₀ ℕ, ∑ p ∈ Finset.antidiagonal a,
        (‖MvPowerSeries.coeff p.1 F‖*radiusMonomial ρ p.1)*
        (‖MvPowerSeries.coeff p.2 G‖*radiusMonomial ρ p.2) :=
      Summable.tsum_le_tsum (mul_term_le ρ hρ F G) (finiteCoefficientMass_mul ρ hρ F G hF hG)
        (summable_sum_mul_antidiagonal_of_summable_mul
      (f := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)
      (g := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) hPair)
    _ = _ := (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (f := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)
      (g := fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a G‖*radiusMonomial ρ a) hF hG hPair).symm

theorem finiteCoefficientMass_sum {ι : Type*} (s : Finset ι)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (F : ι → MvPowerSeries (Fin n) ℂ)
    (hF : ∀ i∈s, HasFiniteCoefficientMass ρ (F i)) :
    HasFiniteCoefficientMass ρ (∑ i∈s, F i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,HasFiniteCoefficientMass,map_zero,norm_zero,zero_mul,summable_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact finiteCoefficientMass_add ρ hρ _ _ (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem coefficientMass_sum_le {ι : Type*} (s : Finset ι)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (F : ι → MvPowerSeries (Fin n) ℂ)
    (hF : ∀ i∈s, HasFiniteCoefficientMass ρ (F i)) :
    coefficientMass ρ (∑ i∈s, F i)≤∑ i∈s, coefficientMass ρ (F i) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficientMass]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (coefficientMass_add_le ρ hρ _ _ (hF i (Finset.mem_insert_self i s))
      (finiteCoefficientMass_sum s ρ hρ F fun j hj => hF j (Finset.mem_insert_of_mem hj))).trans
        (add_le_add le_rfl (ih fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The actual finite generator-tail perturbation of the whole diagram-owner division. -/
def vertexPerturbationMap (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily m I) : MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ :=
  ∑ a : actualInitialVertices m I,
    (LinearMap.mulLeft ℂ (B.series a-MvPowerSeries.monomial a.val 1)).comp (monomialOwnerQuotient m I a)

/-- Literal finite sum of the actual generator-tail masses, scaled by their vertex radii. -/
def vertexPerturbationConstant (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily m I) (ρ : Fin n → ℝ) : ℝ :=
  ∑ a : actualInitialVertices m I,
    coefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)/radiusMonomial ρ a.val

private theorem vertexPerturbationMap_apply (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) :
    vertexPerturbationMap m I B F=∑ a : actualInitialVertices m I,
      (B.series a-MvPowerSeries.monomial a.val 1)*monomialOwnerQuotient m I a F := by
  simp [vertexPerturbationMap]

theorem vertexPerturbation_summable (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) :
    HasFiniteCoefficientMass ρ (vertexPerturbationMap m I B F) := by
  rw [vertexPerturbationMap_apply]
  exact finiteCoefficientMass_sum Finset.univ ρ hρ _ fun a _ =>
    finiteCoefficientMass_mul ρ hρ _ _ (hB a) (monomialOwnerQuotient_summable m I ρ hρ F hF a)

theorem vertexPerturbation_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F)
    (hB : ∀ a : actualInitialVertices m I,
      HasFiniteCoefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)) :
    coefficientMass ρ (vertexPerturbationMap m I B F)≤
      vertexPerturbationConstant m I B ρ*coefficientMass ρ F := by
  rw [vertexPerturbationMap_apply,vertexPerturbationConstant,Finset.sum_mul]
  apply le_trans (coefficientMass_sum_le Finset.univ ρ hρ _ (fun a _ =>
    finiteCoefficientMass_mul ρ hρ _ _ (hB a) (monomialOwnerQuotient_summable m I ρ hρ F hF a)))
  apply Finset.sum_le_sum
  intro a _
  apply le_trans (coefficientMass_mul_le ρ hρ _ _ (hB a) (monomialOwnerQuotient_summable m I ρ hρ F hF a))
  have hQ : coefficientMass ρ (monomialOwnerQuotient m I a F)≤
      coefficientMass ρ F/radiusMonomial ρ a.val :=
    (le_div_iff₀ (radius_pos ρ hρ a.val)).mpr
      (by simpa only [mul_comm] using monomialOwnerQuotient_bound m I ρ hρ F hF a)
  calc
    _ ≤ coefficientMass ρ (B.series a-MvPowerSeries.monomial a.val 1)*
        (coefficientMass ρ F/radiusMonomial ρ a.val) :=
      mul_le_mul_of_nonneg_left hQ (coefficientMass_nonneg ρ hρ _)
    _ = _ := by ring

theorem vertexPerturbation_reconstruction (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) :
    F+vertexPerturbationMap m I B F=
      (∑ a : actualInitialVertices m I, B.series a*monomialOwnerQuotient m I a F)+
        monomialOwnerRemainder m I F := by
  rw [vertexPerturbationMap_apply]
  have he := monomial_owner_division m I F
  calc
    _ = (∑ a : actualInitialVertices m I,
          MvPowerSeries.monomial a.val 1*monomialOwnerQuotient m I a F)+
        monomialOwnerRemainder m I F+
        ∑ a : actualInitialVertices m I,
          (B.series a-MvPowerSeries.monomial a.val 1)*monomialOwnerQuotient m I a F := by
      conv_lhs => lhs; rw [he]
    _ = _ := by
      rw [add_right_comm,←Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring

end
end Hironaka.HironakaActualAnalyticVertexPerturbation
