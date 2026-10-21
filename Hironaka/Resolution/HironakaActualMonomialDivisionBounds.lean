/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
/-!
# Bounded actual monomial-partition division in the complex absolute coefficient norm

The actual finite diagram-owner partition gives literal C-linear quotient
and remainder maps and the whole leading-monomial division identity. Natural
source weighted absolute summability implies quotient/remainder convergence
and sharp bounds, hence absolute complex evaluations on the polydisc.
This does not yet assert a holomorphic-germ Taylor-radius dictionary or
convergence of division by perturbed analytic vertex generators.

Blueprint: `hironaka-actual-monomial-division-bounds-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualMonomialDivisionBounds
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
variable {n : ℕ}

def monomialOwnerQuotient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun F := fun β => if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) F else 0
  map_add' F G := by
    ext β
    change (if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) (F+G) else 0)=
      (if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) F else 0)+
      (if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) G else 0)
    split_ifs <;> simp
  map_smul' c F := by
    ext β
    change (if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) (c • F) else 0)=
      c*(if actualDivisionOwner m I (β+a.val)=some a then MvPowerSeries.coeff (β+a.val) F else 0)
    split_ifs <;> simp

def monomialOwnerRemainder (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun F := fun β => if actualDivisionOwner m I β=none then MvPowerSeries.coeff β F else 0
  map_add' F G := by
    ext β
    change (if actualDivisionOwner m I β=none then MvPowerSeries.coeff β (F+G) else 0)=
      (if actualDivisionOwner m I β=none then MvPowerSeries.coeff β F else 0)+
      (if actualDivisionOwner m I β=none then MvPowerSeries.coeff β G else 0)
    split_ifs <;> simp
  map_smul' c F := by
    ext β
    change (if actualDivisionOwner m I β=none then MvPowerSeries.coeff β (c • F) else 0)=
      c*(if actualDivisionOwner m I β=none then MvPowerSeries.coeff β F else 0)
    split_ifs <;> simp

private theorem coefficient_monomial_owner (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (MvPowerSeries.monomial a.val 1*monomialOwnerQuotient m I a F)=
      if actualDivisionOwner m I c=some a then MvPowerSeries.coeff c F else 0 := by
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hac : a.val≤c
  · rw [if_pos hac,one_mul]
    change (if actualDivisionOwner m I (c-a.val+a.val)=some a then MvPowerSeries.coeff (c-a.val+a.val) F else 0)=_
    rw [tsub_add_cancel_of_le hac]
  · rw [if_neg hac]
    have hne : actualDivisionOwner m I c≠some a := fun h => hac (actualDivisionOwner_le m I c a h)
    rw [if_neg hne]

theorem monomial_owner_division (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) :
    F=(∑ a : actualInitialVertices m I, MvPowerSeries.monomial a.val 1*monomialOwnerQuotient m I a F)+
      monomialOwnerRemainder m I F := by
  apply MvPowerSeries.ext
  intro c
  rw [map_add,map_sum]
  simp_rw [coefficient_monomial_owner]
  change MvPowerSeries.coeff c F=(∑ a : actualInitialVertices m I,
    if actualDivisionOwner m I c=some a then MvPowerSeries.coeff c F else 0)+
      (if actualDivisionOwner m I c=none then MvPowerSeries.coeff c F else 0)
  cases ho : actualDivisionOwner m I c with
  | none => simp
  | some a => simp

theorem monomialOwnerRemainder_diagram (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (monomialOwnerRemainder m I F)=0 := by
  change (if actualDivisionOwner m I c=none then MvPowerSeries.coeff c F else 0)=0
  rw [if_neg (fun h => (actualDivisionOwner_eq_none_iff m I c).mp h hc)]

def radiusMonomial (ρ : Fin n → ℝ) (a : Fin n →₀ ℕ) : ℝ := ∏ i, (ρ i)^(a i)

def coefficientMass (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ) : ℝ :=
  ∑' a : Fin n →₀ ℕ, ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a

def HasFiniteCoefficientMass (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ) : Prop :=
  Summable (fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a)

private theorem radiusMonomial_pos (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i) (a : Fin n →₀ ℕ) :
    0<radiusMonomial ρ a := Finset.prod_pos fun i _ => pow_pos (hρ i) _

private theorem radiusMonomial_add (ρ : Fin n → ℝ) (a b : Fin n →₀ ℕ) :
    radiusMonomial ρ (a+b)=radiusMonomial ρ a*radiusMonomial ρ b := by
  simp only [radiusMonomial,Finsupp.add_apply,pow_add,Finset.prod_mul_distrib]

private theorem scaled_quotient_term_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (a : actualInitialVertices m I) (β : Fin n →₀ ℕ) :
    radiusMonomial ρ a.val*(‖MvPowerSeries.coeff β (monomialOwnerQuotient m I a F)‖*radiusMonomial ρ β)≤
      ‖MvPowerSeries.coeff (β+a.val) F‖*radiusMonomial ρ (β+a.val) := by
  change radiusMonomial ρ a.val*((‖if actualDivisionOwner m I (β+a.val)=some a then
    MvPowerSeries.coeff (β+a.val) F else 0‖)*radiusMonomial ρ β)≤_
  split_ifs
  · rw [radiusMonomial_add]
    nlinarith [norm_nonneg (MvPowerSeries.coeff (β+a.val) F)]
  · simp only [norm_zero,zero_mul,mul_zero]
    exact mul_nonneg (norm_nonneg _) (le_of_lt (radiusMonomial_pos ρ hρ _))

theorem monomialOwnerQuotient_summable (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (a : actualInitialVertices m I) : HasFiniteCoefficientMass ρ (monomialOwnerQuotient m I a F) := by
  have hShift := hF.comp_injective (show Function.Injective (fun β : Fin n →₀ ℕ => β+a.val) from
    fun _ _ h => add_right_cancel h)
  have hScaled : Summable (fun β : Fin n →₀ ℕ => radiusMonomial ρ a.val*
      (‖MvPowerSeries.coeff β (monomialOwnerQuotient m I a F)‖*radiusMonomial ρ β)) := by
    apply Summable.of_nonneg_of_le (fun β => by
      exact mul_nonneg (le_of_lt (radiusMonomial_pos ρ hρ _))
        (mul_nonneg (norm_nonneg _) (le_of_lt (radiusMonomial_pos ρ hρ _))))
      (scaled_quotient_term_le m I ρ hρ F a) hShift
  exact (summable_mul_left_iff (ne_of_gt (radiusMonomial_pos ρ hρ a.val))).mp hScaled

theorem monomialOwnerQuotient_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F)
    (a : actualInitialVertices m I) :
    radiusMonomial ρ a.val*coefficientMass ρ (monomialOwnerQuotient m I a F)≤coefficientMass ρ F := by
  have hShift := hF.comp_injective (show Function.Injective (fun β : Fin n →₀ ℕ => β+a.val) from
    fun _ _ h => add_right_cancel h)
  have hQ := monomialOwnerQuotient_summable m I ρ hρ F hF a
  calc
    _ = ∑' β : Fin n →₀ ℕ, radiusMonomial ρ a.val*
        (‖MvPowerSeries.coeff β (monomialOwnerQuotient m I a F)‖*radiusMonomial ρ β) := tsum_mul_left.symm
    _ ≤ ∑' β : Fin n →₀ ℕ, ‖MvPowerSeries.coeff (β+a.val) F‖*radiusMonomial ρ (β+a.val) :=
      Summable.tsum_le_tsum (scaled_quotient_term_le m I ρ hρ F a) (hQ.mul_left _) hShift
    _ ≤ _ := tsum_comp_le_tsum_of_inj hF
      (fun β => mul_nonneg (norm_nonneg _) (le_of_lt (radiusMonomial_pos ρ hρ β)))
        (fun _ _ h => add_right_cancel h)


private theorem remainder_term_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (β : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff β (monomialOwnerRemainder m I F)‖*radiusMonomial ρ β≤
      ‖MvPowerSeries.coeff β F‖*radiusMonomial ρ β := by
  change ‖if actualDivisionOwner m I β=none then MvPowerSeries.coeff β F else 0‖*radiusMonomial ρ β≤_
  split_ifs
  · exact le_rfl
  · simp only [norm_zero,zero_mul]
    exact mul_nonneg (norm_nonneg _) (le_of_lt (radiusMonomial_pos ρ hρ _))

theorem monomialOwnerRemainder_summable (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    HasFiniteCoefficientMass ρ (monomialOwnerRemainder m I F) := by
  exact Summable.of_nonneg_of_le
    (fun β => mul_nonneg (norm_nonneg _) (le_of_lt (radiusMonomial_pos ρ hρ β)))
    (remainder_term_le m I ρ hρ F) hF

theorem monomialOwnerRemainder_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    coefficientMass ρ (monomialOwnerRemainder m I F)≤coefficientMass ρ F := by
  exact Summable.tsum_le_tsum (remainder_term_le m I ρ hρ F)
    (monomialOwnerRemainder_summable m I ρ hρ F hF) hF

theorem summable_polydisc_evaluation (ρ : Fin n → ℝ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass ρ F) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖≤ρ i) :
    Summable (fun a : Fin n →₀ ℕ => ‖MvPowerSeries.coeff a F*∏ i, (z i)^(a i)‖) ∧
    Summable (fun a : Fin n →₀ ℕ => MvPowerSeries.coeff a F*∏ i, (z i)^(a i)) ∧
    (∑' a : Fin n →₀ ℕ, ‖MvPowerSeries.coeff a F*∏ i, (z i)^(a i)‖)≤coefficientMass ρ F := by
  have hBound (a : Fin n →₀ ℕ) :
      ‖MvPowerSeries.coeff a F*∏ i, (z i)^(a i)‖≤‖MvPowerSeries.coeff a F‖*radiusMonomial ρ a := by
    simp only [norm_mul,norm_prod,norm_pow,radiusMonomial]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg _) _)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) _)
  have hNorm := Summable.of_nonneg_of_le (fun a => norm_nonneg _) hBound hF
  exact ⟨hNorm,hF.of_norm_bounded hBound,Summable.tsum_le_tsum hBound hNorm hF⟩

end
end Hironaka.HironakaActualMonomialDivisionBounds
