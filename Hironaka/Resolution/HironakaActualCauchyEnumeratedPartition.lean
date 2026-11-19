import Hironaka.Resolution.HironakaActualCauchyDiagramPartition

/-! Concrete finite-index quotients and remainder, with their actual unchanged-domain bounds. -/
set_option autoImplicit false
open Set Metric Classical

namespace Hironaka.HironakaActualCauchyEnumeratedPartition

noncomputable section
attribute [local instance] Classical.propDecidable

open HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition

variable {n k : ℕ}

def arrayQuotient (ρ : ℝ) (w : Fin k → CoordinateWord n) (j : Fin k)
    (h : CoordinateSpace n → ℂ) : CoordinateSpace n → ℂ :=
  diagramQuotientAt ρ ((List.ofFn w).take j.val) (w j) h

def arrayRemainder (ρ : ℝ) (w : Fin k → CoordinateWord n)
    (h : CoordinateSpace n → ℂ) : CoordinateSpace n → ℂ :=
  diagramResidual ρ (List.ofFn w) h

private theorem arrayQuotient_zero (ρ : ℝ) (w : Fin (k+1) → CoordinateWord n)
    (h : CoordinateSpace n → ℂ) : arrayQuotient ρ w 0 h = wordQuot ρ (w 0) h := by
  simp only [arrayQuotient,Fin.val_zero,List.take_zero,diagramQuotientAt,diagramResidual]

private theorem arrayQuotient_succ (ρ : ℝ) (w : Fin (k+1) → CoordinateWord n)
    (j : Fin k) (h : CoordinateSpace n → ℂ) :
    arrayQuotient ρ w j.succ h = arrayQuotient ρ (fun i : Fin k => w i.succ) j
      (fun z => h z - wordProjection ρ (w 0) h z) := by
  simp only [arrayQuotient,List.ofFn_succ,Fin.val_succ,List.take_succ_cons,
    diagramQuotientAt,diagramResidual]

theorem array_division_identity (ρ : ℝ) (w : Fin k → CoordinateWord n)
    (h : CoordinateSpace n → ℂ) (z : CoordinateSpace n) :
    h z = ∑ j : Fin k, wordMonomial (w j) z * arrayQuotient ρ w j h z + arrayRemainder ρ w h z := by
  induction k generalizing h with
  | zero => simp [arrayRemainder,diagramResidual]
  | succ k ih =>
    have he := ih (fun i : Fin k => w i.succ) (fun x => h x - wordProjection ρ (w 0) h x)
    rw [Fin.sum_univ_succ]
    simp only [arrayQuotient_zero,arrayQuotient_succ,arrayRemainder,List.ofFn_succ,
      diagramResidual,wordProjection] at he ⊢
    linear_combination he

theorem arrayQuotient_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : Fin k → CoordinateWord n) (j : Fin k) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (arrayQuotient ρ w j h) (ball 0 R) :=
  diagramQuotientAt_differentiableOn hρ hρR _ _ hh

theorem arrayRemainder_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : Fin k → CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (arrayRemainder ρ w h) (ball 0 R) :=
  diagramResidual_differentiableOn hρ hρR _ hh

/-- These simultaneous constants are outputs of the concrete Cauchy constructions. -/
theorem exists_array_partition_bounds {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : Fin k → CoordinateWord n) :
    ∃ (C : Fin k → ℝ) (Cr : ℝ), (∀ j, 0 ≤ C j) ∧ 0 ≤ Cr ∧
      ∀ (M : ℝ) (h : CoordinateSpace n → ℂ), DifferentiableOn ℂ h (ball 0 R) →
        (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
        (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖arrayQuotient ρ w j h z‖ ≤ C j * M) ∧
        ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖arrayRemainder ρ w h z‖ ≤ Cr * M := by
  choose C hC hQ using fun j : Fin k =>
    exists_diagramQuotientAt_bound hρ hρR ((List.ofFn w).take j.val) (w j)
  obtain ⟨Cr,hCr,hR⟩ := exists_diagramResidual_bound hρ hρR (List.ofFn w)
  refine ⟨C,Cr,hC,hCr,?_⟩
  intro M h hh hM
  exact ⟨fun j => hQ j M h hh hM,hR M h hh hM⟩

theorem coeff_arrayQuotientGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : Fin k → CoordinateWord n) (j : Fin k) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (b : Fin n →₀ ℕ) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (arrayQuotient_differentiableOn hρ hρR w j hh))) =
      if AvoidsCones ((List.ofFn w).take j.val) (b + wordExponent (w j)) then
        MvPowerSeries.coeff (b + wordExponent (w j))
          (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 :=
  coeff_diagramQuotientAtGerm hρ hρR _ _ hh b

theorem coeff_arrayRemainderGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (w : Fin k → CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (b : Fin n →₀ ℕ) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (arrayRemainder_differentiableOn hρ hρR w hh))) =
      if AvoidsCones (List.ofFn w) b then MvPowerSeries.coeff b
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 :=
  coeff_diagramResidualGerm hρ hρR _ hh b

private theorem wordMonomial_eq_list_prod (w : CoordinateWord n) (z : CoordinateSpace n) :
    wordMonomial w z = (w.map fun p => z p.1 ^ p.2).prod := by
  induction w with
  | nil => rfl
  | cons p w ih => rcases p with ⟨i,d⟩; simp only [wordMonomial,List.map_cons,List.prod_cons,ih]

theorem wordMonomial_wordOfExponent (a : Fin n →₀ ℕ) (z : CoordinateSpace n) :
    wordMonomial (wordOfExponent a) z = ∏ i : Fin n, z i ^ a i := by
  rw [wordMonomial_eq_list_prod]
  simp only [wordOfExponent,List.map_ofFn,List.prod_ofFn,Function.comp_apply]

end

end Hironaka.HironakaActualCauchyEnumeratedPartition
