import Hironaka.Resolution.HironakaActualCauchyMonomialDivision

/-!
# The actual ordered finite Cauchy partition

Finite subtraction/composition of the concrete monomial cone operators gives
actual holomorphic quotients and remainder on a single unchanged polydisc.
Every support and bound below is a conclusion about these actual functions.
-/

set_option autoImplicit false
open Set Metric

namespace Hironaka.HironakaActualCauchyDiagramPartition

noncomputable section

attribute [local instance] Classical.propDecidable

open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision

variable {n : ℕ}

def AvoidsCones (L : List (CoordinateWord n)) (a : Fin n →₀ ℕ) : Prop :=
  ∀ w ∈ L, ¬ wordExponent w ≤ a

private theorem avoidsCones_cons (w : CoordinateWord n) (L : List (CoordinateWord n))
    (a : Fin n →₀ ℕ) :
    AvoidsCones (w :: L) a ↔ ¬ wordExponent w ≤ a ∧ AvoidsCones L a := by
  simp only [AvoidsCones,List.mem_cons,forall_eq_or_imp]

def diagramResidual (ρ : ℝ) : List (CoordinateWord n) →
    (CoordinateSpace n → ℂ) → CoordinateSpace n → ℂ
  | [],h => h
  | w :: L,h => diagramResidual ρ L (fun z => h z - wordProjection ρ w h z)

def diagramQuotientAt (ρ : ℝ) (L : List (CoordinateWord n)) (w : CoordinateWord n)
    (h : CoordinateSpace n → ℂ) : CoordinateSpace n → ℂ :=
  wordQuot ρ w (diagramResidual ρ L h)

def diagramPieceAt (ρ : ℝ) (L : List (CoordinateWord n)) (w : CoordinateWord n)
    (h : CoordinateSpace n → ℂ) : CoordinateSpace n → ℂ :=
  wordProjection ρ w (diagramResidual ρ L h)

def diagramPieces (ρ : ℝ) : List (CoordinateWord n) →
    (CoordinateSpace n → ℂ) → List (CoordinateSpace n → ℂ)
  | [],_ => []
  | w :: L,h => wordProjection ρ w h ::
      diagramPieces ρ L (fun z => h z - wordProjection ρ w h z)

theorem diagramResidual_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (diagramResidual ρ L h) (ball 0 R) := by
  induction L generalizing h with
  | nil => exact hh
  | cons w L ih => exact ih (hh.sub (wordProjection_differentiableOn hρ hρR w hh))

theorem exists_diagramResidual_bound {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (h : CoordinateSpace n → ℂ),
      DifferentiableOn ℂ h (ball 0 R) →
      (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖diagramResidual ρ L h z‖ ≤ C * M := by
  induction L with
  | nil =>
    refine ⟨1,zero_le_one,?_⟩
    intro M h _hh hM z hz
    simpa only [diagramResidual,one_mul] using hM z hz
  | cons w L ih =>
    obtain ⟨Cp,hCp,hp⟩ := exists_wordProjection_bound hρ hρR w
    obtain ⟨Cr,hCr,hr⟩ := ih
    refine ⟨Cr * (1 + Cp),mul_nonneg hCr (by positivity),?_⟩
    intro M h hh hM z hz
    have hhs := hh.sub (wordProjection_differentiableOn hρ hρR w hh)
    have hMs : ∀ x ∈ ball (0 : CoordinateSpace n) R,
        ‖h x - wordProjection ρ w h x‖ ≤ (1 + Cp) * M := by
      intro x hx
      calc
        _ ≤ ‖h x‖ + ‖wordProjection ρ w h x‖ := norm_sub_le _ _
        _ ≤ M + Cp * M := add_le_add (hM x hx) (hp M h hh hM x hx)
        _ = (1 + Cp) * M := by ring
    have hres := hr ((1 + Cp) * M) (fun x => h x - wordProjection ρ w h x) hhs hMs z hz
    change ‖diagramResidual ρ L (fun x => h x - wordProjection ρ w h x) z‖ ≤
      (Cr * (1 + Cp)) * M
    exact hres.trans_eq (mul_assoc Cr (1 + Cp) M).symm

private theorem modelGerm_sub {R : ℝ} (hR : 0 < R)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) :
    modelGerm hR (hf.sub hg) = modelGerm hR hf - modelGerm hR hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z - modelFunction g z) _ = _
  exact HolGerm.mk_sub _ _ _ _

/-- The true residual function, not an input formal filter, produces the entire mask. -/
theorem coeff_diagramResidualGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (diagramResidual_differentiableOn hρ hρR L hh))) =
      if AvoidsCones L a then MvPowerSeries.coeff a
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 := by
  induction L generalizing h with
  | nil => simp only [diagramResidual,AvoidsCones,List.not_mem_nil,false_implies,forall_const,ite_true]
  | cons w L ih =>
    have hp := wordProjection_differentiableOn hρ hρR w hh
    change MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
      (modelGerm (hρ.trans hρR) (diagramResidual_differentiableOn hρ hρR L (hh.sub hp)))) = _
    rw [ih (hh.sub hp),modelGerm_sub (hρ.trans hρR) hh hp,map_sub,map_sub,
      coeff_wordProjectionGerm hρ hρR w hh]
    by_cases hL : AvoidsCones L a <;> by_cases hw : wordExponent w ≤ a <;>
      simp only [hL,hw,ite_true,ite_false,avoidsCones_cons,not_true_eq_false,
        not_false_eq_true,and_false,and_true,sub_self,sub_zero]

theorem diagramQuotientAt_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (diagramQuotientAt ρ L w h) (ball 0 R) :=
  wordQuot_differentiableOn hρ hρR w (diagramResidual_differentiableOn hρ hρR L hh)

theorem diagramPieceAt_differentiableOn {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) :
    DifferentiableOn ℂ (diagramPieceAt ρ L w h) (ball 0 R) :=
  wordProjection_differentiableOn hρ hρR w (diagramResidual_differentiableOn hρ hρR L hh)

theorem exists_diagramQuotientAt_bound {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) (w : CoordinateWord n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ) (h : CoordinateSpace n → ℂ),
      DifferentiableOn ℂ h (ball 0 R) →
      (∀ z ∈ ball (0 : CoordinateSpace n) R, ‖h z‖ ≤ M) →
      ∀ z ∈ ball (0 : CoordinateSpace n) R, ‖diagramQuotientAt ρ L w h z‖ ≤ C * M := by
  obtain ⟨Cq,hCq,hq⟩ := exists_wordQuot_bound hρ hρR w
  obtain ⟨Cr,hCr,hr⟩ := exists_diagramResidual_bound hρ hρR L
  refine ⟨Cq * Cr,mul_nonneg hCq hCr,?_⟩
  intro M h hh hM z hz
  simpa only [diagramQuotientAt,mul_assoc] using hq (Cr * M) _
    (diagramResidual_differentiableOn hρ hρR L hh) (hr M h hh hM) z hz

theorem coeff_diagramQuotientAtGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (b : Fin n →₀ ℕ) :
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (diagramQuotientAt_differentiableOn hρ hρR L w hh))) =
      if AvoidsCones L (b + wordExponent w) then MvPowerSeries.coeff (b + wordExponent w)
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 := by
  change MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
    (modelGerm (hρ.trans hρR) (wordQuot_differentiableOn hρ hρR w
      (diagramResidual_differentiableOn hρ hρR L hh)))) = _
  rw [coeff_wordQuotGerm hρ hρR w (diagramResidual_differentiableOn hρ hρR L hh),
    coeff_diagramResidualGerm hρ hρR L hh]

theorem coeff_diagramPieceAtGerm {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (L : List (CoordinateWord n)) (w : CoordinateWord n) {h : CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R)) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
        (modelGerm (hρ.trans hρR) (diagramPieceAt_differentiableOn hρ hρR L w hh))) =
      if wordExponent w ≤ a ∧ AvoidsCones L a then MvPowerSeries.coeff a
        (actualUnshiftedTaylorAlgHom n (modelGerm (hρ.trans hρR) hh)) else 0 := by
  change MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n
    (modelGerm (hρ.trans hρR) (wordProjection_differentiableOn hρ hρR w
      (diagramResidual_differentiableOn hρ hρR L hh)))) = _
  rw [coeff_wordProjectionGerm hρ hρR w (diagramResidual_differentiableOn hρ hρR L hh),
    coeff_diagramResidualGerm hρ hρR L hh]
  by_cases hw : wordExponent w ≤ a <;> by_cases hL : AvoidsCones L a <;> simp [hw,hL]

theorem diagramResidual_append (ρ : ℝ) (L V : List (CoordinateWord n))
    (h : CoordinateSpace n → ℂ) :
    diagramResidual ρ (L ++ V) h = diagramResidual ρ V (diagramResidual ρ L h) := by
  induction L generalizing h with
  | nil => rfl
  | cons w L ih => exact ih (fun z => h z - wordProjection ρ w h z)

theorem diagramResidual_append_single (ρ : ℝ) (L : List (CoordinateWord n))
    (w : CoordinateWord n) (h : CoordinateSpace n → ℂ) :
    diagramResidual ρ (L ++ [w]) h = fun z => diagramResidual ρ L h z -
      wordMonomial w z * diagramQuotientAt ρ L w h z := by
  rw [diagramResidual_append]
  rfl

/-- The partition is an equality of actual functions, even before taking germs. -/
theorem diagram_function_decomposition (ρ : ℝ) (L : List (CoordinateWord n))
    (h : CoordinateSpace n → ℂ) (z : CoordinateSpace n) :
    h z = ((diagramPieces ρ L h).map fun f => f z).sum + diagramResidual ρ L h z := by
  induction L generalizing h with
  | nil => simp only [diagramPieces,List.map_nil,List.sum_nil,diagramResidual,zero_add]
  | cons w L ih =>
    have he := ih (fun x => h x - wordProjection ρ w h x)
    simp only [diagramPieces,List.map_cons,List.sum_cons,diagramResidual]
    linear_combination he

end

end Hironaka.HironakaActualCauchyDiagramPartition
