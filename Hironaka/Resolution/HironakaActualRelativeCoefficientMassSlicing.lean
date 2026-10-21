/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCoefficientPresentationCentrePower
import Hironaka.Resolution.HironakaActualPolydiscHolomorphicEvaluation

/-!
# One actual full mass radius controls EVERY relative normal coefficient

The literal joined-exponent fibre and exact block radius product extract
summability at the SAME fixed base radius for all normal exponents. The
sharp mass bound gives genuine evaluated coefficient functions on ONE
actual original Euclidean base polydisc, without per-label shrinking.
Blueprint: `hironaka-actual-relative-coefficient-mass-slicing-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology BigOperators Manifold ContDiff
namespace Hironaka.HironakaActualRelativeCoefficientMassSlicing
noncomputable section
open HironakaActualCoefficientPresentationCentrePower
  HironakaActualMonomialDivisionBounds HironakaActualPolydiscHolomorphicEvaluation
variable {d t : ℕ}

/-- The unchanged first-block part of the ONE prescribed original radius. -/
def baseRadius (ρ : Fin (d+t) → ℝ) : Fin d → ℝ := fun i => ρ (i.castAdd t)

/-- The unchanged normal-block part of the ONE prescribed original radius. -/
def normalRadius (ρ : Fin (d+t) → ℝ) : Fin t → ℝ := fun i => ρ (i.natAdd d)

/-- Each actual normal coefficient is an injective fibre of the original entire coefficient array. -/
theorem actualJoinedExponent_left_injective (γ : Fin t →₀ ℕ) :
    Function.Injective (fun β : Fin d →₀ ℕ => actualJoinedExponent β γ) := by
  intro β β' he
  ext i
  simpa [actualJoinedExponent]
    using congrArg (fun a : Fin (d+t) →₀ ℕ => a (i.castAdd t)) he

/-- Literal original radius monomials split exactly on the genuine joined exponent. -/
theorem radiusMonomial_actualJoinedExponent (ρ : Fin (d+t) → ℝ)
    (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    radiusMonomial ρ (actualJoinedExponent β γ)=
      radiusMonomial (baseRadius ρ) β*radiusMonomial (normalRadius ρ) γ := by
  unfold radiusMonomial
  rw [Fin.prod_univ_add]
  simp [baseRadius,normalRadius,actualJoinedExponent]

private theorem normal_radius_weight_pos (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (γ : Fin t →₀ ℕ) : 0<radiusMonomial (normalRadius ρ) γ :=
  Finset.prod_pos fun i _ => pow_pos (hρ (i.natAdd d)) _

/-- ONE fixed full radius gives the SAME base radius for EVERY actual relative coefficient series. -/
theorem normalCoefficient_hasFiniteCoefficientMass (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ γ : Fin t →₀ ℕ,HasFiniteCoefficientMass (baseRadius ρ) (actualFormalNormalCoefficient F γ) := by
  intro γ
  have hs := hF.comp_injective (actualJoinedExponent_left_injective γ)
  have hscaled : Summable (fun β : Fin d →₀ ℕ => radiusMonomial (normalRadius ρ) γ*
      (‖MvPowerSeries.coeff β (actualFormalNormalCoefficient F γ)‖*radiusMonomial (baseRadius ρ) β)) := by
    apply hs.congr
    intro β
    change ‖MvPowerSeries.coeff (actualJoinedExponent β γ) F‖*radiusMonomial ρ (actualJoinedExponent β γ)=
      radiusMonomial (normalRadius ρ) γ*
        (‖MvPowerSeries.coeff (actualJoinedExponent β γ) F‖*radiusMonomial (baseRadius ρ) β)
    rw [radiusMonomial_actualJoinedExponent]
    ring
  exact (summable_mul_left_iff (ne_of_gt (normal_radius_weight_pos ρ hρ γ))).mp hscaled

/-- The genuine original coefficient fibre has its sharp SAME-radius mass bound. -/
theorem normalCoefficient_mass_bound (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ γ : Fin t →₀ ℕ,radiusMonomial (normalRadius ρ) γ*
      coefficientMass (baseRadius ρ) (actualFormalNormalCoefficient F γ)≤coefficientMass ρ F := by
  intro γ
  calc
    _ = ∑' β : Fin d →₀ ℕ,radiusMonomial (normalRadius ρ) γ*
        (‖MvPowerSeries.coeff β (actualFormalNormalCoefficient F γ)‖*radiusMonomial (baseRadius ρ) β) :=
      tsum_mul_left.symm
    _ = ∑' β : Fin d →₀ ℕ,‖MvPowerSeries.coeff (actualJoinedExponent β γ) F‖*
        radiusMonomial ρ (actualJoinedExponent β γ) := by
      apply tsum_congr
      intro β
      change radiusMonomial (normalRadius ρ) γ*
        (‖MvPowerSeries.coeff (actualJoinedExponent β γ) F‖*radiusMonomial (baseRadius ρ) β)=_
      rw [radiusMonomial_actualJoinedExponent]
      ring
    _ ≤ _ := tsum_comp_le_tsum_of_inj hF
      (fun a => mul_nonneg (norm_nonneg _) (le_of_lt (Finset.prod_pos fun i _ => pow_pos (hρ i) _)))
      (actualJoinedExponent_left_injective γ)

/-- Division by the actual positive normal radius factor gives the sharp coefficient-mass estimate. -/
theorem normalCoefficient_mass_le_div (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ γ : Fin t →₀ ℕ,coefficientMass (baseRadius ρ) (actualFormalNormalCoefficient F γ)≤
      coefficientMass ρ F/radiusMonomial (normalRadius ρ) γ := by
  intro γ
  apply (le_div_iff₀ (normal_radius_weight_pos ρ hρ γ)).mpr
  simpa only [mul_comm] using normalCoefficient_mass_bound ρ hρ F hF γ

/-- ONE genuine original Euclidean base open, independent of EVERY normal label. -/
def actualBaseOpenPolydisc (ρ : Fin (d+t) → ℝ) : Set (ComplexModel d) :=
  (EuclideanSpace.equiv (Fin d) ℂ) ⁻¹' HironakaActualPolydiscHolomorphicEvaluation.openPolydisc (baseRadius ρ)

/-- The corresponding actual closed base polydisc used in the coefficient bound. -/
def actualBaseClosedPolydisc (ρ : Fin (d+t) → ℝ) : Set (ComplexModel d) :=
  (EuclideanSpace.equiv (Fin d) ℂ) ⁻¹' closedPolydisc (baseRadius ρ)

/-- The literal actual evaluated relative coefficient function in unchanged original base coordinates. -/
def actualNormalCoefficientEvaluation (F : MvPowerSeries (Fin (d+t)) ℂ)
    (γ : Fin t →₀ ℕ) : ComplexModel d → ℂ :=
  fun z => actualSeriesEvaluation (actualFormalNormalCoefficient F γ) ((EuclideanSpace.equiv (Fin d) ℂ) z)

/-- The actual evaluated function uses exactly the original coordinate tuple, without a coordinate change. -/
theorem actualNormalCoefficientEvaluation_apply (F : MvPowerSeries (Fin (d+t)) ℂ)
    (γ : Fin t →₀ ℕ) (u : ComplexModel d) :
    actualNormalCoefficientEvaluation F γ u=
      actualSeriesEvaluation (actualFormalNormalCoefficient F γ) (fun i : Fin d => u i) := rfl

/-- EVERY evaluated coefficient is holomorphic and smooth on ONE actual original open neighbourhood. -/
theorem normalCoefficient_evaluations_common_domain (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    IsOpen (actualBaseOpenPolydisc ρ) ∧ (0 : ComplexModel d)∈actualBaseOpenPolydisc ρ ∧
      ∀ γ : Fin t →₀ ℕ,
        DifferentiableOn ℂ (actualNormalCoefficientEvaluation F γ) (actualBaseOpenPolydisc ρ) ∧
        MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ)
          (actualNormalCoefficientEvaluation F γ) (actualBaseOpenPolydisc ρ) ∧
        ContDiffOn ℂ ∞ (actualNormalCoefficientEvaluation F γ) (actualBaseOpenPolydisc ρ) := by
  have hO : IsOpen (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc (baseRadius ρ)) := by
    have he : HironakaActualPolydiscHolomorphicEvaluation.openPolydisc (baseRadius ρ)=⋂ i : Fin d,{z : Fin d → ℂ | ‖z i‖<baseRadius ρ i} := by
      ext z
      simp only [HironakaActualPolydiscHolomorphicEvaluation.openPolydisc,mem_ofPred_eq,mem_iInter]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const
  refine ⟨hO.preimage (EuclideanSpace.equiv (Fin d) ℂ).continuous,?_,?_⟩
  · change ∀ i : Fin d,‖((EuclideanSpace.equiv (Fin d) ℂ) (0 : ComplexModel d)) i‖<baseRadius ρ i
    simpa only [map_zero,Pi.zero_apply,norm_zero,baseRadius] using fun i : Fin d => hρ (i.castAdd t)
  · intro γ
    have hγ := normalCoefficient_hasFiniteCoefficientMass ρ hρ F hF γ
    have hd : DifferentiableOn ℂ (actualNormalCoefficientEvaluation F γ) (actualBaseOpenPolydisc ρ) :=
      (evaluation_differentiableOn (baseRadius ρ) _ hγ).comp
        (EuclideanSpace.equiv (Fin d) ℂ).differentiable.differentiableOn (fun _ hz => hz)
    exact ⟨hd,mdifferentiableOn_iff_differentiableOn.mpr hd,
      (evaluation_contDiffOn (baseRadius ρ) _ hγ).comp
        (EuclideanSpace.equiv (Fin d) ℂ).contDiff.contDiffOn (fun _ hz => hz)⟩

/-- Each actual coefficient is a genuine original holomorphic representative at zero, from the SAME common domain. -/
theorem normalCoefficient_evaluation_holomorphicAt_zero (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ γ : Fin t →₀ ℕ,∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (actualNormalCoefficientEvaluation F γ) z := by
  obtain ⟨hU,h0,hc⟩ := normalCoefficient_evaluations_common_domain ρ hρ F hF
  intro γ
  have hn : ∀ᶠ z in 𝓝 (0 : ComplexModel d),z∈actualBaseOpenPolydisc ρ := hU.mem_nhds h0
  exact hn.mono fun z hz => ((hc γ).1).differentiableAt (hU.mem_nhds hz)

/-- EVERY actual coefficient function satisfies the sharp full-source bound on the SAME closed base polydisc. -/
theorem normalCoefficient_evaluation_bound (ρ : Fin (d+t) → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∀ (γ : Fin t →₀ ℕ) (z : ComplexModel d),z∈actualBaseClosedPolydisc ρ →
      radiusMonomial (normalRadius ρ) γ*‖actualNormalCoefficientEvaluation F γ z‖≤coefficientMass ρ F := by
  intro γ z hz
  have hb := (evaluation_uniform_and_bound (baseRadius ρ) _
    (normalCoefficient_hasFiniteCoefficientMass ρ hρ F hF γ)).2 ((EuclideanSpace.equiv (Fin d) ℂ) z) hz
  exact (mul_le_mul_of_nonneg_left hb (le_of_lt (normal_radius_weight_pos ρ hρ γ))).trans
    (normalCoefficient_mass_bound ρ hρ F hF γ)

end
end Hironaka.HironakaActualRelativeCoefficientMassSlicing
