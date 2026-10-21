import TranscendentalNakamaye.Pending.HironakaActualSignedConeDivision
import TranscendentalNakamaye.Pending.HironakaActualConvergentTaylorRealization
import TranscendentalNakamaye.Pending.HironakaActualAnalyticBlowupTaylor

/-!
# Whole actual blowup-cone range and genuine analytic inverse convergence

The literal coefficient inverse at the true exponent insertion gives the
WHOLE formal range iff. Actual inverse coefficients converge at the squared
positive radius with a mass bound. True Taylor realization and genuine
chart naturality then give the entire ORIGINAL analytic image iff; no
preimage or output-convergence certificate is assumed.
Blueprint: `hironaka-actual-blowup-cone-inverse-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace TranscendentalNakamaye.Pending.HironakaActualBlowupConeInverse
noncomputable section
open FirstPass HolGerm HironakaActualFormalCoordinatePowerDivision
 HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
 HironakaActualSignedConeDivision HironakaActualMonomialDivisionBounds
 HironakaActualConvergentTaylorRealization HironakaActualVertexSmallRadius
 HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticFormalNormalPowers
 HironakaActualRelativeTaylorCoefficients HironakaActualOriginalFormalTaylor
 HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

def actualBlowupCoefficientInverse (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun a => MvPowerSeries.coeff (actualMonomialBlowupExponent A e a) F

theorem actualBlowupCoefficientInverse_blowup (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualBlowupCoefficientInverse A e (actualFormalBlowup A e (fun _ => 0) F)=F := by
  ext a
  exact actualFormalBlowup_zero_coefficient A e F a

private theorem exists_preimage_exponent (A : Set (Fin n)) (e : Fin n)
    (β : Fin n →₀ ℕ) (hβ : 0≤actualBlowupConeWeight A e β) :
    ∃ a : Fin n →₀ ℕ,actualMonomialBlowupExponent A e a=β := by
  let s := Finsupp.weight (actualCoordinateWeight (A\{e})) β
  have he : s≤β e := by
    change 0≤(β e : ℤ)-(s : ℤ) at hβ
    omega
  have hle : Finsupp.single e s≤β := by
    intro i
    by_cases hi : i=e
    · subst i;simpa using he
    · simp [Finsupp.single_eq_of_ne hi]
  let a := β-Finsupp.single e s
  have hadd : a+Finsupp.single e s=β := tsub_add_cancel_of_le hle
  have hw : Finsupp.weight (actualCoordinateWeight (A\{e})) a=s := by
    have hh := congrArg (Finsupp.weight (actualCoordinateWeight (A\{e}))) hadd
    simpa [Finsupp.weight_single,actualCoordinateWeight,s] using hh
  refine ⟨a,?_⟩
  change a+Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)=β
  rwa [hw]

theorem actualFormalBlowup_coefficientInverse (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : ∀ β,actualBlowupConeWeight A e β<0→MvPowerSeries.coeff β F=0) :
    actualFormalBlowup A e (fun _ => 0) (actualBlowupCoefficientInverse A e F)=F := by
  ext β
  by_cases hβ : actualBlowupConeWeight A e β<0
  · rw [actualFormalBlowup_zero_coefficient_outside_cone A e _ β hβ,hF β hβ]
  · obtain ⟨a,rfl⟩ := exists_preimage_exponent A e β (le_of_not_gt hβ)
    exact actualFormalBlowup_zero_coefficient A e (actualBlowupCoefficientInverse A e F) a

theorem mem_range_actualFormalBlowup_zero_iff (A : Set (Fin n)) (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) :
    F∈Set.range (actualFormalBlowup A e (fun _ => 0))↔
      ∀ β,actualBlowupConeWeight A e β<0→MvPowerSeries.coeff β F=0 := by
  constructor
  · rintro ⟨G,rfl⟩
    exact actualFormalBlowup_zero_coefficient_outside_cone A e G
  · intro hF
    exact ⟨actualBlowupCoefficientInverse A e F,actualFormalBlowup_coefficientInverse A e F hF⟩

private theorem selected_weight_le_degree (A : Set (Fin n)) (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) a≤a.degree := by
  rw [Finsupp.weight_eq_sum,Finsupp.degree_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [smul_eq_mul]
  by_cases hi : i∈A <;> simp [actualCoordinateWeight,hi]

private theorem actualMonomialBlowupExponent_degree_le (A : Set (Fin n)) (e : Fin n)
    (a : Fin n →₀ ℕ) : (actualMonomialBlowupExponent A e a).degree≤2*a.degree := by
  change (a+Finsupp.single e (Finsupp.weight (actualCoordinateWeight (A\{e})) a)).degree≤_
  rw [map_add,Finsupp.degree_single]
  have hh := selected_weight_le_degree (A\{e}) a
  omega

private theorem radiusMonomial_uniform (r : ℝ) (a : Fin n →₀ ℕ) :
    radiusMonomial (fun _ => r) a=r^a.degree := by
  simp only [radiusMonomial,Finset.prod_pow_eq_pow_sum,Finsupp.degree_eq_sum]

private theorem inverse_mass_term_le (A : Set (Fin n)) (e : Fin n)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1) (F : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff a (actualBlowupCoefficientInverse A e F)‖*radiusMonomial (fun _ => r^2) a≤
      ‖MvPowerSeries.coeff (actualMonomialBlowupExponent A e a) F‖*
        radiusMonomial (fun _ => r) (actualMonomialBlowupExponent A e a) := by
  simp only [actualBlowupCoefficientInverse,MvPowerSeries.coeff_apply,radiusMonomial_uniform,←pow_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (le_of_lt hr) hr1 (actualMonomialBlowupExponent_degree_le A e a))
    (norm_nonneg _)

theorem actualBlowupCoefficientInverse_summable (A : Set (Fin n)) (e : Fin n)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass (fun _ => r) F) :
    HasFiniteCoefficientMass (fun _ => r^2) (actualBlowupCoefficientInverse A e F) := by
  have hs := hF.comp_injective (actualMonomialBlowupExponent_injective A e)
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (sq_nonneg r) _))
    (inverse_mass_term_le A e r hr hr1 F) hs

theorem actualBlowupCoefficientInverse_mass_le (A : Set (Fin n)) (e : Fin n)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1) (F : MvPowerSeries (Fin n) ℂ)
    (hF : HasFiniteCoefficientMass (fun _ => r) F) :
    coefficientMass (fun _ => r^2) (actualBlowupCoefficientInverse A e F)≤
      coefficientMass (fun _ => r) F := by
  have hs := hF.comp_injective (actualMonomialBlowupExponent_injective A e)
  have hI := actualBlowupCoefficientInverse_summable A e r hr hr1 F hF
  calc
    _≤∑' a : Fin n →₀ ℕ, ‖MvPowerSeries.coeff (actualMonomialBlowupExponent A e a) F‖*
        radiusMonomial (fun _ => r) (actualMonomialBlowupExponent A e a) :=
      Summable.tsum_le_tsum (inverse_mass_term_le A e r hr hr1 F) hI hs
    _≤_ := tsum_comp_le_tsum_of_inj hF
      (fun a => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (le_of_lt hr) _))
      (actualMonomialBlowupExponent_injective A e)


private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem exists_unshifted_realization (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∃ g : HolGerm (ComplexModel n),actualUnshiftedTaylorAlgHom n g=F := by
  apply unshiftedTaylor_property n (fun m τ => ∃ g : HolGerm (ComplexModel m),τ g=F)
  exact ⟨evaluationGerm ρ hρ F hF,originalTaylor_evaluationGerm ρ hρ F hF⟩

/-- Whole convergent cone series internally produce genuine original analytic preimages. -/
theorem exists_analytic_preimage_of_convergent_cone (A : Set (Fin n)) (e : Fin n)
    (r : ℝ) (hr : 0<r) (F : MvPowerSeries (Fin n) ℂ)
    (hMass : HasFiniteCoefficientMass (fun _ => r) F)
    (hCone : ∀ β,actualBlowupConeWeight A e β<0→MvPowerSeries.coeff β F=0) :
    ∃ g : HolGerm (ComplexModel n),
      actualUnshiftedTaylorAlgHom n g=actualBlowupCoefficientInverse A e F ∧
      actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e (fun _ => 0) g)=F := by
  let s := min r 1
  have hs : 0<s := lt_min hr zero_lt_one
  have hMs : HasFiniteCoefficientMass (fun _ => s) F :=
    finiteCoefficientMass_mono (fun _ => s) (fun _ => r) (fun _ => hs) (fun _ => min_le_left _ _) F hMass
  have hI := actualBlowupCoefficientInverse_summable A e s hs (min_le_right _ _) F hMs
  obtain ⟨g,hg⟩ := exists_unshifted_realization (fun _ => s^2) (fun _ => pow_pos hs 2) _ hI
  refine ⟨g,hg,?_⟩
  have hn := AlgHom.congr_fun (actualTaylor_analyticBlowupPullback A e (fun _ => 0)) g
  change actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e (fun _ => 0) g)=
    actualFormalBlowup A e (fun _ => 0) (actualUnshiftedTaylorAlgHom n g) at hn
  rw [hn,hg]
  exact actualFormalBlowup_coefficientInverse A e F hCone

/-- Actual original analytic image membership is exactly the true full signed Taylor cone. -/
theorem mem_range_actualAnalyticBlowupPullback_zero_iff (A : Set (Fin n)) (e : Fin n)
    (h : HolGerm (ComplexModel n)) :
    h∈Set.range (actualAnalyticBlowupPullback A e (fun _ => 0))↔
      ∀ β,actualBlowupConeWeight A e β<0→
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n h)=0 := by
  constructor
  · rintro ⟨g,rfl⟩
    have hn := AlgHom.congr_fun (actualTaylor_analyticBlowupPullback A e (fun _ => 0)) g
    change actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e (fun _ => 0) g)=
      actualFormalBlowup A e (fun _ => 0) (actualUnshiftedTaylorAlgHom n g) at hn
    rw [hn]
    exact actualFormalBlowup_zero_coefficient_outside_cone A e _
  · intro hCone
    have hAll : ∀ g : HolGerm (ComplexModel n),∃ r : ℝ,0<r ∧
        HasFiniteCoefficientMass (fun _ : Fin n => r) (actualUnshiftedTaylorAlgHom n g) := by
      apply unshiftedTaylor_property n (fun m τ => ∀ g : HolGerm (ComplexModel m),∃ r : ℝ,0<r ∧
        HasFiniteCoefficientMass (fun _ : Fin n => r) (τ g))
      exact HironakaActualMultilinearTaylorCoordinates.exists_originalTaylor_finiteMass n
    obtain ⟨r,hr,hMass⟩ := hAll h
    obtain ⟨g,_hg,hpull⟩ := exists_analytic_preimage_of_convergent_cone A e r hr _ hMass hCone
    exact ⟨g,actualUnshiftedTaylorAlgHom_injective n hpull⟩

end
end TranscendentalNakamaye.Pending.HironakaActualBlowupConeInverse
