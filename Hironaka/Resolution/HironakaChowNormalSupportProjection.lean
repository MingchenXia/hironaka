import Hironaka.Resolution.HironakaActualFormalNormalSeries
import Hironaka.Resolution.HironakaActualOriginalVertexConvergence
import Hironaka.Resolution.HironakaActualConvergentTaylorRealization
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers

/-! Actual A-linear analytic projection onto arbitrary ORIGINAL normal support.
Whole Taylor mass constructs genuine analytic germs. Their SAME native range
is a flat retract for the actual tangent-pullback action, not a formal proxy.
Blueprint first: hironaka-g10-normal-support-projection.tex. -/
set_option autoImplicit false

namespace Hironaka.HironakaChowNormalSupportProjection
noncomputable section
open Set Classical HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalTaylor
  HironakaActualOriginalVertexConvergence HironakaActualConvergentTaylorRealization
  HironakaActualMonomialDivisionBounds HironakaActualRelativeTaylorCoefficients
  HironakaActualRelativeCoefficientGerms HironakaActualFormalNormalSeries
  HironakaActualAnalyticFormalNormalPowers

private def formalSupport (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (F : MvPowerSeries (Fin (d+t)) ℂ) : MvPowerSeries (Fin (d+t)) ℂ :=
  fun α => if actualNormalExponent α ∈ Δ then MvPowerSeries.coeff α F else 0

private theorem unshifted_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem formalSupport_mass (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (ρ : Fin (d+t) → ℝ) (hρ : ∀ i, 0 < ρ i)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    HasFiniteCoefficientMass ρ (formalSupport d t Δ F) := by
  have hRadius (α : Fin (d+t) →₀ ℕ) : 0 ≤ radiusMonomial ρ α :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (hρ i).le _)
  apply Summable.of_nonneg_of_le
    (fun α => mul_nonneg (norm_nonneg _) (hRadius α)) _ hF
  intro α
  change ‖if actualNormalExponent α ∈ Δ then MvPowerSeries.coeff α F else 0‖ *
    radiusMonomial ρ α ≤ ‖MvPowerSeries.coeff α F‖ * radiusMonomial ρ α
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (hRadius α)

private theorem exists_support_germ (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) :
    ∃ g : HolGerm (ComplexModel (d+t)), actualUnshiftedTaylorAlgHom (d+t) g =
      formalSupport d t Δ (actualUnshiftedTaylorAlgHom (d+t) f) := by
  have hMass : ∃ r : ℝ, 0 < r ∧ HasFiniteCoefficientMass (fun _ : Fin (d+t) => r)
      (actualUnshiftedTaylorAlgHom (d+t) f) := by
    apply unshifted_property (d+t) (fun m τ => ∀ f : HolGerm (ComplexModel m),
      ∃ r : ℝ, 0 < r ∧ HasFiniteCoefficientMass (fun _ : Fin (d+t) => r) (τ f)) _ f
    intro g
    obtain ⟨r, hr, hM⟩ := exists_finite_originalTaylor_common_mass (fun _ : Unit => g)
    exact ⟨r, hr, hM ()⟩
  obtain ⟨r, hr, hM⟩ := hMass
  let F := formalSupport d t Δ (actualUnshiftedTaylorAlgHom (d+t) f)
  have hF := formalSupport_mass d t Δ (fun _ => r) (fun _ => hr) _ hM
  apply unshifted_property (d+t) (fun m τ => ∃ g : HolGerm (ComplexModel m), τ g = F)
  exact ⟨evaluationGerm (fun _ => r) (fun _ => hr) F hF,
    originalTaylor_evaluationGerm (fun _ => r) (fun _ => hr) F hF⟩

private def projectionFunction (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) : HolGerm (ComplexModel (d+t)) :=
  Classical.choose (exists_support_germ d t Δ f)

private theorem projection_taylor (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) :
    actualUnshiftedTaylorAlgHom (d+t) (projectionFunction d t Δ f) =
      formalSupport d t Δ (actualUnshiftedTaylorAlgHom (d+t) f) :=
  Classical.choose_spec (exists_support_germ d t Δ f)

private theorem formalSupport_coefficient (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (F : MvPowerSeries (Fin (d+t)) ℂ) (γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff γ (formalNormalSeriesEquiv d t (formalSupport d t Δ F)) =
      if γ ∈ Δ then MvPowerSeries.coeff γ (formalNormalSeriesEquiv d t F) else 0 := by
  ext β
  change (if actualNormalExponent (actualJoinedExponent β γ) ∈ Δ then
    MvPowerSeries.coeff (actualJoinedExponent β γ) F else 0) = _
  rw [normal_joined]
  by_cases hγ : γ ∈ Δ
  · rw [if_pos hγ, if_pos hγ]
    exact (formalNormalSeriesEquiv_coefficient d t F γ β).symm
  · simp [hγ]

private theorem formalNormal_tangent (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    formalNormalSeriesEquiv d t (actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t a)) =
      MvPowerSeries.C (actualUnshiftedTaylorAlgHom d a) := by
  let : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    tangentAlgebra d t
  have h := formalNormalSeries_normalPolynomialEval d t (MvPolynomial.C a)
  have hC : normalPolynomialEval d t (MvPolynomial.C a) = tangentPullback d t a := by
    change MvPolynomial.aeval (normalCoordinate d t) (MvPolynomial.C a) = _
    rw [MvPolynomial.aeval_C]
    rfl
  rw [hC] at h
  have h' : formalNormalSeriesEquiv d t
      (actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t a)) =
      MvPowerSeries.C ((actualUnshiftedTaylorAlgHom d).toRingHom a) := by
    simpa only [MvPolynomial.map_C, MvPolynomial.coe_C] using h
  exact h'.trans (congrArg MvPowerSeries.C (show
    (actualUnshiftedTaylorAlgHom d).toRingHom a = actualUnshiftedTaylorAlgHom d a from rfl))

private theorem formalSupport_tangent_mul (d t : ℕ) (Δ : Set (Fin t →₀ ℕ))
    (a : HolGerm (ComplexModel d)) (F : MvPowerSeries (Fin (d+t)) ℂ) :
    formalSupport d t Δ (actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t a) * F) =
      actualUnshiftedTaylorAlgHom (d+t) (tangentPullback d t a) * formalSupport d t Δ F := by
  apply (formalNormalSeriesEquiv d t).injective
  apply MvPowerSeries.ext
  intro γ
  rw [formalSupport_coefficient, map_mul, formalNormal_tangent, MvPowerSeries.coeff_C_mul,
    map_mul, formalNormal_tangent, MvPowerSeries.coeff_C_mul, formalSupport_coefficient]
  by_cases hγ : γ ∈ Δ <;> simp [hγ]

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- The actual analytic projection, linear for the original full tangent-germ action. -/
def normalSupportProjection (Δ : Set (Fin t →₀ ℕ)) :
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)) where
  toFun := projectionFunction d t Δ
  map_add' f g := by
    apply actualUnshiftedTaylorAlgHom_injective (d+t)
    simp only [projection_taylor, map_add]
    ext α
    change (if actualNormalExponent α ∈ Δ then
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) f) +
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) g) else 0) =
      (if actualNormalExponent α ∈ Δ then
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) f) else 0) +
      (if actualNormalExponent α ∈ Δ then
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) g) else 0)
    by_cases hα : actualNormalExponent α ∈ Δ <;> simp [hα]
  map_smul' a f := by
    change projectionFunction d t Δ (tangentPullback d t a * f) =
      tangentPullback d t a * projectionFunction d t Δ f
    apply actualUnshiftedTaylorAlgHom_injective (d+t)
    rw [projection_taylor, map_mul, map_mul, projection_taylor]
    exact formalSupport_tangent_mul d t Δ a _

/-- Every original Taylor coefficient is retained or deleted by its NORMAL exponent only. -/
theorem taylor_normalSupportProjection (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) (α : Fin (d+t) →₀ ℕ) :
    MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) (normalSupportProjection d t Δ f)) =
      if actualNormalExponent α ∈ Δ then MvPowerSeries.coeff α
        (actualUnshiftedTaylorAlgHom (d+t) f) else 0 := by
  rw [show normalSupportProjection d t Δ f = projectionFunction d t Δ f from rfl,
    projection_taylor]
  rfl

/-- The output coefficients are the SAME original analytic normal coefficient germs. -/
theorem normalCoefficient_normalSupportProjection (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t (normalSupportProjection d t Δ f) γ =
      if γ ∈ Δ then actualNormalAnalyticCoefficientGerm d t f γ else 0 := by
  apply actualUnshiftedTaylorAlgHom_injective d
  rw [← actualFormalNormalCoefficient_actualTaylor]
  ext β
  change MvPowerSeries.coeff (actualJoinedExponent β γ)
    (actualUnshiftedTaylorAlgHom (d+t) (normalSupportProjection d t Δ f)) = _
  rw [taylor_normalSupportProjection, normal_joined]
  by_cases hγ : γ ∈ Δ
  · rw [if_pos hγ, if_pos hγ]
    exact congrArg (MvPowerSeries.coeff β) (actualFormalNormalCoefficient_actualTaylor d t f γ)
  · simp [hγ]

/-- Selecting the SAME original normal support twice changes no analytic germ. -/
theorem normalSupportProjection_idempotent (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) :
    normalSupportProjection d t Δ (normalSupportProjection d t Δ f) = normalSupportProjection d t Δ f := by
  apply actualUnshiftedTaylorAlgHom_injective (d+t)
  ext α
  simp only [taylor_normalSupportProjection]
  split_ifs <;> rfl

/-- The genuine native range over the actual original tangent ring. -/
def normalSupportSubmodule (Δ : Set (Fin t →₀ ℕ)) :
    Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  LinearMap.range (normalSupportProjection d t Δ)

/-- This native range is EXACTLY the original analytic germs with the prescribed normal support. -/
theorem mem_normalSupportSubmodule_iff (Δ : Set (Fin t →₀ ℕ))
    (f : HolGerm (ComplexModel (d+t))) :
    f ∈ normalSupportSubmodule d t Δ ↔
      ∀ γ : Fin t →₀ ℕ, γ ∉ Δ → actualNormalAnalyticCoefficientGerm d t f γ = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ γ hγ
    rw [normalCoefficient_normalSupportProjection, if_neg hγ]
  · intro hf
    refine ⟨f, ?_⟩
    apply actualUnshiftedTaylorAlgHom_injective (d+t)
    ext α
    rw [taylor_normalSupportProjection]
    by_cases hα : actualNormalExponent α ∈ Δ
    · rw [if_pos hα]
    · rw [if_neg hα]
      have hz := congrArg (fun g => MvPowerSeries.coeff (actualTangentExponent α)
        (actualUnshiftedTaylorAlgHom d g)) (hf (actualNormalExponent α) hα)
      rw [map_zero] at hz
      have hc := congrArg (MvPowerSeries.coeff (actualTangentExponent α))
        (actualFormalNormalCoefficient_actualTaylor d t f (actualNormalExponent α))
      change MvPowerSeries.coeff (actualJoinedExponent (actualTangentExponent α)
        (actualNormalExponent α)) (actualUnshiftedTaylorAlgHom (d+t) f) = _ at hc
      rw [actualJoinedExponent_split, hz] at hc
      exact hc.symm

/-- Native range restriction of the SAME internally produced analytic projection. -/
def normalSupportRetraction (Δ : Set (Fin t →₀ ℕ)) :
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] normalSupportSubmodule d t Δ :=
  (normalSupportProjection d t Δ).rangeRestrict

/-- The literal native inclusion and range-restricted SAME projection form a retract. -/
theorem normalSupportRetraction_comp_subtype (Δ : Set (Fin t →₀ ℕ)) :
    (normalSupportRetraction d t Δ).comp (normalSupportSubmodule d t Δ).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rcases f with ⟨f, g, rfl⟩
  exact normalSupportProjection_idempotent d t Δ g

/-- The SAME actual analytic support module is flat, without finiteness over the tangent ring. -/
theorem flat_normalSupportSubmodule (Δ : Set (Fin t →₀ ℕ)) :
    Module.Flat (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Δ) := by
  let A := HolGerm (ComplexModel d)
  let S := HolGerm (ComplexModel (d+t))
  let P := MvPolynomial (Fin t) A
  let : Algebra P S := (normalPolynomialEval d t).toRingHom.toAlgebra
  let : IsScalarTower A P S := IsScalarTower.of_algebraMap_eq
    (fun a => ((normalPolynomialEval d t).commutes a).symm)
  have : Module.Flat P S := normalPolynomialEval_flat d t
  have : Module.Flat A S := Module.Flat.trans A P S
  exact Module.Flat.of_retract (normalSupportSubmodule d t Δ).subtype
    (normalSupportRetraction d t Δ) (normalSupportRetraction_comp_subtype d t Δ)

end
end Hironaka.HironakaChowNormalSupportProjection
