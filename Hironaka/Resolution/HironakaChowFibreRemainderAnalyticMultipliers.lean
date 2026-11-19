import Hironaka.Resolution.HironakaChowFibreRemainderCoefficientOrders
import Hironaka.Resolution.HironakaChowBaseIdealNormalCoefficients
import Hironaka.Resolution.HironakaChowNormalSupportBaseChange

/-! ALL genuine analytic multipliers for the SAME actual native remainder,
from ALL normal monomial multipliers. Actual finite normalTaylor and ALL
base point truncations/Krull are internal; no continuity packet is input.
Blueprint FIRST: hironaka-g10-fibre-remainder-analytic-multipliers.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowFibreRemainderAnalyticMultipliers
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualSplitAnalyticCoefficients HironakaActualAnalyticFormalNormalPowers
  HironakaActualCoefficientPresentationCentrePower HironakaActualFiniteDegLexWeights
  HironakaChowFibreLiftUniformTails HironakaChowFibreSupportModules
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreDivisionRemainder
  HironakaChowNormalSupportProjection HironakaChowNormalSupportBaseChange
  HironakaChowBaseIdealNormalCoefficients HironakaChowFibreRemainderCoefficientOrders
  HolomorphicGermPointTruncationClosure

variable (d t : ℕ)
local notation "A" => HolGerm (ComplexModel d)
local notation "S" => HolGerm (ComplexModel (d+t))
local instance : Algebra A S := tangentAlgebra d t

/- This private actual coefficient-linear factory is reused literally
from BaseIdealNormalCoefficients98, with zero separate proof credit. -/
private def coefficientLinearMap (gamma : Fin t →₀ ℕ) :
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel d) where
  toFun := fun f => actualNormalAnalyticCoefficientGerm d t f gamma
  map_add' f g := by
    apply actualUnshiftedTaylorAlgHom_injective d
    rw [map_add, ← actualFormalNormalCoefficient_actualTaylor,
      ← actualFormalNormalCoefficient_actualTaylor, ← actualFormalNormalCoefficient_actualTaylor]
    apply MvPowerSeries.ext
    intro beta
    change MvPowerSeries.coeff (actualJoinedExponent beta gamma)
      (actualUnshiftedTaylorAlgHom (d+t) (f+g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a f := by
    change actualNormalAnalyticCoefficientGerm d t (tangentPullback d t a * f) gamma =
      a * actualNormalAnalyticCoefficientGerm d t f gamma
    exact actualNormalAnalyticCoefficientGerm_tangent_mul d t a f gamma

/-- Ordinary ALL normal-monomial memberships imply ALL actual analytic
multiplier memberships for the SAME original produced native remainder. -/
theorem analytic_multiplier_mem_base_ideal (I : Ideal S)
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[A] S)
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (a : Ideal A) (x : S)
    (hMonomial : ∀ γ : Fin t →₀ ℕ, divisionRemainder d t I e
      (normalExponentMonomial d t γ * x) ∈
        a • (⊤ : Submodule A (fibreRemainderModule d t I))) (h : S) :
    divisionRemainder d t I e (h*x) ∈
      a • (⊤ : Submodule A (fibreRemainderModule d t I)) := by
  let N := fibreRemainderModule d t I
  let R := divisionRemainder d t I e
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  have hPolynomial (Q : MvPolynomial (Fin t) A) :
      R (normalPolynomialEval d t Q * x) ∈ a • (⊤ : Submodule A N) := by
    rw [Q.as_sum, map_sum, Finset.sum_mul, map_sum]
    apply Submodule.sum_mem
    intro γ _
    rw [normalPolynomialEval_monomial]
    have hScalar : (tangentPullback d t (MvPolynomial.coeff γ Q) *
        normalExponentMonomial d t γ) * x =
        (MvPolynomial.coeff γ Q) • (normalExponentMonomial d t γ * x) := by
      change _ = tangentPullback d t (MvPolynomial.coeff γ Q) * _
      ring
    rw [hScalar, map_smul]
    exact (a • (⊤ : Submodule A N)).smul_mem _ (hMonomial γ)
  change R (h*x) ∈ a • (⊤ : Submodule A (normalSupportSubmodule d t Δ))
  rw [← normal_support_comap_base_ideal d t Δ a]
  change (R (h*x) : S) ∈ a • (⊤ : Submodule A S)
  rw [Ideal.smul_top_eq_map]
  apply (mem_extended_base_ideal_iff_all_normal_coefficients d t a _).mpr
  intro γ
  let C : S →ₗ[A] A := (coefficientLinearMap d t γ).comp
    ((fibreRemainderModule d t I).subtype.comp R)
  apply (mem_iff_mem_all_point_truncations d a _).mpr
  intro r
  let q := P.baseWeight * r + weightedDegree (degLexWeight t P.fibre.degreeBound) γ
  let Q := actualNormalTaylorPolynomial d t q h
  let H := normalPolynomialEval d t Q
  let E := (h-H)*x
  have hError : E ∈ normalIdeal d t ^ q :=
    Ideal.mul_mem_right x (normalIdeal d t ^ q) (actualNormalTaylorPolynomial_remainder d t q h)
  have hErrorCoeff : C E ∈ IsLocalRing.maximalIdeal A ^ r :=
    coefficient_remainder_mem_base_maximal_pow d t I P e he E q r γ hError (by rfl)
  have hPolyN := hPolynomial Q
  have hPolyAmbient : (R (H*x) : S) ∈ Ideal.map (tangentPullback d t).toRingHom a := by
    have hm := (normal_support_comap_base_ideal d t Δ a).ge hPolyN
    change (R (H*x) : S) ∈ a • (⊤ : Submodule A S) at hm
    rwa [Ideal.smul_top_eq_map] at hm
  have hPolyCoeff : C (H*x) ∈ a :=
    (mem_extended_base_ideal_iff_all_normal_coefficients d t a _).mp hPolyAmbient γ
  have hSplit : h*x = H*x + E := by
    dsimp only [E]
    ring
  change C (h*x) ∈ a ⊔ IsLocalRing.maximalIdeal A ^ r
  rw [hSplit, map_add]
  exact Ideal.add_mem _ (Submodule.mem_sup_left hPolyCoeff) (Submodule.mem_sup_right hErrorCoeff)

end
end Hironaka.HironakaChowFibreRemainderAnalyticMultipliers
