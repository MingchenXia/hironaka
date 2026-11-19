import Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
import Hironaka.Resolution.HironakaG10FlatPolydiscAlgebra

/-! # Holomorphic interior reconstruction from actual Banach coefficients -/
set_option autoImplicit false
open Set
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicExtension
open Hironaka.HironakaG10FlatPolydiscAlgebra

/-- Reconstruct an actual finite-dimensional parameter value on the ambient
space by extending each original B(K) coefficient by zero. -/
noncomputable def coefficientExtension
    {Q X ι : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [Fintype ι] (b : ι → Q) (v : ι → holSubalgebra K) (x : X) : Q :=
  ∑ i, extendZero K ((v i : holSubalgebra K) : C(K,ℂ)) x • b i

/-- The reconstructed family is genuinely holomorphic throughout the
interior of the larger compact set. -/
theorem differentiableOn_coefficientExtension
    {Q X ι : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [Fintype ι] (b : ι → Q) (v : ι → holSubalgebra K) :
    DifferentiableOn ℂ (coefficientExtension b v) (interior K) := by
  classical
  apply DifferentiableOn.fun_sum
  intro i hi
  exact (v i).property.smul_const (b i)

/-- On the larger compact set, reconstruction is the actual weighted
pointwise sum of the original B(K) coefficient functions. -/
theorem coefficientExtension_apply
    {Q X ι : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [Fintype ι] (b : ι → Q) (v : ι → holSubalgebra K) (x : K) :
    coefficientExtension b v x = ∑ i, (((v i : holSubalgebra K) : C(K,ℂ)) x) • b i := by
  classical
  simp only [coefficientExtension, extendZero_of_mem K _ x.property]

end Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicExtension
