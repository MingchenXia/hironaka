import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
import Hironaka.Resolution.HironakaG10LocFrischLocus
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10KernelSectionResidue
open Hironaka HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
noncomputable section

variable {Q E₁ E₀ ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
  [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℂ Q] [CompleteSpace E₁] [CompleteSpace E₀] in
theorem coefficientResidue_coefficientCLM (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (T : E₁ →L[ℂ] E₀) (v : ι → E₁) :
    coefficientResidue b ε (coefficientCLM T v) = T (coefficientResidue b ε v) := by
  simp only [coefficientResidue_apply, coefficientCLM_apply, map_sum, map_smul]

omit [FiniteDimensional ℂ Q] [CompleteSpace E₁] [CompleteSpace E₀] in
/-- Literal residue of the fixed kernel section is the kernel section of
its literal residue operator, including the inverse comparison. -/
theorem coefficientResidue_kerSec (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (P : E₁ →L[ℂ] E₁) (T : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (F : (ι → E₁) →L[ℂ] (ι → E₀)) (f : E₁ →L[ℂ] E₀)
    (hred : ∀ v, coefficientResidue b ε (F v) = f (coefficientResidue b ε v))
    (hC : (opC P T S₀ f).IsInvertible)
    (hCQ : (opC (coefficientCLM P) (coefficientCLM T) (coefficientCLM S₀) F).IsInvertible)
    (v : ι → E₁) :
    coefficientResidue b ε
      (kerSec (coefficientCLM P) (coefficientCLM T) (coefficientCLM S₀) F v) =
      kerSec P T S₀ f (coefficientResidue b ε v) := by
  let C := opC P T S₀ f
  let CQ := opC (coefficientCLM P) (coefficientCLM T) (coefficientCLM S₀) F
  have hC' : C.IsInvertible := hC
  have hCQ' : CQ.IsInvertible := hCQ
  have hcmp (w : ι → E₀) : coefficientResidue b ε (CQ w) = C (coefficientResidue b ε w) := by
    simp only [CQ, C, opC, _root_.add_apply, _root_.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_add, map_sub,
      coefficientResidue_coefficientCLM, hred]
  have hinv (w : ι → E₀) : coefficientResidue b ε (CQ.inverse w) = C.inverse (coefficientResidue b ε w) := by
    have hw := hcmp (CQ.inverse w)
    rw [hCQ'.self_apply_inverse] at hw
    have hh := congrArg C.inverse hw
    simpa only [hC'.inverse_apply_self] using hh.symm
  have hinv' (w : ι → E₀) : coefficientResidue b ε
      ((opC (coefficientCLM P) (coefficientCLM T) (coefficientCLM S₀) F).inverse w) =
      (opC P T S₀ f).inverse (coefficientResidue b ε w) := hinv w
  simp only [kerSec, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_sub, hinv', hred, coefficientResidue_coefficientCLM]
end
end Hironaka.Analytic.Unibranch.HironakaG10KernelSectionResidue
