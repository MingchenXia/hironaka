import Hironaka.Resolution.HironakaG10LocFrischLocus
import Hironaka.Resolution.HironakaG10FlatComplexPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10SchurOperatorLimit
open Hironaka HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
noncomputable section

/-- The literal Schur operator is norm-continuous at any invertible comparison. -/
theorem continuousAt_schurOp_of_invertible
    {E₁ E₀ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f₀ : E₁ →L[ℂ] E₀) (hC : (opC P Q S₀ f₀).IsInvertible) :
    ContinuousAt (fun f : E₁ →L[ℂ] E₀ => schurOp P Q S₀ f) f₀ := by
  have hc : ContinuousAt (fun f : E₁ →L[ℂ] E₀ => opC P Q S₀ f) f₀ := by
    unfold opC
    exact (continuousAt_id.clm_comp continuousAt_const).add continuousAt_const
  have hi : ContinuousAt (fun f : E₁ →L[ℂ] E₀ => (opC P Q S₀ f).inverse) f₀ :=
    (hC.contDiffAt_map_inverse (n := 0)).continuousAt.comp hc
  change ContinuousAt (fun f : E₁ →L[ℂ] E₀ =>
    (ContinuousLinearMap.id ℂ E₀ - Q).comp ((opC P Q S₀ f).inverse.comp f)) f₀
  exact continuousAt_const.clm_comp (hi.clm_comp continuousAt_id)

/-- If actual operators converge in norm and their actual Schur operators
are eventually zero, the limiting actual Schur operator is zero. -/
theorem schurOp_eq_zero_of_tendsto
    {E₁ E₀ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    {α : Type*} (l : Filter α) [NeBot l]
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f₀ : E₁ →L[ℂ] E₀) (hC : (opC P Q S₀ f₀).IsInvertible)
    (f : α → E₁ →L[ℂ] E₀) (hf : Tendsto f l (𝓝 f₀))
    (hzero : ∀ᶠ z in l, schurOp P Q S₀ (f z) = 0) :
    schurOp P Q S₀ f₀ = 0 := by
  have hlim : Tendsto (fun z => schurOp P Q S₀ (f z)) l (𝓝 (schurOp P Q S₀ f₀)) :=
    (continuousAt_schurOp_of_invertible P Q S₀ f₀ hC).tendsto.comp hf
  have hzero' : Tendsto (fun z => schurOp P Q S₀ (f z)) l (𝓝 0) :=
    (tendsto_congr' hzero).2 tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero'
end
end Hironaka.Analytic.Unibranch.HironakaG10SchurOperatorLimit
