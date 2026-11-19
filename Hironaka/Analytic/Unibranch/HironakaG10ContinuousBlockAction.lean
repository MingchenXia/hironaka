import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ContinuousBlockAction
noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
  {a k ι : Type*} [Fintype a] [Fintype k] [Fintype ι]
  [DecidableEq a] [DecidableEq k] [DecidableEq ι]

/-- The same finite coefficient-block formula as the actual Banach matrix action. -/
def blockAction (B : (a × ι) → (k × ι) → R) : (ι → k → R) →L[ℂ] (ι → a → R) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.pi fun i =>
    ∑ j, ∑ m, (ContinuousLinearMap.mul ℂ R (B (i,l) (j,m))).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : k => R) j).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => k → R) m))

omit [Fintype a] [DecidableEq a] [DecidableEq k] [DecidableEq ι] in
/-- The finite block action is continuous in the complete finite entry matrix. -/
theorem continuous_blockAction :
    Continuous (blockAction (R := R) (a := a) (k := k) (ι := ι)) := by
  let D := ι → k → R
  have hterm (i : a) (l : ι) (j : k) (m : ι) :
      Continuous (fun B : (a × ι) → (k × ι) → R =>
        (ContinuousLinearMap.mul ℂ R (B (i,l) (j,m))).comp
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : k => R) j).comp
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => k → R) m))) := by
    exact ((ContinuousLinearMap.mul ℂ R).continuous.comp
      ((continuous_apply (j,m)).comp (continuous_apply (i,l)))).clm_comp continuous_const
  have hsum (l : ι) (i : a) : Continuous (fun B : (a × ι) → (k × ι) → R =>
      ∑ j, ∑ m, (ContinuousLinearMap.mul ℂ R (B (i,l) (j,m))).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : k => R) j).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => k → R) m))) := by
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun m _ => hterm i l j m
  have hinner (l : ι) : Continuous (fun B : (a × ι) → (k × ι) → R =>
      ContinuousLinearMap.pi fun i : a => ∑ j, ∑ m,
        (ContinuousLinearMap.mul ℂ R (B (i,l) (j,m))).comp
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : k => R) j).comp
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => k → R) m))) := by
    exact (ContinuousLinearMap.piEquivL ℂ D (fun _ : a => R)).continuous.comp
      (continuous_pi fun i => hsum l i)
  exact (ContinuousLinearMap.piEquivL ℂ D (fun _ : ι => a → R)).continuous.comp
    (continuous_pi hinner)
end
end Hironaka.Analytic.Unibranch.HironakaG10ContinuousBlockAction
