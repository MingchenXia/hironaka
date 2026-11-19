import Hironaka.Resolution.HironakaG4NormalDerivative

/-! A unit times a free coordinate has a nonzero free partial. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG4UnitTraceDerivative
noncomputable section
open Hironaka.BlowupSequences NormalCrossings

variable {n : ℕ}

/-- A holomorphic trace equal on a carrier plane to a unit times a free
coordinate has a nonzero partial in that free coordinate. -/
theorem free_partial_ne_zero_of_unit_trace
    {f a d : ComplexModel n → ℂ} (S : Finset (Fin n)) (t : Fin n) (ht : t ∉ S)
    (hf : DifferentiableAt ℂ f 0) (ha : DifferentiableAt ℂ a 0) (hd : DifferentiableAt ℂ d 0)
    (ha0 : a 0 ≠ 0) (hd0 : d 0 ≠ 0)
    (htrace : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ coordSubspace S → f z = a z * (d z * z t)) :
    fderiv ℂ f 0 (EuclideanSpace.single t 1) ≠ 0 := by
  let e : ComplexModel n := EuclideanSpace.single t 1
  have hline : HasDerivAt (fun z : ℂ => z • e) e 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const e
  have hfline : HasDerivAt (fun z : ℂ => f (z • e)) (fderiv ℂ f 0 e) 0 := by
    simpa only [Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have haline : DifferentiableAt ℂ (fun z : ℂ => a (z • e)) 0 := by
    have ha' : DifferentiableAt ℂ a ((fun z : ℂ => z • e) 0) := by simpa using ha
    exact ha'.comp 0 hline.differentiableAt
  have hdline : DifferentiableAt ℂ (fun z : ℂ => d (z • e)) 0 := by
    have hd' : DifferentiableAt ℂ d ((fun z : ℂ => z • e) 0) := by simpa using hd
    exact hd'.comp 0 hline.differentiableAt
  have hprod : HasDerivAt (fun z : ℂ => (a (z • e) * d (z • e)) * z) (a 0 * d 0) 0 := by
    have hp := (haline.hasDerivAt.mul hdline.hasDerivAt).mul (hasDerivAt_id (0 : ℂ))
    change HasDerivAt (fun z : ℂ => (a (z • e) * d (z • e)) * z) _ 0 at hp
    simpa only [zero_smul, Pi.mul_apply, id_eq, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one] using hp
  have hcont : Tendsto (fun z : ℂ => z • e) (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
    have hc : Continuous (fun z : ℂ => z • e) := by fun_prop
    simpa only [zero_smul] using hc.tendsto 0
  have heq : (fun z : ℂ => f (z • e)) =ᶠ[𝓝 0] (fun z => (a (z • e) * d (z • e)) * z) := by
    filter_upwards [hcont.eventually htrace] with z hz
    have hzS : z • e ∈ coordSubspace S := by
      intro i hi
      have hit : i ≠ t := fun h => ht (h ▸ hi)
      simp [e,hit]
    rw [hz hzS]
    simp [e, mul_assoc]
  have heqDeriv := hfline.unique (hprod.congr_of_eventuallyEq heq)
  change fderiv ℂ f 0 e ≠ 0
  rw [heqDeriv]
  exact mul_ne_zero ha0 hd0

end
end Hironaka.HironakaG4UnitTraceDerivative
