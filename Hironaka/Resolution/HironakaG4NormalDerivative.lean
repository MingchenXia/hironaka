import Hironaka.Resolution.HironakaG4WeightedBinomialStraightening

/-! A nonzero first jet vanishing along a coordinate plane has a normal pivot. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG4NormalDerivative
noncomputable section
open Hironaka.BlowupSequences NormalCrossings

variable {n : ℕ}

/-- A holomorphic function vanishing on the carrier plane has zero first
partials in every free coordinate. -/
theorem free_partial_eq_zero {g : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U) (hg : DifferentiableAt ℂ g 0)
    (S : Finset (Fin n)) (hvan : ∀ z ∈ U, z ∈ coordSubspace S → g z = 0)
    (j : Fin n) (hj : j ∉ S) :
    fderiv ℂ g 0 (EuclideanSpace.single j 1) = 0 := by
  let e : ComplexModel n := EuclideanSpace.single j 1
  have hline : HasDerivAt (fun a : ℂ => a • e) e 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const e
  have hcomp : HasDerivAt (fun a : ℂ => g (a • e)) (fderiv ℂ g 0 e) 0 := by
    simpa only [Function.comp_def] using hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hevent : (fun a : ℂ => g (a • e)) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    have ht : Tendsto (fun a : ℂ => a • e) (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
      have hc : Continuous (fun a : ℂ => a • e) := by fun_prop
      simpa only [zero_smul] using hc.tendsto 0
    filter_upwards [ht.eventually (hU.mem_nhds h0)] with a ha
    apply hvan _ ha
    intro i hi
    have hij : i ≠ j := by intro h; subst i; exact hj hi
    simp [e, hij]
  have hzero : HasDerivAt (fun a : ℂ => g (a • e)) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hevent
  exact hcomp.unique hzero

/-- If the first derivative is nonzero, a coordinate in the carrier mask is a
nonzero partial derivative. -/
theorem exists_nonzero_normal_partial {g : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U) (hg : DifferentiableAt ℂ g 0)
    (S : Finset (Fin n)) (hvan : ∀ z ∈ U, z ∈ coordSubspace S → g z = 0)
    (hne : fderiv ℂ g 0 ≠ 0) :
    ∃ s ∈ S, fderiv ℂ g 0 (EuclideanSpace.single s 1) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hall (i : Fin n) : fderiv ℂ g 0 (EuclideanSpace.single i 1) = 0 := by
    by_cases hi : i ∈ S
    · exact h i hi
    · exact free_partial_eq_zero hU h0 hg S hvan i hi
  apply hne
  ext v
  have hvsum : v = ∑ j : Fin n, v j • EuclideanSpace.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  rw [hvsum, map_sum]
  simp [hall]

end
end Hironaka.HironakaG4NormalDerivative
