import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-!
# First-order equations on the exceptional trace of an arc chart

This is the analytic limit in the first-order strict-transform lemma used in
the proof of Bierstone--Milman 2008, Theorem 6.1. In an iterated point chart the
original coordinates have the form `t ^ r • v`. A limit of points with `t ≠ 0`
on the transform of a level set therefore satisfies the linearized equation.

The proof uses Mathlib's rescaled derivative limit, without requiring
analyticity, nonvanishing of the differential, or a chosen equation factor.
It proves only this analytic part of L1; the identification with the native
arc-tower strict transform and the carrier dimension argument are separate.
-/

open Filter Set
open scoped Topology

namespace Hironaka.HironakaG8P1ArcTangentLimit

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Directions of rescaled points in a level set lie in the kernel of its
linearized equation. The scale may vanish to any positive order. -/
theorem derivative_eq_zero_of_rescaled_levelSet
    {α : Type*} {l : Filter α} [l.NeBot]
    {f : E → F} {A : E →L[𝕜] F} {s : α → 𝕜} {v : α → E} {v₀ : E}
    (hf : HasFDerivAt f A 0)
    (hs : Tendsto s l (𝓝 0)) (hv : Tendsto v l (𝓝 v₀))
    (hsne : ∀ᶠ i in l, s i ≠ 0)
    (hlevel : ∀ᶠ i in l, f (s i • v i) = f 0) :
    A v₀ = 0 := by
  have harg : Tendsto (fun i => s i • v i) l (𝓝 (0 : E)) := by
    simpa only [zero_smul] using hs.smul hv
  have hcancel : (fun i => (s i)⁻¹ • (s i • v i)) =ᶠ[l] v := by
    filter_upwards [hsne] with i hi
    exact inv_smul_smul₀ hi (v i)
  have hdir : Tendsto (fun i => (s i)⁻¹ • (s i • v i)) l (𝓝 v₀) :=
    Filter.Tendsto.congr' hcancel.symm hv
  have hder := (hf.hasFDerivWithinAt (s := univ)).lim harg
    (Eventually.of_forall fun _ => mem_univ _) hdir
  have hzero : (fun i => (s i)⁻¹ • (f (0 + s i • v i) - f 0)) =ᶠ[l]
      (fun _ => (0 : F)) := by
    filter_upwards [hlevel] with i hi
    simp only [zero_add, hi, sub_self, smul_zero]
  exact tendsto_nhds_unique hder (Filter.Tendsto.congr' hzero.symm tendsto_const_nhds)

/-- In the chart `(v,t) ↦ t^r • v`, every exceptional point of the closure
of the inverse image of a level set satisfies its first-order equation. -/
theorem derivative_eq_zero_of_mem_closure_powerChart
    {f : E → F} {A : E →L[𝕜] F} {v₀ : E} {r : ℕ}
    (hf : HasFDerivAt f A 0) (hr : 0 < r)
    (hclosure : (v₀, (0 : 𝕜)) ∈
      closure {p : E × 𝕜 | p.2 ≠ 0 ∧ f (p.2 ^ r • p.1) = f 0}) :
    A v₀ = 0 := by
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hclosure
  have hv : Tendsto (fun i => (p i).1) atTop (𝓝 v₀) :=
    (continuous_fst.tendsto (v₀, (0 : 𝕜))).comp hlim
  have ht : Tendsto (fun i => (p i).2) atTop (𝓝 (0 : 𝕜)) :=
    (continuous_snd.tendsto (v₀, (0 : 𝕜))).comp hlim
  have hscale : Tendsto (fun i => (p i).2 ^ r) atTop (𝓝 (0 : 𝕜)) := by
    simpa only [zero_pow (Nat.ne_of_gt hr)] using ht.pow r
  exact derivative_eq_zero_of_rescaled_levelSet hf hscale hv
    (Eventually.of_forall fun i => pow_ne_zero r (hp i).1)
    (Eventually.of_forall fun i => (hp i).2)

end Hironaka.HironakaG8P1ArcTangentLimit
