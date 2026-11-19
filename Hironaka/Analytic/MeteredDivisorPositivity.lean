import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.PotentialTheory.LocalPotentialsBasic
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.PolydiskPerronDataComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The current of a metered effective `ℚ`-divisor is positive

Source: Copy-4, `sec:qpsh` and Step 6 of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), where the chain

    `θ_Y + ddᶜ φ_U = Ω_U + [D] + (½δ₀ π^*ω + ddᶜ χ) ≥ Ω_U`

uses `[D] ≥ 0` for the effective `ℚ`-divisor `D` of `eq:def-DLY`.

A `MeteredEffectiveQDivisor` `E` on `M` carries a weight `ψ_E`, a curvature
`Θ_E` and, around every point, a presentation

    `ψ_E = ∑ aᵢ log |gᵢ|² + h`,   `Θ_E = -ddᶜ h`,

with `aᵢ ≥ 0` rational and `gᵢ` holomorphic.  Adding the local potential `-h` of
`Θ_E` therefore leaves exactly `∑ aᵢ log |gᵢ|²`, a nonnegative combination of
logarithms of squared absolute values of holomorphic functions, which is PSH.
That is the statement `[E] = Θ_E + ddᶜ ψ_E ≥ 0`, recorded here as

    `ThetaPlurisubharmonic E.curvature.val E.weight`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.MeteredDivisorPositivity

open Hironaka.HolomorphicIdealSheaves

noncomputable section

section Auxiliary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A finite sum of PSH functions is PSH.  No hypothesis beyond termwise
plurisubharmonicity is needed: `EReal` addition is monotone and `⊥`-absorbing. -/
theorem plurisubharmonicOn_finsetSum {ι : Type*} (s : Finset ι)
    {f : ι → E → EReal} {U : Set E} (hf : ∀ i ∈ s, PlurisubharmonicOn (f i) U) :
    PlurisubharmonicOn (fun y => ∑ i ∈ s, f i y) U := by
  classical
  induction s using Finset.induction with
  | empty => simpa using plurisubharmonicOn_const (E := E) 0 U
  | insert i s hi ih =>
      have heq : (fun y => ∑ j ∈ insert i s, f j y)
          = fun y => f i y + ∑ j ∈ s, f j y := by
        funext y
        rw [Finset.sum_insert hi]
      rw [heq]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A nonnegative rational multiple of `log ‖g‖²` for a holomorphic `g` is PSH.
The coefficient is allowed to vanish, in which case the function is the constant
`0` — the `EReal` convention `0 * ⊥ = 0` is what makes this uniform. -/
theorem plurisubharmonicOn_qsmul_generatorLog {U : Set E} (hU : IsOpen U)
    {a : ℚ} (ha : 0 ≤ a) {g : E → ℂ} (hg : DifferentiableOn ℂ g U) :
    PlurisubharmonicOn
      (fun y => ((a : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g) y) U := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have hfun : (fun y => ((a : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g) y)
        = fun _ : E => ((0 : ℝ) : EReal) := by
      funext y
      rw [← hzero]
      simp
    rw [hfun]
    exact plurisubharmonicOn_const (E := E) 0 U
  · have hposR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hpos
    intro x hx
    exact Hironaka.plurisubharmonicAt_scaled_generatorLog
      (f := fun _ : Fin 1 => g) (x := x) ⟨U, hU, hx, fun _ => hg⟩ hposR

end Auxiliary

section Divisor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Manifold holomorphy on `U`, read in an **arbitrary** chart of the atlas, is
ordinary complex differentiability on the part of that chart's target lying over
`U`.  `Hironaka.differentiableOn_comp_chartSymm` states this only for the
preferred chart at a point, which is not enough for a criterion quantified over
all charts. -/
theorem differentiableOn_comp_chartSymm (e : ComplexChart n M) {f : M → ℂ} {U : Set M}
    (hf : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U) :
    DifferentiableOn ℂ (fun z => f (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' U) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  have hsymm : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      e.val.symm e.val.target :=
    (contMDiffOn_symm_of_mem_maximalAtlas (n := ∞)
      (IsManifold.subset_maximalAtlas e.property)).mdifferentiableOn (by simp)
  exact hf.comp (hsymm.mono inter_subset_left) (fun z hz => hz.2)

/-- Cancelling the smooth part of a divisor weight.  Adding and then subtracting
a real number is exact on all of `EReal`, including at a pole of the weight:
`⊥ + t = ⊥` and `⊤ + t = ⊤` for every real `t`. -/
theorem add_coe_add_neg_coe (A : EReal) (t : ℝ) :
    A + (t : EReal) + ((-t : ℝ) : EReal) = A := by
  induction A using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
      rw [← EReal.coe_add, ← EReal.coe_add]
      congr 1
      ring

/-- **The current of a metered effective `ℚ`-divisor is positive**:
`[E] = Θ_E + ddᶜ ψ_E ≥ 0`. -/
theorem thetaPlurisubharmonic_weight (D : MeteredEffectiveQDivisor n M) :
    ThetaPlurisubharmonic D.curvature.val D.weight := by
  intro e z hz
  obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, -, hh, hw, hc⟩ :=
    D.local_presentation (e.val.symm z)
  set W : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U with hWdef
  have hWopen : IsOpen W := e.val.isOpen_inter_preimage_symm hU
  have hzW : z ∈ W := ⟨hz, by rw [mem_preimage]; exact hxU⟩
  have hhW : ContDiffOn ℝ ∞ (fun y => h (e.val.symm y)) W := hh e
  refine ⟨W, fun y => -h (e.val.symm y), hzW, ⟨hWopen, inter_subset_left, hhW.neg, ?_⟩, ?_⟩
  · intro y hy
    rw [smoothDDC_neg hWopen hhW hy, hc e y hy.1 hy.2]
  · -- the smooth part cancels and only `∑ aᵢ log |gᵢ|²` is left
    have heqOn : EqOn
        (fun y => chartFunction D.weight e y + ((-h (e.val.symm y) : ℝ) : EReal))
        (fun y => ∑ i, ((a i : ℝ) : EReal) *
          generatorLog (fun _ : Fin 1 => fun w => g i (e.val.symm w)) y) W := by
      intro y hy
      simp only [chartFunction]
      rw [hw (e.val.symm y) hy.2]
      exact add_coe_add_neg_coe _ _
    have hpsh : PlurisubharmonicOn
        (fun y => ∑ i, ((a i : ℝ) : EReal) *
          generatorLog (fun _ : Fin 1 => fun w => g i (e.val.symm w)) y) W :=
      plurisubharmonicOn_finsetSum _ fun i _ =>
        plurisubharmonicOn_qsmul_generatorLog hWopen (ha i)
          (differentiableOn_comp_chartSymm e (hg i))
    intro y hy
    refine (hpsh y hy).congr ?_
    filter_upwards [hWopen.mem_nhds hy] with w hw'
    exact (heqOn hw').symm

end Divisor

end

end Hironaka.MeteredDivisorPositivity
