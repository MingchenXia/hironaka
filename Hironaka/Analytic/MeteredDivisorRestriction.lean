import Hironaka.Analytic.StepFourOnStrictTransform
import Hironaka.Analytic.PullbackNonvanishing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restricting a metered divisor to a submanifold, and Copy-4 Step 4 in the source's words

Source: Copy-4, `prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906`):

> `φ' := (π|_W)^*φ_{K,ℓ} + τψ_{E_rel}|_W` has log singularities along `D|_W` **with the
> restricted metric** [...] `θ' := (π^*θ - ½δ₀π^*ω)|_W` [...] By `lem:residual-nef`, the
> class `{θ'} - {D|_W} = {θ_Y - Θ_D - ½δ₀π^*ω}|_W` is Kähler on `W`.

`MeteredDivisorOperations.pullback` pulls a metered divisor back along a map between
manifolds of the **same** dimension whose exceptional locus has empty interior.  Restriction
to a submanifold changes the dimension, and the hypothesis that keeps the local generators
nonzero is different: it is Copy-4's *"no component of `D` contains `W`"*, which on the level
of weights says that `ψ_D ∘ ι` is `-∞` on no nonempty open subset of `V`.

* `restrictAlong` — `ι^*D` for a holomorphic `ι : V → M` (any dimensions) with that
  nondegeneracy: weight `ψ_D ∘ ι`, curvature `ι^*Θ_D` (the restricted metric).  Generators
  with coefficient `0` are replaced by `1`; the others stay nonzero on open sets because a
  positive multiple of `log|g|` with `g ≡ 0` would make `ψ_D ∘ ι ≡ -∞` there.
* `exists_positiveOnOneFlattening_of_restrictedDivisor` — Copy-4 Step 4 verbatim: if `φ'`
  is a Kähler-current potential of `θ' = (θ_Y - δ ω_Y)|_W` on the strict transform with log
  singularities along `D|_W`, then `θ_Y - Θ_D - δ ω_Y + ddᶜf̃` is strictly positive along
  `T_W` for a chart-smooth `f̃`.  The form identity `θ' - Θ_{D|_W} = β|_W` is now a
  theorem (pullback commutes with subtraction), not a hypothesis.

The restriction and its lemmas are sorry-free; the Step-4 theorem rests on
`lem:residual-nef`'s two named inputs, like `StepFourOnStrictTransform`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MeteredDivisorRestriction

open Hironaka.HolomorphicMaps Hironaka.HolomorphicIdealSheaves
  Hironaka.LocalPotentialPullback Hironaka.AnalyticGluingData Hironaka.BlowupSequences
  SubmanifoldChartedSpace ManifoldTubePositivity TubePositivityOneFlattening
  ResidualNefReduction StepFourOnStrictTransform

noncomputable section

variable {k n : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Chart calculus along a holomorphic map of any dimension -/

/-- A function chart-smooth on `U` composes with a holomorphic map to one chart-smooth on
`g⁻¹ U` (`MeteredDivisorOperations.contDiffOn_comp_chart_symm`, any source dimension). -/
theorem contDiffOn_comp_chart_symm {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {U : Set M} (hU : IsOpen U)
    {h : M → ℝ} (hh : ∀ d : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (d.val.symm z)) (d.val.target ∩ d.val.symm ⁻¹' U))
    (e : ComplexChart k V) :
    ContDiffOn ℝ ∞ (fun z => h (g (e.val.symm z))) (e.val.target ∩ e.val.symm ⁻¹' (g ⁻¹' U)) := by
  intro u hu
  let d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ coordinateDomain g e d := ⟨hu.1, mem_complexChartAt_source _⟩
  have hW : IsOpen (potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U)) :=
    potentialDomain_isOpen hg e d (d.val.isOpen_inter_preimage_symm hU)
  have hmem : u ∈ potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U) := by
    refine ⟨hud, coordinateMap_mem_target hud, ?_⟩
    change d.val.symm (d.val (g (e.val.symm u))) ∈ U
    rw [d.val.left_inv hud.2]
    exact hu.2
  have hcomp := (hh d).comp_inter (coordinateMap_contDiffOn_real hg e d)
  refine ((hcomp.contDiffAt (hW.mem_nhds hmem)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hud] with w hw
  change h (g (e.val.symm w)) = h (d.val.symm (d.val (g (e.val.symm w))))
  rw [d.val.left_inv hw.2]

/-- The coefficients of `g^* θ` for a form with local potentials `-h` on `U`, any source
dimension. -/
theorem coeff_pullback_eq_neg_smoothDDC {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ : ClosedRealOneOneForm n M} {U : Set M} (hU : IsOpen U) {h : M → ℝ}
    (hh : ∀ d : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (d.val.symm z)) (d.val.target ∩ d.val.symm ⁻¹' U))
    (hc : ∀ (d : ComplexChart n M) (z : ComplexModel n), z ∈ d.val.target →
      d.val.symm z ∈ U → θ.val.coeff d z = -smoothDDC (fun y => h (d.val.symm y)) z)
    (e : ComplexChart k V) {u : ComplexModel k} (hu : u ∈ e.val.target)
    (huU : e.val.symm u ∈ g ⁻¹' U) :
    (ClosedRealOneOneForm.pullback hg θ).val.coeff e u =
      -smoothDDC (fun y => h (g (e.val.symm y))) u := by
  let d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have hWo : IsOpen (d.val.target ∩ d.val.symm ⁻¹' U) := d.val.isOpen_inter_preimage_symm hU
  have hρ : IsSmoothLocalPotential θ.val d (d.val.target ∩ d.val.symm ⁻¹' U)
      (fun z => -h (d.val.symm z)) := by
    refine ⟨hWo, inter_subset_left, (hh d).neg, fun z hz => ?_⟩
    rw [hc d z hz.1 hz.2, smoothDDC_neg hWo (hh d) hz]
  have hmem : u ∈ potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U) := by
    refine ⟨hud, coordinateMap_mem_target hud, ?_⟩
    change d.val.symm (d.val (g (e.val.symm u))) ∈ U
    rw [d.val.left_inv hud.2]
    exact huU
  have hpot := (isSmoothLocalPotential_pullback hg e hρ).2.2.2 hmem
  rw [ClosedRealOneOneForm.pullback_val, ← hpot]
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (g ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (hU.preimage hg.continuous)
  rw [← smoothDDC_neg hS (contDiffOn_comp_chart_symm hg hU hh e) ⟨hu, huU⟩]
  apply smoothDDC_congr
  filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hud] with w hw
  change -h (d.val.symm (d.val (g (e.val.symm w)))) = -h (g (e.val.symm w))
  rw [d.val.left_inv hw.2]

/-! ### The restriction -/

/-- A weight presentation with one vanishing generator of positive coefficient is `-∞`. -/
theorem sum_add_eq_bot {N : ℕ} {a : Fin N → ℚ} {t : Fin N → EReal} {i : Fin N}
    (hai : 0 < a i) (hti : t i = ⊥) (r : ℝ) :
    (∑ j, ((a j : ℝ) : EReal) * t j) + (r : EReal) = ⊥ := by
  have hpos : (0 : ℝ) < (a i : ℝ) := by exact_mod_cast hai
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hti,
    EReal.coe_mul_bot_of_pos hpos, EReal.bot_add, EReal.bot_add]

variable (k) in
/-- **`ι^*D`, the restriction of a metered divisor along a holomorphic map** of any
dimension, when `ψ_D ∘ ι` is `-∞` on no nonempty open set (Copy-4: no component of `D`
contains `W`).  Weight `ψ_D ∘ ι`, curvature `ι^*Θ_D`: the restricted metric. -/
def restrictAlong {g : V → M} (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    (D : MeteredEffectiveQDivisor n M)
    (hnd : ∀ O : Set V, IsOpen O → O.Nonempty → ∃ v ∈ O, D.weight (g v) ≠ ⊥) :
    MeteredEffectiveQDivisor k V where
  weight := fun v => D.weight (g v)
  curvature := ClosedRealOneOneForm.pullback hg D.curvature
  local_presentation := fun v => by
    classical
    obtain ⟨U, hU, hvU, N, a, f, h, ha, hf, -, hh, hw, hc⟩ := D.local_presentation (g v)
    refine ⟨g ⁻¹' U, hU.preimage hg.continuous, hvU, N, a,
      fun i => if a i = 0 then (fun _ => 1) else f i ∘ g, fun y => h (g y), ha, ?_, ?_,
      fun e => contDiffOn_comp_chart_symm hg hU hh e, ?_,
      fun e u hu huU => coeff_pullback_eq_neg_smoothDDC hg hU hh hc e hu huU⟩
    · intro i y hy
      by_cases hai : a i = 0
      · simp only [hai, if_true]
        exact mdifferentiableWithinAt_const
      · simp only [hai, if_false]
        exact ((hf i (g y) hy).mdifferentiableAt (hU.mem_nhds hy)).comp_mdifferentiableWithinAt y
          ((hg y).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    · intro i O hO hOU hOne
      by_cases hai : a i = 0
      · obtain ⟨y, hy⟩ := hOne
        exact ⟨y, hy, by simp [hai]⟩
      · by_contra hcon
        push Not at hcon
        obtain ⟨y, hyO, hy⟩ := hnd O hO hOne
        apply hy
        rw [hw (g y) (hOU hyO)]
        refine sum_add_eq_bot (i := i) (lt_of_le_of_ne (ha i) (Ne.symm hai)) ?_ _
        rw [generatorLog_eq_bot_iff]
        intro _
        have := hcon y hyO
        simpa [hai] using this
    · intro y hy
      show D.weight (g y) = _
      rw [hw (g y) hy]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hai : a i = 0
      · simp [hai]
      · simp only [hai, if_false]
        rfl

@[simp] theorem weight_restrictAlong {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    (D : MeteredEffectiveQDivisor n M)
    (hnd : ∀ O : Set V, IsOpen O → O.Nonempty → ∃ v ∈ O, D.weight (g v) ≠ ⊥) (v : V) :
    (restrictAlong k hg D hnd).weight v = D.weight (g v) := rfl

@[simp] theorem curvature_restrictAlong {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    (D : MeteredEffectiveQDivisor n M)
    (hnd : ∀ O : Set V, IsOpen O → O.Nonempty → ∃ v ∈ O, D.weight (g v) ≠ ⊥) :
    (restrictAlong k hg D hnd).curvature = ClosedRealOneOneForm.pullback hg D.curvature := rfl

end

/-! ### Copy-4 Step 4 in the source's words -/

section StepFour

variable {n k : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

/-- **Copy-4 Step 4.**  Let `W` be a closed connected complex submanifold of dimension `k`
of a compact complex manifold, with its flattening complex structure, `θ_Y`, `ω_Y` closed
real `(1,1)`-forms, `δ ∈ ℝ`, and `D` a metered divisor no component of which contains `W`
(`ψ_D|_W ≢ -∞` on open sets).  If `φ'` is a Kähler-current potential on `W` of
`θ' = (θ_Y - δ ω_Y)|_W` with log singularities along `D|_W` (restricted metric), then for a
chart-smooth `f̃` on the ambient manifold, `θ_Y - Θ_D - δ ω_Y + ddᶜf̃` is strictly positive
along the tangent directions of `W` (`eq:AW-class`, read as Step 6 uses it). -/
theorem exists_positiveOnOneFlattening_of_restrictedDivisor [CompactSpace X]
    (hW : IsClosedConnectedSubmanifold n W k) (θY ωY : ClosedRealOneOneForm n X) (δ : ℝ)
    (D : MeteredEffectiveQDivisor n X) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ (hnd : ∀ O : Set W, IsOpen O → O.Nonempty → ∃ p ∈ O, D.weight (p : X) ≠ ⊥)
      {φ' : W → EReal},
      IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback
        (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2) (θY - δ • ωY)) φ' →
      HasLogSingularitiesAlong
        (restrictAlong k (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2) D hnd)
        φ' →
      ∃ (f : X → ℝ) (hf : ChartSmooth (n := n) f),
        PositiveOnOneFlattening W k (θY - D.curvature - δ • ωY + ddcClosedForm f hf) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  intro hnd φ' hφ' hlog
  refine exists_positiveOnOneFlattening_of_logSingularities_strictTransform hW
    (θY - D.curvature - δ • ωY) hφ' hlog ?_
  intro e z hz
  have hform : θY - D.curvature - δ • ωY = (θY - δ • ωY) - D.curvature := by abel
  rw [hform, curvature_restrictAlong]
  exact (BlowupBigPullback.pullback_sub_geometricallyEq (contMDiff_val hk hW.2.2)
    (θY - δ • ωY) D.curvature e hz).symm

end StepFour

end Hironaka.MeteredDivisorRestriction
