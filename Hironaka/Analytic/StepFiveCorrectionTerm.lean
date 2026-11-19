import Hironaka.Analytic.IdealFunctionMaxGluing
import Hironaka.Analytic.MeteredDivisorWeightBounds
import Hironaka.Analytic.PullbackNonvanishing
import Hironaka.Analytic.PolarBranchStepThree
import Hironaka.Blowup.ExceptionalWeightBounds
import Hironaka.Analytic.IdealPowers

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 5: the correction term `χ` and the positive correction `ρ = ψ_D + χ`

Source: Copy-4, `prop:principalization`, Step 5 and Step 6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1908-1997`):

> Set `χ := ((C-1)/M) Ψ_m ∘ π` [...] Then `χ ≤ 0` is quasi-psh on `Y`, and it is
> smooth on the open set `π⁻¹(X \ (Z' ∪ Z(𝔅_m)))` [...] Moreover
> `ddᶜχ ≥ -((C-1)c_Ψ/M) π^*ω`, which is at least `-½δ₀ π^*ω` [...]
>
> `θ_Y + ddᶜφ_U = Ω_U + [D] + (½δ₀ π^*ω + ddᶜχ) ≥ Ω_U` [...] we may choose `y ∈ W`
> outside `Supp D` near which `χ` is smooth.  Then `φ_U` is smooth near `y`.

## What this module discharges

Two fields of `PrincipalizationCopy4StepFiveCoreReduction.Copy4StepFiveExceptionalWeightData`
that had no producer, with `ρ := ψ_D + κ Ψ ∘ π` (`correction_eq` is then `rfl`
with `χ := κ Ψ ∘ π`) and `β := θ_Y - Θ_D - δ π^*ω`:

* `positive_correction` — `ρ` is `(θ_Y - β)`-PSH on any `U`:
  `isThetaPshPotentialOn_correction`.  `θ_Y - β = Θ_D + δ π^*ω`; `ψ_D` is
  `Θ_D`-PSH (`[D] ≥ 0`), `κ Ψ ∘ π` is `κ c_Ψ π^*ω`-PSH, and the remaining
  `(δ - κ c_Ψ) π^*ω` is semipositive — Copy-4's choice `M ≥ 2(C-1)c_Ψ/δ₀`, i.e.
  `κ c_Ψ ≤ δ = ½δ₀`, is the hypothesis `hκδ`.  Local nondegeneracy comes from the
  identity principle on the connected `Y` and finiteness at one point.
* `smooth_rho_at_y` — `ρ` is smooth near any `y ∉ Supp D` with `Ψ` smooth near
  `π y`: `isSmoothNear_correction`.

`Ψ` is the output of `IdealFunctionMaxGluing.exists_idealFunction` (Copy-4
`lem:ideal-function`, applied to `𝔧 𝔅_m`), but here it is a hypothesis: any
`(c_Ψ ω)`-PSH `Ψ` works.  `π` is any holomorphic map; nothing about the
three-stage modification of Step 1 is used.

What `β` must still satisfy — `dominates_beta`, i.e. `β + ddᶜσ` dominates a
Kähler form near `W` — is Steps 4 and 6 (`lem:residual-nef` and the tube) and is
NOT addressed here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFiveCorrectionTerm

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.AnalyticGluingData Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold Hironaka.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-! ### Smoothness near a point -/

/-- Smoothness near `π y` pulls back to smoothness near `y` along a holomorphic map. -/
theorem IsSmoothNear.comp {π : Y → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {u : M → EReal} {y : Y}
    (hu : IsSmoothNear (n := n) u (π y)) : IsSmoothNear (n := n) (fun x => u (π x)) y := by
  obtain ⟨U, hU, hyU, h, hh, heq⟩ := hu
  exact ⟨π ⁻¹' U, hU.preimage hπ.continuous, hyU, fun x => h (π x),
    fun e => MeteredDivisorOperations.contDiffOn_comp_chart_symm hπ hU hh e,
    fun x hx => heq (π x) hx⟩

/-- A real multiple of a function smooth near a point is smooth near it. -/
theorem IsSmoothNear.const_mul {u : M → EReal} {p : M} (hu : IsSmoothNear (n := n) u p)
    (c : ℝ) : IsSmoothNear (n := n) (fun x => (c : EReal) * u x) p := by
  obtain ⟨U, hU, hpU, h, hh, heq⟩ := hu
  refine ⟨U, hU, hpU, fun x => c * h x, fun e => (hh e).const_smul c, fun x hx => ?_⟩
  dsimp only
  rw [heq x hx, ← EReal.coe_mul]

/-- The sum of two functions smooth near a point is smooth near it. -/
theorem IsSmoothNear.add {u v : M → EReal} {p : M} (hu : IsSmoothNear (n := n) u p)
    (hv : IsSmoothNear (n := n) v p) : IsSmoothNear (n := n) (fun x => u x + v x) p := by
  obtain ⟨U, hU, hpU, h, hh, heq⟩ := hu
  obtain ⟨V, hV, hpV, k, hk, hkeq⟩ := hv
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, fun x => h x + k x, fun e => ?_, fun x hx => ?_⟩
  · have hsub : e.val.target ∩ e.val.symm ⁻¹' (U ∩ V)
        ⊆ e.val.target ∩ e.val.symm ⁻¹' U := fun z hz => ⟨hz.1, hz.2.1⟩
    have hsub' : e.val.target ∩ e.val.symm ⁻¹' (U ∩ V)
        ⊆ e.val.target ∩ e.val.symm ⁻¹' V := fun z hz => ⟨hz.1, hz.2.2⟩
    exact ((hh e).mono hsub).add ((hk e).mono hsub')
  · dsimp only
    rw [heq x hx.1, hkeq x hx.2, ← EReal.coe_add]

/-- **Off its support, the weight of a metered divisor is smooth.**  Near the
point `ψ_E = ∑ aᵢ log ‖gᵢ‖² + h`, every `gᵢ` with `aᵢ > 0` is nonzero, and the
`gᵢ` are holomorphic. -/
theorem isSmoothNear_weight_of_notMem_support (E : MeteredEffectiveQDivisor n M) {x : M}
    (hx : x ∉ E.support) : IsSmoothNear (n := n) E.weight x := by
  classical
  obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, -, hh, hw, -⟩ := E.local_presentation x
  have hxbot : E.weight x ≠ ⊥ := hx
  have hgx : ∀ i, 0 < a i → g i x ≠ 0 := by
    intro i hai hgi
    refine hxbot ?_
    rw [hw x hxU]
    refine (EReal.add_eq_bot_iff.mpr (Or.inl ?_))
    refine MeteredDivisorWeightBounds.sum_eq_bot_of_eq_bot (Finset.mem_univ i) ?_
    rw [(generatorLog_eq_bot_iff _ x).mpr (fun _ => hgi),
      EReal.coe_mul_bot_of_pos (by exact_mod_cast hai)]
  -- the open set where the positive-coefficient generators do not vanish
  set O : Set M := U ∩ ⋂ i, {y | 0 < a i → g i y ≠ 0} with hOdef
  have hO : IsOpen O := by
    refine isOpen_iff_mem_nhds.mpr fun y hy => ?_
    refine inter_mem (hU.mem_nhds hy.1) (iInter_mem.mpr fun i => ?_)
    by_cases hai : 0 < a i
    · have hc : ContinuousAt (g i) y := ((hg i).continuousOn).continuousAt (hU.mem_nhds hy.1)
      filter_upwards [hc.eventually (isOpen_ne.mem_nhds (mem_iInter.mp hy.2 i hai))] with z hz
      exact fun _ => hz
    · exact Eventually.of_forall fun z h => absurd h hai
  have hxO : x ∈ O := ⟨hxU, mem_iInter.mpr hgx⟩
  refine ⟨O, hO, hxO, fun y => (∑ i, (a i : ℝ) * Real.log (‖g i y‖ ^ 2)) + h y,
    fun e => ?_, fun y hy => ?_⟩
  · set D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' O with hDdef
    have hDU : D ⊆ e.val.target ∩ e.val.symm ⁻¹' U := fun z hz => ⟨hz.1, hz.2.1⟩
    refine ContDiffOn.add (ContDiffOn.sum fun i _ => ?_) ((hh e).mono hDU)
    rcases eq_or_lt_of_le (ha i) with hai | hai
    · simp only [← hai, Rat.cast_zero, zero_mul]
      exact contDiffOn_const
    · refine contDiffOn_const.mul ?_
      have hhol : DifferentiableOn ℂ (fun z => g i (e.val.symm z))
          (e.val.target ∩ e.val.symm ⁻¹' U) :=
        MeteredDivisorPositivity.differentiableOn_comp_chartSymm e (hg i)
      have hsm : ContDiffOn ℝ ∞ (fun z => g i (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U) :=
        contDiffOn_real_of_differentiableOn_complex hhol
          (e.val.isOpen_inter_preimage_symm hU)
      refine (((contDiff_norm_sq ℝ).comp_contDiffOn (hsm.mono hDU)).log fun z hz => ?_)
      have hne : g i (e.val.symm z) ≠ 0 := mem_iInter.mp hz.2.2 i hai
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  · have hyne : ∀ i, 0 < a i → g i y ≠ 0 := fun i hai => mem_iInter.mp hy.2 i hai
    rw [hw y hy.1]
    have hterm : ∀ i, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y =
        (((a i : ℝ) * Real.log (‖g i y‖ ^ 2) : ℝ) : EReal) := by
      intro i
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · simp [← hai]
      · rw [MeteredDivisorWeightBounds.generatorLog_single_eq_coe (hyne i hai), ← EReal.coe_mul]
    simp only [hterm]
    rw [← MeteredDivisorWeightBounds.coe_finsetSum, ← EReal.coe_add]

/-- **`smooth_rho_at_y`.**  `ρ = ψ_D + κ Ψ ∘ π` is smooth near every point off
`Supp D` over which `Ψ` is smooth. -/
theorem isSmoothNear_correction {π : Y → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (D : MeteredEffectiveQDivisor n Y) {Ψ : M → EReal} (κ : ℝ) {y : Y}
    (hyD : y ∉ D.support) (hΨ : IsSmoothNear (n := n) Ψ (π y)) :
    IsSmoothNear (n := n) (fun x => D.weight x + (κ : EReal) * Ψ (π x)) y :=
  IsSmoothNear.add (isSmoothNear_weight_of_notMem_support D hyD)
    (IsSmoothNear.const_mul (IsSmoothNear.comp hπ hΨ) κ)

/-! ### The positive correction -/

/-- The correction `ρ = ψ_D + κ Ψ ∘ π` is `(Θ_D + δ π^*ω)`-PSH on `Y`, when `Ψ` is
`(c_Ψ ω)`-PSH, `κ > 0` and `κ c_Ψ ≤ δ`. -/
theorem thetaPlurisubharmonic_correction (omega : KahlerBackground n M) {π : Y → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (D : MeteredEffectiveQDivisor n Y) {Ψ : M → EReal} {cΨ κ δ : ℝ}
    (hΨ : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ) (hκ : 0 < κ) (hκδ : κ * cΨ ≤ δ) :
    ThetaPlurisubharmonic (D.curvature + δ • ClosedRealOneOneForm.pullback hπ omega.form).val
      (fun x => D.weight x + (κ : EReal) * Ψ (π x)) := by
  set ωY := ClosedRealOneOneForm.pullback hπ omega.form with hωY
  -- `Ψ ∘ π` is `c_Ψ π^*ω`-PSH
  have hΨπ : ThetaPlurisubharmonic (cΨ • ωY).val (fun x => Ψ (π x)) :=
    ((BlowupPushforward.pullback_smul_geometricallyEq hπ cΨ omega.form).thetaPlurisubharmonic_iff
      _).mp (GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ hΨ)
  have hsum := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos hκ
    (MeteredDivisorPositivity.thetaPlurisubharmonic_weight D) hΨπ
  have hsemi : ((δ - κ * cΨ) • ωY).val.IsSemipositive := by
    intro e z hz v
    rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (sub_nonneg.mpr hκδ)
      (ClosedRealOneOneForm.pullback_isSemipositive hπ omega.isSemipositive e z hz v)
  have hall := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hsum hsemi
  have hform : (1 : ℝ) • D.curvature + κ • (cΨ • ωY) + (δ - κ * cΨ) • ωY
      = D.curvature + δ • ωY := by
    module
  have hfun : (fun p => ((1 : ℝ) : EReal) * D.weight p + (κ : EReal) * Ψ (π p))
      = (fun x => D.weight x + (κ : EReal) * Ψ (π x)) := by
    funext p
    rw [EReal.coe_one, one_mul]
  rw [← hform, ← hfun]
  exact hall

/-- **`positive_correction`.**  With `β := θ_Y - Θ_D - δ π^*ω`, the correction
`ρ = ψ_D + κ Ψ ∘ π` is a `(θ_Y - β)`-PSH potential on any `U ⊆ Y`, provided `Y` is
connected and `ρ` is finite at one point (for instance at the point where it is
smooth, `IsSmoothNear.ne_bot`). -/
theorem isThetaPshPotentialOn_correction [ConnectedSpace Y] (omega : KahlerBackground n M)
    {π : Y → M} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θY : ClosedRealOneOneForm n Y) (D : MeteredEffectiveQDivisor n Y) {Ψ : M → EReal}
    {cΨ κ δ : ℝ} (hΨ : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ) (hκ : 0 < κ)
    (hκδ : κ * cΨ ≤ δ) {y₀ : Y} (hy₀ : D.weight y₀ + (κ : EReal) * Ψ (π y₀) ≠ ⊥)
    (U : Set Y) :
    IsThetaPshPotentialOn
      (θY - (θY - D.curvature - δ • ClosedRealOneOneForm.pullback hπ omega.form)).val
      (fun x => D.weight x + (κ : EReal) * Ψ (π x)) U := by
  have hpsh := thetaPlurisubharmonic_correction omega hπ D hΨ hκ hκδ
  have hform : θY - (θY - D.curvature - δ • ClosedRealOneOneForm.pullback hπ omega.form)
      = D.curvature + δ • ClosedRealOneOneForm.pullback hπ omega.form := by
    abel
  rw [hform]
  have hnd := ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh ⟨y₀, hy₀⟩
  exact ⟨fun e z hz _ => hpsh e z hz, fun x _ V hV hxV => hnd x V hV hxV⟩

/-! ### The correction weight -/

/-- **`correction_weight`.**  If `Ψ` has analytic singularities of type
`(1, 𝔧 𝔅)` on `X` (Copy-4 `eq:def-Psi`, `Ψ_m` for `𝔧 𝔅_m`), `ψ_𝔧` and `ψ_𝔅` have
types `(1, 𝔧)` and `(1, 𝔅)`, and the pulled-back `ψ_𝔅 ∘ π` is more singular than
`ψ_{H^fix}` on `Y` (Copy-4: `𝔅_m 𝒪 = 𝒪(-G̃_m)` and `G̃_m ≥ H^fix_m`, i.e. the
Step-1 data), then `χ = κ Ψ ∘ π` satisfies `χ ≤ κ (ψ_𝔧 ∘ π + ψ_{H^fix}) + O(1)`.

The coefficient of `ψ_𝔧` is `1`: in `Copy4StepFiveExceptionalWeightData` the
weight `psiJ = psij ∘ π` carries the ambient common coefficient of
`AmbientPhiRLowerSource`, which is `1` in Copy-4 (`ψ_{𝓘_V}`, `ψ_𝔧`). -/
theorem moreSingularOn_correction_weight [CompactSpace M] {π : Y → M}
    {Ψ psij psib : M → EReal} {psiHfix : Y → EReal} {𝔧 𝔟 : GermIdeal n M} {κ : ℝ}
    (hκ : 0 ≤ κ) (hΨ : HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟))
    (hj : HasAnalyticSingularitiesOfType (n := n) psij 1 𝔧)
    (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    (hHfix : MoreSingularOn (fun y => psib (π y)) psiHfix univ) :
    MoreSingularOn (fun y => (κ : EReal) * Ψ (π y))
      (fun y => (κ : EReal) * (psij (π y) + psiHfix y)) univ := by
  have hX : MoreSingularOn Ψ (fun x => psij x + psib x) univ :=
    (IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hΨ
      (IdealWeightPowers.hasAnalyticSingularitiesOfType_mul hj hb)).1
  have hY : MoreSingularOn (fun y => Ψ (π y)) (fun y => psij (π y) + psib (π y)) univ := by
    simpa using CollarWeightComparison.moreSingularOn_comp π hX
  exact ExceptionalWeightBounds.moreSingularOn_chi hκ (fun _ => rfl) hY hHfix

end

end Hironaka.StepFiveCorrectionTerm
