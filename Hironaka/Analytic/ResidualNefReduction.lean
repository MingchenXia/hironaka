import Hironaka.Analytic.MeteredDivisorSmoothOffSupport
import Hironaka.Analytic.PshAnalyticSetExtension
import Hironaka.Blowup.BlowupBigPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:residual-nef`, the reduction half: the residual potential off `Supp D`

Source: Copy-4 `lem:residual-nef` (`transcendental-nakamaye-copy4-20260911`,
`source/main-Nulllocus.tex:328-336`), quoting Xia, *Singularities in global
pluripotential theory*, Lemma 1.6.1:

> Let `X` be a compact Kähler manifold, let `θ` be a smooth closed real
> `(1,1)`-form on `X`, and let `φ ∈ PSH(X, θ)` have log singularities along an
> effective `ℚ`-divisor `D`.  Then the class `{θ} - {D}` is nef.  If moreover
> `θ + ddᶜφ` is a Kähler current, then `{θ} - {D}` is Kähler.

This module contains the part of that lemma which needs **no** analytic input:
the passage from `φ` to its residual potential.  "Log singularities along `D`"
is, verbatim, `φ = ψ_D + b` with `b` a globally bounded real function, where
`ψ_D` is the weight of a smooth metric on `𝒪(D)` and `Θ_D` its curvature
(`Hironaka.HolomorphicIdealSheaves.MeteredEffectiveQDivisor`).  What is proved
here is

* `HasLogSingularitiesAlong` — the predicate, with no plurisubharmonicity
  assumption on `b` whatsoever;
* `thetaPshOff_residual` — **`b` is `(θ - Θ_D)`-PSH off `Supp D`.**  Off the
  support `ψ_D` is an honest smooth local potential of `-Θ_D`
  (`Hironaka.MeteredDivisorSmoothOffSupport`), so adding it to a smooth local
  potential of `θ` turns the `θ`-PSH germ of `φ` into a `(θ - Θ_D)`-PSH germ of
  `b`.  This is the potential-level form of `ddᶜψ_D = [D] - Θ_D` together with
  `[D] = 0` off `Supp D`;
* `HasLogSingularitiesAlong.locallyBoundedAboveOff` — the other hypothesis of
  the removable-singularity step, immediate from the bound on `b`;
* `HasLogSingularitiesAlong.support_ne_univ` — `Supp D ≠ X` as soon as `φ` is
  somewhere finite, so the removable-singularity step is never applied to a
  vacuous configuration.

Nothing here is `sorry`, and nothing here uses compactness, a Kähler
background, or connectedness.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ResidualNefReduction

open Hironaka.HolomorphicIdealSheaves
  Hironaka.NumericalRestrictedVolumeScaffold
  MeteredDivisorSmoothOffSupport MeteredDivisorWeightBounds
  ThetaPshCodimTwoExtension PshAnalyticSetExtension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Plurisubharmonicity on an open set only depends on the values there.**
Same three-line argument as `Hironaka.plurisubharmonicOn_congr`,
repeated here so that this module does not import the measure-theoretic
`Hironaka.PatchLocalBoundedMeasure`. -/
theorem plurisubharmonicOn_congr' {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {u w : E → EReal} {U : Set E} (hU : IsOpen U)
    (hu : PlurisubharmonicOn u U) (heq : EqOn u w U) : PlurisubharmonicOn w U := by
  intro x hx
  obtain ⟨V, hVopen, hxV, hV⟩ := hu x hx
  exact ⟨V ∩ U, hVopen.inter hU, ⟨hxV, hx⟩,
    (hV.mono inter_subset_left).congr (heq.mono inter_subset_right)⟩

/-! ### Adding smooth local potentials -/

/-- Smooth local potentials add: `ddᶜ(ρ + σ) = α + β` on the common piece. -/
theorem smoothDDC_add_of_isSmoothLocalPotential {α β : SmoothRealForm n M 2}
    {e : ComplexChart n M} {W : Set (ComplexModel n)} {ρ σ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential α e W ρ) (hσ : IsSmoothLocalPotential β e W σ)
    {z : ComplexModel n} (hz : z ∈ W) :
    smoothDDC (fun y => ρ y + σ y) z = α.coeff e z + β.coeff e z := by
  rw [smoothDDC_add hρ.1 hρ.2.2.1 hσ.2.2.1 hz, hρ.2.2.2 hz, hσ.2.2.2 hz]

/-! ### Log singularities along a metered effective `ℚ`-divisor -/

/-- **Log singularities along `D`** (Copy-4 `lem:residual-nef`, Xia 1.6.1): the
difference `φ - ψ_D` is a globally bounded real function.  No plurisubharmonicity
of the residual is assumed — that is the content of `thetaPshOff_residual` and
of the removable-singularity step which follows it. -/
structure HasLogSingularitiesAlong (D : MeteredEffectiveQDivisor n M)
    (φ : M → EReal) where
  /-- The residual potential `b = φ - ψ_D`, a genuine real function. -/
  residual : M → ℝ
  /-- A global bound for `b`. -/
  bound : ℝ
  /-- `b` is bounded, two-sidedly, by `bound`. -/
  residual_bound : ∀ x, |residual x| ≤ bound
  /-- `φ = ψ_D + b` pointwise, as extended reals. -/
  weight_add : ∀ x, φ x = D.weight x + (residual x : EReal)

namespace HasLogSingularitiesAlong

variable {D : MeteredEffectiveQDivisor n M} {φ : M → EReal}

theorem neg_bound_le (L : HasLogSingularitiesAlong D φ) (x : M) :
    -L.bound ≤ L.residual x :=
  neg_le_of_abs_le (L.residual_bound x)

theorem le_bound (L : HasLogSingularitiesAlong D φ) (x : M) :
    L.residual x ≤ L.bound :=
  le_of_abs_le (L.residual_bound x)

/-- Where `φ` is finite, so is `ψ_D`: such a point is off the support. -/
theorem notMem_support_of_ne_bot (L : HasLogSingularitiesAlong D φ) {x : M}
    (hx : φ x ≠ ⊥) : x ∉ D.support := by
  intro hmem
  refine hx ?_
  have hw : D.weight x = ⊥ := hmem
  rw [L.weight_add x, hw, EReal.bot_add]

/-- A locally nondegenerate `φ` forces `Supp D ≠ X`. -/
theorem support_ne_univ [Nonempty M] (L : HasLogSingularitiesAlong D φ)
    (hnd : LocallyNondegenerate φ) : D.support ≠ univ := by
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨y, -, hy⟩ := hnd x univ isOpen_univ (mem_univ x)
  exact fun hsupp => L.notMem_support_of_ne_bot hy (hsupp ▸ mem_univ y)

/-- The residual is bounded above everywhere, in particular off `Supp D`. -/
theorem locallyBoundedAboveOff (L : HasLogSingularitiesAlong D φ) :
    LocallyBoundedAboveOff D.support (fun x => (L.residual x : EReal)) :=
  fun _ => ⟨univ, univ_mem, L.bound,
    fun y _ _ => EReal.coe_le_coe_iff.mpr (L.le_bound y)⟩

end HasLogSingularitiesAlong

/-! ### The residual is `(θ - Θ_D)`-PSH off the support -/

/-- **The reduction half of `lem:residual-nef`.**  If `φ` is `θ`-PSH and has log
singularities along the metered effective `ℚ`-divisor `D`, then the residual
`b = φ - ψ_D` is `(θ - Θ_D)`-plurisubharmonic at every point off `Supp D`.

Off the support `ψ_D` is real-valued and an exact smooth local potential of
`-Θ_D`, so on a small enough chart piece `b + (ψ_D + ρ_θ) = φ + ρ_θ`; the
right-hand side is PSH because `φ` is `θ`-PSH, and the bracket is a smooth local
potential of `θ + (-Θ_D) = θ - Θ_D`. -/
theorem thetaPshOff_residual {θ : ClosedRealOneOneForm n M}
    {D : MeteredEffectiveQDivisor n M} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic θ.val φ) (L : HasLogSingularitiesAlong D φ) :
    ThetaPshOff (θ - D.curvature).val D.support
      (fun x => (L.residual x : EReal)) := by
  intro e z hz hzsupp
  have hxsource : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hex : e.val (e.val.symm z) = z := e.val.right_inv hz
  obtain ⟨W₁, hzW₁, hpot₁⟩ :=
    exists_isSmoothLocalPotential_neg_curvature D hzsupp e hxsource
  rw [hex] at hzW₁
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := hφ e z hz
  obtain ⟨F, -, hFeq⟩ :=
    exists_real_continuousAt_eventuallyEq_of_notMem_support D hzsupp
  obtain ⟨U₀, hU₀sub, hU₀open, hxU₀⟩ := mem_nhds_iff.mp hFeq
  set W₃ : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U₀ with hW₃def
  have hW₃open : IsOpen W₃ := e.val.isOpen_inter_preimage_symm hU₀open
  have hzW₃ : z ∈ W₃ := ⟨hz, hxU₀⟩
  set W : Set (ComplexModel n) := W₁ ∩ W₂ ∩ W₃ with hWdef
  have hWopen : IsOpen W := (hpot₁.1.inter hpot₂.1).inter hW₃open
  have hWW₁ : W ⊆ W₁ := inter_subset_left.trans inter_subset_left
  have hWW₂ : W ⊆ W₂ := inter_subset_left.trans inter_subset_right
  have hWW₃ : W ⊆ W₃ := inter_subset_right
  have hzW : z ∈ W := ⟨⟨hzW₁, hzW₂⟩, hzW₃⟩
  have hpot₁' : IsSmoothLocalPotential (-D.curvature).val e W
      (fun y => (D.weight (e.val.symm y)).toReal) := hpot₁.mono hWopen hWW₁
  have hpot₂' : IsSmoothLocalPotential θ.val e W ρ₂ := hpot₂.mono hWopen hWW₂
  -- the weight is real on `W`
  have hweight : ∀ y ∈ W, D.weight (e.val.symm y) =
      (((D.weight (e.val.symm y)).toReal : ℝ) : EReal) := by
    intro y hy
    have hyU₀ : e.val.symm y ∈ U₀ := (hWW₃ hy).2
    rw [hU₀sub hyU₀, EReal.toReal_coe]
  refine ⟨W, fun y => (D.weight (e.val.symm y)).toReal + ρ₂ y, hzW, ?_, ?_⟩
  · refine ⟨hWopen, hpot₁'.2.1, hpot₁'.2.2.1.add hpot₂'.2.2.1, ?_⟩
    intro y hy
    rw [smoothDDC_add_of_isSmoothLocalPotential hpot₁' hpot₂' hy,
      BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_neg]
    abel
  · refine plurisubharmonicOn_congr' hWopen (hpsh₂.mono hWW₂) ?_
    intro y hy
    show chartFunction φ e y + (ρ₂ y : EReal)
      = chartFunction (fun x => (L.residual x : EReal)) e y
        + (((D.weight (e.val.symm y)).toReal + ρ₂ y : ℝ) : EReal)
    simp only [chartFunction]
    rw [L.weight_add (e.val.symm y), EReal.coe_add, ← hweight y hy,
      add_comm (D.weight (e.val.symm y)) ((L.residual (e.val.symm y) : ℝ) : EReal),
      add_assoc]

end

end Hironaka.ResidualNefReduction
