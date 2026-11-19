import Hironaka.Analytic.ERealChordUSC
import Hironaka.Analytic.RegularizedMaxEReal
import Hironaka.Analytic.SmoothOffPole

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The regularized maximum in the STRONG (CT22) analytic-singularity convention

`Hironaka.RegularizedMaxEReal` compares `M_δ(u,v)` with the ordinary maximum up
to the additive constant `δ`, which settles the BOUNDED convention.  The strong
convention of CT22 — locally `c · log Σ|fⱼ|² + b` with `b` SMOOTH — is not a
bounded-perturbation statement, and the ordinary maximum genuinely fails it near
the crossing locus.  This file proves what the regularized maximum does deliver.

The mechanism is translation equivariance.  `M_δ` commutes with adding the same
extended real to both arguments (`eregularizedMax_ereal_add`), and
`realRegularizedMax δ : ℝ × ℝ → ℝ` is smooth.  Hence if the two branches are
presented with the SAME coefficient and the SAME generator family,

    u = c·L_f + b₁,   v = c·L_f + b₂   (b₁, b₂ smooth),

then `M_δ(u,v) = c·L_f + M_δ(b₁,b₂)` exactly, and `M_δ(b₁,b₂)` is smooth: the
presentation is inherited verbatim, poles included.

Away from a COMMON pole no alignment is needed:

* at a point where both branches are finite, both are locally smooth real
  functions (`exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt`)
  and so is `M_δ` of them;
* at a point where exactly one branch is `-∞`, that branch drops below the other
  by more than `δ` on a neighbourhood, and `M_δ` equals the finite branch there
  *exactly* — the scale-`δ` gap is what makes this an equality of germs rather
  than a bounded comparison.

So the only obligation left is at common poles, and it is a statement about
GENERATORS, not about analysis; it is packaged downstream as
`Hironaka.FiniteRegularizedMaxCoreCover.PolewiseAlignedBranches`.  This is the precise
residue of the strong-convention multi-chart gluing recorded in I-0304.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.RegularizedMaxSmoothAnalyticType

open Hironaka
open Hironaka.RegularizedMaxEReal
open Hironaka
open Hironaka.AdmissibleCurrentFormPositivity

noncomputable section

/-! ## Translation equivariance and smoothness of the real regularized maximum -/

/-- `M_δ` commutes with adding a common extended real to both arguments.  The
hypothesis `t ≠ ⊤` is what keeps the `⊤` branches of `eregularizedMax` out of
the way; `t = ⊥` is allowed and is the case that matters at a pole. -/
theorem eregularizedMax_ereal_add {δ : ℝ} {t : EReal} (ht : t ≠ ⊤) (a b : ℝ) :
    eregularizedMax δ (t + (a : EReal)) (t + (b : EReal))
      = t + ((realRegularizedMax δ a b : ℝ) : EReal) := by
  induction t using EReal.rec with
  | bot => simp
  | coe s =>
      have hkey : realRegularizedMax δ (s + a) (s + b)
          = s + realRegularizedMax δ a b := by
        have harg : ((s + a) - (s + b)) / δ = (a - b) / δ := by ring
        rw [realRegularizedMax_apply, realRegularizedMax_apply, harg]
        ring
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
      rw [eregularizedMax_eq_coe_realRegularizedMax (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp only [EReal.toReal_coe]
      exact congrArg (fun r : ℝ => (r : EReal)) hkey
  | top => exact absurd rfl ht


/-- The real regularized maximum of two germs of smooth functions is a germ of a
smooth function: `realRegularizedMax δ a b = b + δ·P((a-b)/δ)` with `P` the
smooth positive part of `Hironaka.SmoothMax`. -/
theorem eventually_contDiffAt_realRegularizedMax {n : ℕ} {δ : ℝ}
    {b₁ b₂ : ComplexModel n → ℝ} {z : ComplexModel n}
    (h₁ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ b₁ y)
    (h₂ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ b₂ y) :
    ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (fun w => realRegularizedMax δ (b₁ w) (b₂ w)) y := by
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  simp only [realRegularizedMax_apply]
  refine hy₂.add (contDiffAt_const.mul ?_)
  exact (SmoothMax.contDiff_posPart.contDiffAt).comp y ((hy₁.sub hy₂).div_const δ)

/-- A scale-`δ` gap makes the regularized maximum EQUAL to the larger branch —
not merely close to it.  This is the property the ordinary maximum shares but
`M_δ` needs in order to inherit a smooth presentation. -/
theorem eregularizedMax_eq_right_of_gap {δ : ℝ} (hδ : 0 < δ) {a b : EReal}
    (hab : a + (δ : EReal) ≤ b) (hb : b ≠ ⊤) : eregularizedMax δ a b = b := by
  by_cases ha : a = ⊥
  · simp [ha]
  have hatop : a ≠ ⊤ := by
    intro h
    rw [h] at hab
    simp only [EReal.top_add_coe] at hab
    exact hb (top_le_iff.mp hab)
  have hbbot : b ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, EReal.add_eq_bot_iff] at hab
    rcases hab with h' | h'
    · exact ha h'
    · exact (EReal.coe_ne_bot δ) h'
  rw [eregularizedMax_eq_coe_formula hatop ha hb hbbot]
  have hreal : a.toReal + δ ≤ b.toReal := by
    have h1 : ((a.toReal + δ : ℝ) : EReal) ≤ ((b.toReal : ℝ) : EReal) := by
      rw [EReal.coe_add, EReal.coe_toReal hatop ha, EReal.coe_toReal hb hbbot]
      exact hab
    exact_mod_cast h1
  have hzero : SmoothMax.posPart ((a.toReal - b.toReal) / δ) = 0 := by
    refine SmoothMax.posPart_eq_zero ?_
    rw [div_le_iff₀ hδ]
    linarith
  rw [hzero]
  simp [EReal.coe_toReal hb hbbot]


/-! ## The aligned case: a common coefficient and a common generator family -/

/-- A positive multiple of a generator logarithm is never `⊤`. -/
theorem scaled_generatorLog_ne_top {X : Type*} {N : ℕ} {c : ℝ} (hc : 0 < c)
    (f : Fin N → X → ℂ) (y : X) : (c : EReal) * generatorLog f y ≠ ⊤ :=
  eReal_const_mul_ne_top hc.le (generatorLog_ne_top f y)

/-- **The strong convention is preserved by the regularized maximum when the two
branches are presented with the same coefficient and the same generators.**
The presentation of the result is the *same* `(c, f)`; only the smooth remainder
changes, from `(b₁, b₂)` to `M_δ(b₁, b₂)`.  Nothing is lost at the pole: the
identity holds across `L_f = -∞` as well. -/
theorem SmoothLogarithmicTypeAt.eregularizedMax_of_aligned {n : ℕ} {δ c : ℝ} {N : ℕ}
    {u v : ComplexModel n → EReal} {f : Fin N → ComplexModel n → ℂ}
    {z : ComplexModel n}
    (hu : SmoothLogarithmicTypeAt u c f z) (hv : SmoothLogarithmicTypeAt v c f z) :
    SmoothLogarithmicTypeAt (fun y => eregularizedMax δ (u y) (v y)) c f z := by
  obtain ⟨hc, hf, b₁, hb₁, heq₁⟩ := hu
  obtain ⟨-, -, b₂, hb₂, heq₂⟩ := hv
  refine ⟨hc, hf, fun y => realRegularizedMax δ (b₁ y) (b₂ y),
    eventually_contDiffAt_realRegularizedMax hb₁ hb₂, ?_⟩
  filter_upwards [heq₁, heq₂] with y hy₁ hy₂
  simp only [hy₁, hy₂]
  exact eregularizedMax_ereal_add (scaled_generatorLog_ne_top hc f y) _ _


/-! ## Away from a common pole: no alignment is needed -/

/-- At one of its own poles a branch with a smooth presentation drops below every
real level on a neighbourhood.  This is the ingredient that turns "one branch is
`-∞` here" into the scale-`δ` gap of `eregularizedMax_eq_right_of_gap`. -/
theorem eventually_le_of_smoothLogarithmicTypeAt_eq_bot {n N : ℕ} {c : ℝ}
    {u : ComplexModel n → EReal} {f : Fin N → ComplexModel n → ℂ}
    {z : ComplexModel n}
    (hu : SmoothLogarithmicTypeAt u c f z) (hz : u z = ⊥) (A : ℝ) :
    ∀ᶠ y in 𝓝 z, u y ≤ (A : EReal) := by
  obtain ⟨hc, hgen, b, hb, heq⟩ := hu
  obtain ⟨U, hU, hzU, hf⟩ := hgen
  obtain ⟨C, hC0, hCb⟩ := boundedRealGermAt_of_continuousAt (b := b) (x := z)
    hb.self_of_nhds.continuousAt
  have hvec : DifferentiableOn ℂ (generatorVector f) U := by
    rw [differentiableOn_piLp]
    exact hf
  have hcontLog : ContinuousOn (generatorLog f) U :=
    continuous_logNormSq.comp_continuousOn' hvec.continuousOn
  have hbot : generatorLog f z = ⊥ := by
    have h := heq.eq_of_nhds
    rw [hz] at h
    exact (generatorLog_eq_bot_iff f z).mpr
      ((scaled_generatorLog_add_eq_bot_iff f z hc (b z)).mp h.symm)
  have hcontAt : ContinuousAt (generatorLog f) z :=
    hcontLog.continuousAt (hU.mem_nhds hzU)
  set A' : ℝ := (A - C) / c with hA'def
  have hev : ∀ᶠ y in 𝓝 z, generatorLog f y < (A' : EReal) := by
    have hmem : Iio (A' : EReal) ∈ 𝓝 (generatorLog f z) := by
      rw [hbot]
      exact Iio_mem_nhds (EReal.bot_lt_coe _)
    exact hcontAt hmem
  have hcA' : c * A' = A - C := by
    rw [hA'def]
    field_simp
  filter_upwards [hev, hCb, heq] with y hy hyb hyeq
  rw [hyeq]
  have h1 : (c : EReal) * generatorLog f y ≤ (c : EReal) * (A' : EReal) :=
    Hironaka.monotone_eReal_const_mul hc.le hy.le
  have h2 : ((b y : ℝ) : EReal) ≤ ((C : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (abs_le.mp hyb).2
  calc (c : EReal) * generatorLog f y + (b y : EReal)
      ≤ (c : EReal) * (A' : EReal) + ((C : ℝ) : EReal) := add_le_add h1 h2
    _ = (A : EReal) := by
        rw [← EReal.coe_mul, hcA', ← EReal.coe_add]
        norm_num


/-- The mirror of `eregularizedMax_eq_right_of_gap`: below a scale-`δ` gap the
regularized maximum equals the LEFT branch exactly.  Proved directly from
`posPart_eq_self`, so no commutativity of `M_δ` is needed. -/
theorem eregularizedMax_eq_left_of_gap {δ : ℝ} (hδ : 0 < δ) {a b : EReal}
    (hba : b + (δ : EReal) ≤ a) (ha : a ≠ ⊤) : eregularizedMax δ a b = a := by
  by_cases hb : b = ⊥
  · simp [hb]
  have hbtop : b ≠ ⊤ := by
    intro h
    rw [h] at hba
    simp only [EReal.top_add_coe] at hba
    exact ha (top_le_iff.mp hba)
  have habot : a ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, EReal.add_eq_bot_iff] at hba
    rcases hba with h' | h'
    · exact hb h'
    · exact (EReal.coe_ne_bot δ) h'
  rw [eregularizedMax_eq_coe_formula ha habot hbtop hb]
  have hreal : b.toReal + δ ≤ a.toReal := by
    have h1 : ((b.toReal + δ : ℝ) : EReal) ≤ ((a.toReal : ℝ) : EReal) := by
      rw [EReal.coe_add, EReal.coe_toReal hbtop hb, EReal.coe_toReal ha habot]
      exact hba
    exact_mod_cast h1
  have hself : SmoothMax.posPart ((a.toReal - b.toReal) / δ) =
      (a.toReal - b.toReal) / δ := by
    refine SmoothMax.posPart_eq_self ?_
    rw [le_div_iff₀ hδ]
    linarith
  rw [hself]
  rw [show b.toReal + δ * ((a.toReal - b.toReal) / δ) = a.toReal by field_simp; ring]
  exact EReal.coe_toReal ha habot

/-- A germ that is locally a smooth real function trivially satisfies the strong
convention: take the one-element constant generator family. -/
theorem hasSmoothAnalyticSingularitiesAt_of_eventuallyEq_coe {n : ℕ}
    {u : ComplexModel n → EReal} {z : ComplexModel n} {g : ComplexModel n → ℝ}
    (hg : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y)
    (hu : u =ᶠ[𝓝 z] fun y => (g y : EReal)) :
    HasSmoothAnalyticSingularitiesAt u z := by
  refine ⟨1, 1, fun _ _ => (1 : ℂ), one_pos,
    ⟨univ, isOpen_univ, mem_univ z, fun _ => differentiableOn_const 1⟩, g, hg, ?_⟩
  filter_upwards [hu] with y hy
  rw [hy]
  have h0 : generatorLog (fun (_ : Fin 1) (_ : ComplexModel n) => (1 : ℂ)) y = 0 := by
    rw [generatorLog_of_nonzero ⟨0, one_ne_zero⟩]
    norm_num [generatorNormSq]
  rw [h0]
  simp

/-- The strong convention is stable under a germ equality. -/
theorem HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq {n : ℕ}
    {u w : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : HasSmoothAnalyticSingularitiesAt u z) (h : w =ᶠ[𝓝 z] u) :
    HasSmoothAnalyticSingularitiesAt w z := by
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hu
  exact ⟨c, N, f, hc, hf, b, hb, h.trans heq⟩


/-! ## The pointwise theorem: alignment is needed only at a COMMON pole -/

/-- **The regularized maximum of two branches in the strong CT22 convention is
again in the strong convention, provided the two presentations can be aligned at
their COMMON poles.**

The three cases are genuinely different:

* both branches finite at `z` — both are locally smooth real functions, and so is
  `M_δ` of them; no generators are involved;
* exactly one branch is `-∞` at `z` — that branch falls below the other by more
  than `δ` nearby, and `M_δ` equals the finite branch as a GERM;
* both branches are `-∞` at `z` — here, and only here, the hypothesis is used.

No alignment can hold at a point where exactly one branch is a pole (a family
witnessing the pole must vanish there, and a family witnessing finiteness must
not), which is why the hypothesis is conditioned on the common pole. -/
theorem hasSmoothAnalyticSingularitiesAt_eregularizedMax {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {u v : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : HasSmoothAnalyticSingularitiesAt u z)
    (hv : HasSmoothAnalyticSingularitiesAt v z)
    (halign : u z = ⊥ → v z = ⊥ →
      ∃ (c : ℝ) (N : ℕ) (f : Fin N → ComplexModel n → ℂ),
        SmoothLogarithmicTypeAt u c f z ∧ SmoothLogarithmicTypeAt v c f z) :
    HasSmoothAnalyticSingularitiesAt (fun y => eregularizedMax δ (u y) (v y)) z := by
  by_cases hub : u z = ⊥
  · by_cases hvb : v z = ⊥
    · obtain ⟨c, N, f, h₁, h₂⟩ := halign hub hvb
      exact ⟨c, N, f, SmoothLogarithmicTypeAt.eregularizedMax_of_aligned h₁ h₂⟩
    · -- `u` is the pole, `v` is finite: the glue is `v` near `z`.
      obtain ⟨g, hg, hvg⟩ :=
        exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt hv hvb
      obtain ⟨c, N, f, hu'⟩ := id hu
      have hglow : ∀ᶠ y in 𝓝 z, g z - 1 < g y :=
        continuousAt_const.eventually_lt hg.self_of_nhds.continuousAt (by linarith)
      have hulow := eventually_le_of_smoothLogarithmicTypeAt_eq_bot hu' hub (g z - 1 - δ)
      have hgerm : (fun y => eregularizedMax δ (u y) (v y)) =ᶠ[𝓝 z] v := by
        filter_upwards [hvg, hglow, hulow] with y hyv hyg hyu
        refine eregularizedMax_eq_right_of_gap hδ ?_ (by rw [hyv]; exact EReal.coe_ne_top _)
        have h1 : u y + (δ : EReal) ≤ ((g z - 1 - δ : ℝ) : EReal) + (δ : EReal) :=
          add_le_add hyu le_rfl
        refine h1.trans ?_
        rw [hyv, ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      exact HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq hv hgerm
  · by_cases hvb : v z = ⊥
    · -- `v` is the pole, `u` is finite: the glue is `u` near `z`.
      obtain ⟨g, hg, hug⟩ :=
        exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt hu hub
      obtain ⟨c, N, f, hv'⟩ := id hv
      have hglow : ∀ᶠ y in 𝓝 z, g z - 1 < g y :=
        continuousAt_const.eventually_lt hg.self_of_nhds.continuousAt (by linarith)
      have hvlow := eventually_le_of_smoothLogarithmicTypeAt_eq_bot hv' hvb (g z - 1 - δ)
      have hgerm : (fun y => eregularizedMax δ (u y) (v y)) =ᶠ[𝓝 z] u := by
        filter_upwards [hug, hglow, hvlow] with y hyu hyg hyv
        refine eregularizedMax_eq_left_of_gap hδ ?_ (by rw [hyu]; exact EReal.coe_ne_top _)
        have h1 : v y + (δ : EReal) ≤ ((g z - 1 - δ : ℝ) : EReal) + (δ : EReal) :=
          add_le_add hyv le_rfl
        refine h1.trans ?_
        rw [hyu, ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      exact HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq hu hgerm
    · -- both finite: the glue is a smooth real function near `z`.
      obtain ⟨g₁, hg₁, hug⟩ :=
        exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt hu hub
      obtain ⟨g₂, hg₂, hvg⟩ :=
        exists_smooth_eventuallyEq_of_hasSmoothAnalyticSingularitiesAt hv hvb
      refine hasSmoothAnalyticSingularitiesAt_of_eventuallyEq_coe
        (g := fun y => realRegularizedMax δ (g₁ y) (g₂ y))
        (eventually_contDiffAt_realRegularizedMax hg₁ hg₂) ?_
      filter_upwards [hug, hvg] with y hy₁ hy₂
      rw [hy₁, hy₂, eregularizedMax_eq_coe_realRegularizedMax (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp

end

end Hironaka.RegularizedMaxSmoothAnalyticType
