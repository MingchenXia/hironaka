import Hironaka.Analytic.RegularizedMaxOffPoleAnalyticType

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The regularized maximum in the `I-0489` convention: concatenate, do not align

`Hironaka.RegularizedMaxSmoothAnalyticType` needs the two branches of `M_δ(u,v)`
to be presented by the *same* generator family at a common pole, because the
STRONG convention asks the remainder to be smooth ACROSS the poles and
`M_δ(c·L + b₁, c·L + b₂) = c·L + M_δ(b₁,b₂)` only when the logarithm `L` is
literally shared.  That alignment obligation is
`Hironaka.FiniteRegularizedMaxCoreCover.PolewiseAlignedBranches`, and nothing in
the tree produces it.

`I-0489` fixed a weaker convention: the remainder is BOUNDED near the point and
`C^∞` only off the pole set (`Hironaka.BoundedSmoothOffPoleLogarithmicTypeAt`).
**In that convention alignment is not needed at all.**  Two branches with the
same positive coefficient `c` and arbitrary families `f`, `g` combine under
`M_δ` with the concatenated family `Fin.append f g`:

* the remainder is bounded, because the ordinary maximum already has the
  concatenated presentation
  (`Hironaka.DemaillyAnalyticType.LogarithmicTypeAt.max_of_generators`) and `M_δ`
  differs from `max` by at most `δ`
  (`LogarithmicTypeAt.of_sandwich`);
* off the pole set of `Fin.append f g` at least one of the two branches is
  finite, so only the *second* and *third* cases of the three-case analysis of
  `hasSmoothAnalyticSingularitiesAt_eregularizedMax` occur — and those are
  exactly the cases whose proofs never mention a common family.  Where both
  branches are finite `M_δ` is a smooth function of two smooth functions; where
  exactly one is a pole, the pole falls below the other branch by more than `δ`
  and `M_δ` equals the finite branch as a germ.

The device that makes the second bullet a *pointwise* statement at nearby points
rather than only at the centre is the **localization** of the presentation
predicates (`LogarithmicTypeAt.eventually` and its off-pole analogue): all three
clauses of the definition are witnessed on one honest open neighbourhood, so
every point of that neighbourhood inherits the presentation.

Combined with `canonicalRemainder` this yields the off-pole analogue of
`Hironaka.FiniteRegularizedMaxCoreCover.hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued_of_coreCover`
with `PolewiseAlignedBranches` replaced by the hypothesis that all branches carry
ONE coefficient — which for a level-`m` Bergman atlas is `c = 1/m` and is
available (I-0508).
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.RegularizedMaxOffPoleAppend

open Hironaka
open Hironaka
open Hironaka.AdmissibleCurrentFormPositivity
open Hironaka.DemaillyAnalyticType
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxSmoothAnalyticType
open Hironaka.RegularizedMaxOffPoleAnalyticType

noncomputable section

/-! ### The polar locus, read off the generators -/

section Generators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The pole set of a generator family is cut out by the vanishing of its norm
square, in either description. -/
theorem generatorNormSq_eq_zero_iff_generatorLog_eq_bot {k : ℕ} (h : Fin k → X → ℂ)
    (y : X) : generatorNormSq h y = 0 ↔ generatorLog h y = ⊥ := by
  refine ⟨generatorLog_eq_bot_of_normSq_eq_zero h, fun hy => ?_⟩
  have hzero : ∀ j, h j y = 0 := (generatorLog_eq_bot_iff h y).mp hy
  simp [generatorNormSq, hzero]

/-- A branch presented by `(c, h)` is a pole exactly where its generators all
vanish; in terms of the norm square this is the `if` condition of
`canonicalRemainder`. -/
theorem eq_bot_iff_generatorNormSq_eq_zero {u : X → EReal} {c : ℝ} {k : ℕ}
    {h : Fin k → X → ℂ} {y : X} (hu : LogarithmicTypeAt u c h y) :
    u y = ⊥ ↔ generatorNormSq h y = 0 :=
  hu.eq_bot_iff.trans
    ((generatorNormSq_eq_zero_iff_generatorLog_eq_bot h y).trans
      (generatorLog_eq_bot_iff h y)).symm

end Generators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Finiteness above: a logarithmic presentation never reaches `⊤` -/

/-- A bounded logarithmic presentation is a sum of a nonpositive-infinity term and
a real one, so it is `< ⊤` on the whole neighbourhood where it holds. -/
theorem LogarithmicTypeAt.eventually_ne_top {u : X → EReal} {c : ℝ} {k : ℕ}
    {h : Fin k → X → ℂ} {z : X} (hu : LogarithmicTypeAt u c h z) :
    ∀ᶠ y in 𝓝 z, u y ≠ ⊤ := by
  obtain ⟨hc, -, b, -, heq⟩ := hu
  filter_upwards [heq] with y hy
  rw [hy]
  exact EReal.add_ne_top (scaled_generatorLog_ne_top hc h y) (EReal.coe_ne_top _)

/-! ### Localization: a presentation at `z` is a presentation near `z` -/

/-- **A bounded logarithmic presentation at `z` holds at every nearby point.**
Each of the three clauses of `LogarithmicTypeAt` is witnessed on an honest open
neighbourhood of `z`, and that one neighbourhood then serves every point in it. -/
theorem LogarithmicTypeAt.eventually {u : X → EReal} {c : ℝ} {k : ℕ}
    {h : Fin k → X → ℂ} {z : X} (hu : LogarithmicTypeAt u c h z) :
    ∀ᶠ y in 𝓝 z, LogarithmicTypeAt u c h y := by
  obtain ⟨hc, ⟨U, hU, hzU, hUh⟩, b, ⟨C, hC0, hCb⟩, heq⟩ := hu
  have hmem : {y : X | |b y| ≤ C ∧
      u y = (c : EReal) * generatorLog h y + (b y : EReal)} ∩ U ∈ 𝓝 z :=
    inter_mem (hCb.and heq) (hU.mem_nhds hzU)
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hmem
  filter_upwards [hW.mem_nhds hzW] with y hy
  refine ⟨hc, ⟨U, hU, (hWsub hy).2, hUh⟩, b, ⟨C, hC0, ?_⟩, ?_⟩
  · filter_upwards [hW.mem_nhds hy] with w hw using (hWsub hw).1.1
  · filter_upwards [hW.mem_nhds hy] with w hw using (hWsub hw).1.2

variable [NormedSpace ℝ X]

/-- **The `I-0489` presentation at `z` holds at every nearby point.**  The
off-pole smoothness clause is itself a germ statement, so it localizes together
with the other two. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.eventually {u : X → EReal} {c : ℝ}
    {k : ℕ} {h : Fin k → X → ℂ} {z : X}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c h z) :
    ∀ᶠ y in 𝓝 z, BoundedSmoothOffPoleLogarithmicTypeAt u c h y := by
  obtain ⟨hc, ⟨U, hU, hzU, hUh⟩, b, ⟨C, hC0, hCb⟩, hsm, heq⟩ := hu
  have hmem : {y : X | (|b y| ≤ C ∧ (generatorNormSq h y ≠ 0 → ContDiffAt ℝ ∞ b y)) ∧
      u y = (c : EReal) * generatorLog h y + (b y : EReal)} ∩ U ∈ 𝓝 z :=
    inter_mem ((hCb.and hsm).and heq) (hU.mem_nhds hzU)
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hmem
  filter_upwards [hW.mem_nhds hzW] with y hy
  refine ⟨hc, ⟨U, hU, (hWsub hy).2, hUh⟩, b, ⟨C, hC0, ?_⟩, ?_, ?_⟩
  · filter_upwards [hW.mem_nhds hy] with w hw using (hWsub hw).1.1.1
  · filter_upwards [hW.mem_nhds hy] with w hw using (hWsub hw).1.1.2
  · filter_upwards [hW.mem_nhds hy] with w hw using (hWsub hw).1.2

/-! ### At its own pole a bounded presentation falls below every level -/

/-- The bounded-remainder version of
`Hironaka.RegularizedMaxSmoothAnalyticType.eventually_le_of_smoothLogarithmicTypeAt_eq_bot`:
smoothness of the remainder is never used there, only its boundedness. -/
theorem eventually_le_of_logarithmicTypeAt_eq_bot {k : ℕ} {c : ℝ} {u : X → EReal}
    {h : Fin k → X → ℂ} {z : X} (hu : LogarithmicTypeAt u c h z) (hz : u z = ⊥)
    (A : ℝ) : ∀ᶠ y in 𝓝 z, u y ≤ (A : EReal) := by
  obtain ⟨hc, ⟨U, hU, hzU, hUh⟩, b, ⟨C, hC0, hCb⟩, heq⟩ := hu
  have hvec : DifferentiableOn ℂ (generatorVector h) U := by
    rw [differentiableOn_piLp]
    exact hUh
  have hcontLog : ContinuousOn (generatorLog h) U :=
    continuous_logNormSq.comp_continuousOn' hvec.continuousOn
  have hbot : generatorLog h z = ⊥ := by
    have hz' : u z = ⊥ := hz
    rw [heq.eq_of_nhds] at hz'
    exact (generatorLog_eq_bot_iff h z).mpr
      ((scaled_generatorLog_add_eq_bot_iff h z hc (b z)).mp hz')
  have hcontAt : ContinuousAt (generatorLog h) z :=
    hcontLog.continuousAt (hU.mem_nhds hzU)
  set A' : ℝ := (A - C) / c with hA'def
  have hev : ∀ᶠ y in 𝓝 z, generatorLog h y < (A' : EReal) := by
    have hmem : Iio (A' : EReal) ∈ 𝓝 (generatorLog h z) := by
      rw [hbot]
      exact Iio_mem_nhds (EReal.bot_lt_coe _)
    exact hcontAt hmem
  have hcA' : c * A' = A - C := by
    rw [hA'def]
    field_simp
  filter_upwards [hev, hCb, heq] with y hy hyb hyeq
  rw [hyeq]
  have h1 : (c : EReal) * generatorLog h y ≤ (c : EReal) * (A' : EReal) :=
    Hironaka.monotone_eReal_const_mul hc.le hy.le
  have h2 : ((b y : ℝ) : EReal) ≤ ((C : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (abs_le.mp hyb).2
  calc (c : EReal) * generatorLog h y + (b y : EReal)
      ≤ (c : EReal) * (A' : EReal) + ((C : ℝ) : EReal) := add_le_add h1 h2
    _ = (A : EReal) := by
        rw [← EReal.coe_mul, hcA', ← EReal.coe_add]
        norm_num

/-! ### Off the appended pole set the regularized maximum is a smooth real germ -/

section Model

variable {n : ℕ}

/-- **Away from a COMMON pole, `M_δ(u,v)` is locally a smooth real function.**

This is the three-case analysis of
`Hironaka.RegularizedMaxSmoothAnalyticType.hasSmoothAnalyticSingularitiesAt_eregularizedMax`
with its first case — both branches polar, the only one that needed a common
generator family — deleted by hypothesis.  The two surviving cases are proved
exactly as there: where both branches are finite, `M_δ` is the smooth real
`realRegularizedMax` of the two smooth real germs; where exactly one is polar,
that branch falls below the other by more than `δ` nearby, so `M_δ` equals the
finite branch as a germ. -/
theorem exists_smooth_eventuallyEq_eregularizedMax {δ : ℝ} (hδ : 0 < δ)
    {u v : ComplexModel n → EReal} {y : ComplexModel n}
    (hu : HasAnalyticSingularitiesSmoothOffPoleAt u y)
    (hv : HasAnalyticSingularitiesSmoothOffPoleAt v y)
    (hne : ¬(u y = ⊥ ∧ v y = ⊥)) :
    ∃ φ : ComplexModel n → ℝ, (∀ᶠ w in 𝓝 y, ContDiffAt ℝ ∞ φ w) ∧
      (fun w => eregularizedMax δ (u w) (v w)) =ᶠ[𝓝 y] fun w => (φ w : EReal) := by
  by_cases hub : u y = ⊥
  · -- `u` is the pole, `v` is finite: the germ is `v`.
    have hvb : v y ≠ ⊥ := fun h => hne ⟨hub, h⟩
    obtain ⟨g, hg, hvg⟩ :=
      exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hv hvb
    obtain ⟨c, N, fam, hu'⟩ := hu
    have hglow : ∀ᶠ w in 𝓝 y, g y - 1 < g w :=
      continuousAt_const.eventually_lt hg.self_of_nhds.continuousAt (by linarith)
    have hulow := eventually_le_of_logarithmicTypeAt_eq_bot hu'.logarithmicTypeAt hub
      (g y - 1 - δ)
    refine ⟨g, hg, ?_⟩
    filter_upwards [hvg, hglow, hulow] with w hwv hwg hwu
    have hgap : u w + (δ : EReal) ≤ v w := by
      refine (add_le_add hwu (le_refl ((δ : ℝ) : EReal))).trans ?_
      rw [hwv, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    rw [eregularizedMax_eq_right_of_gap hδ hgap (by rw [hwv]; exact EReal.coe_ne_top _), hwv]
  · by_cases hvb : v y = ⊥
    · -- `v` is the pole, `u` is finite: the germ is `u`.
      obtain ⟨g, hg, hug⟩ :=
        exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hu hub
      obtain ⟨c, N, fam, hv'⟩ := hv
      have hglow : ∀ᶠ w in 𝓝 y, g y - 1 < g w :=
        continuousAt_const.eventually_lt hg.self_of_nhds.continuousAt (by linarith)
      have hvlow := eventually_le_of_logarithmicTypeAt_eq_bot hv'.logarithmicTypeAt hvb
        (g y - 1 - δ)
      refine ⟨g, hg, ?_⟩
      filter_upwards [hug, hglow, hvlow] with w hwu hwg hwv
      have hgap : v w + (δ : EReal) ≤ u w := by
        refine (add_le_add hwv (le_refl ((δ : ℝ) : EReal))).trans ?_
        rw [hwu, ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      rw [eregularizedMax_eq_left_of_gap hδ hgap (by rw [hwu]; exact EReal.coe_ne_top _), hwu]
    · -- both branches finite: a smooth real function of two smooth real functions.
      obtain ⟨g₁, hg₁, hug⟩ :=
        exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hu hub
      obtain ⟨g₂, hg₂, hvg⟩ :=
        exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hv hvb
      refine ⟨fun w => realRegularizedMax δ (g₁ w) (g₂ w),
        eventually_contDiffAt_realRegularizedMax hg₁ hg₂, ?_⟩
      filter_upwards [hug, hvg] with w hw₁ hw₂
      rw [hw₁, hw₂, eregularizedMax_eq_coe_realRegularizedMax (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp

/-! ### The append theorem -/

/-- **The regularized maximum of two branches in the `I-0489` convention, with one
common coefficient, is again in that convention — presented by the CONCATENATED
generator family, with no alignment hypothesis whatsoever.**

Boundedness of the remainder comes from
`Hironaka.DemaillyAnalyticType.LogarithmicTypeAt.max_of_generators` (the ordinary
maximum already has the concatenated presentation) together with
`LogarithmicTypeAt.of_sandwich` (`max ≤ M_δ ≤ max + δ`).  Smoothness off the
concatenated pole set is `exists_smooth_eventuallyEq_eregularizedMax`: a point
where the concatenated generators do not all vanish is a point where the two
branches do not have a common pole, so the alignment case never arises.

This is the statement that removes
`Hironaka.FiniteRegularizedMaxCoreCover.PolewiseAlignedBranches` from the route;
the price is the single common coefficient `c`, which for a level-`m` Bergman
atlas is `c = 1/m` and is available (`I-0508`). -/
theorem boundedSmoothOffPoleLogarithmicTypeAt_eregularizedMax_append {δ : ℝ}
    (hδ : 0 < δ) {u v : ComplexModel n → EReal} {z : ComplexModel n} {c : ℝ}
    {k l : ℕ} {f : Fin k → ComplexModel n → ℂ} {g : Fin l → ComplexModel n → ℂ}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c f z)
    (hv : BoundedSmoothOffPoleLogarithmicTypeAt v c g z) :
    BoundedSmoothOffPoleLogarithmicTypeAt
      (fun y => eregularizedMax δ (u y) (v y)) c (Fin.append f g) z := by
  obtain ⟨hc, hfgen, -⟩ := id hu
  obtain ⟨-, hggen, -⟩ := id hv
  have hLu : LogarithmicTypeAt u c f z := hu.logarithmicTypeAt
  have hLv : LogarithmicTypeAt v c g z := hv.logarithmicTypeAt
  have hmax : LogarithmicTypeAt (fun y => max (u y) (v y)) c (Fin.append f g) z :=
    LogarithmicTypeAt.max_of_generators hLu hLv
  have hsand : ∀ᶠ y in 𝓝 z, max (u y) (v y) ≤ eregularizedMax δ (u y) (v y) ∧
      eregularizedMax δ (u y) (v y) ≤ max (u y) (v y) + (δ : EReal) := by
    filter_upwards [LogarithmicTypeAt.eventually_ne_top hLu,
      LogarithmicTypeAt.eventually_ne_top hLv] with y hy₁ hy₂
    exact max_le_eregularizedMax_le_max_add hδ hy₁ hy₂
  have hM : LogarithmicTypeAt (fun y => eregularizedMax δ (u y) (v y)) c
      (Fin.append f g) z := LogarithmicTypeAt.of_sandwich hδ.le hmax hsand
  obtain ⟨hbdd, heqM⟩ := LogarithmicTypeAt.canonical hM
  obtain ⟨U, hU, hzU, hUfg⟩ := id (HolomorphicGeneratorsAt.append hfgen hggen)
  have hsmoothSq : ContDiffOn ℝ ∞ (generatorNormSq (Fin.append f g)) U := by
    unfold generatorNormSq
    refine ContDiffOn.sum fun j _ => ?_
    have hj : ContDiffOn ℝ ∞ (Fin.append f g j) U :=
      contDiffOn_real_of_differentiableOn_complex (hUfg j) hU
    exact (contDiff_norm_sq ℝ).comp_contDiffOn hj
  refine ⟨hc, HolomorphicGeneratorsAt.append hfgen hggen,
    canonicalRemainder c (Fin.append f g) (fun y => eregularizedMax δ (u y) (v y)),
    hbdd, ?_, heqM⟩
  filter_upwards [BoundedSmoothOffPoleLogarithmicTypeAt.eventually hu,
    BoundedSmoothOffPoleLogarithmicTypeAt.eventually hv, hU.mem_nhds hzU]
    with y hyu hyv hyU hynz
  -- at `y` the two branches have no common pole
  have hne : ¬(u y = ⊥ ∧ v y = ⊥) := by
    rintro ⟨h₁, h₂⟩
    refine hynz ?_
    rw [generatorNormSq_append,
      (eq_bot_iff_generatorNormSq_eq_zero hyu.logarithmicTypeAt).mp h₁,
      (eq_bot_iff_generatorNormSq_eq_zero hyv.logarithmicTypeAt).mp h₂, add_zero]
  obtain ⟨φ, hφ, hMφ⟩ := exists_smooth_eventuallyEq_eregularizedMax hδ
    ⟨c, k, f, hyu⟩ ⟨c, l, g, hyv⟩ hne
  have hsqy : ContDiffAt ℝ ∞ (generatorNormSq (Fin.append f g)) y :=
    hsmoothSq.contDiffAt (hU.mem_nhds hyU)
  have hposNear : ∀ᶠ w in 𝓝 y, generatorNormSq (Fin.append f g) w ≠ 0 :=
    hsqy.continuousAt.eventually_ne hynz
  have hcongr : canonicalRemainder c (Fin.append f g)
      (fun w => eregularizedMax δ (u w) (v w)) =ᶠ[𝓝 y]
      fun w => φ w - c * Real.log (generatorNormSq (Fin.append f g) w) := by
    filter_upwards [hposNear, hMφ] with w hw hwφ
    simp only [canonicalRemainder, if_neg hw, hwφ, EReal.toReal_coe]
  exact (hφ.self_of_nhds.sub (contDiffAt_const.mul (hsqy.log hynz))).congr_of_eventuallyEq
    hcongr

/-- The existential form of the append theorem: in the `I-0489` convention the
regularized maximum of two branches sharing one coefficient has analytic
singularities, unconditionally. -/
theorem hasAnalyticSingularitiesSmoothOffPoleAt_eregularizedMax {δ : ℝ} (hδ : 0 < δ)
    {u v : ComplexModel n → EReal} {z : ComplexModel n} {c : ℝ} {k l : ℕ}
    {f : Fin k → ComplexModel n → ℂ} {g : Fin l → ComplexModel n → ℂ}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c f z)
    (hv : BoundedSmoothOffPoleLogarithmicTypeAt v c g z) :
    HasAnalyticSingularitiesSmoothOffPoleAt
      (fun y => eregularizedMax δ (u y) (v y)) z :=
  ⟨c, k + l, Fin.append f g,
    boundedSmoothOffPoleLogarithmicTypeAt_eregularizedMax_append hδ hu hv⟩

end Model

end

end Hironaka.RegularizedMaxOffPoleAppend
