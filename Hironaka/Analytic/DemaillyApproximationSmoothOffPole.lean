import Hironaka.Analytic.DemaillyApproximationAnalyticType
import Hironaka.Analytic.BergmanKernelSmooth

set_option autoImplicit false

/-!
# Demailly's approximants are smooth off their poles (clause (i), chartwise form)

Clause (i) of Demailly 1992 (`bou02-volume:2.6`) in the `I-0489` convention
`HasManifoldAnalyticSingularitiesSmoothOffPole`: in every chart the approximant
`ψ_k = DemaillyApproximationSequence.seq F ρ ψ E k` is `c log ∑|f_i|² + b` with `b` bounded near
the point and `C^∞` off the common zeros of the `f_i`.

* The bounded-remainder presentation in every chart is the global one of
  `DemaillyApproximationAnalyticType.hasAnalyticSingularities_seq`, read in the chart.
* Off the poles `ψ_k` is a smooth real germ (`exists_smoothGerm_seq`): near a point `p` with
  `ψ_k(p) ≠ -∞` the glued function is `M_δ` of the branches active at `p`
  (`DemaillySymmetricGluing.exists_nhds_rglue_eq`); by the overlap comparison
  `b_j ≤ b_l + C_B/m` either all active branches are `-∞` at `p` or none is, so all are finite;
  each is `m⁻¹ log K_j ∘ e_j - ρ_j ∘ e_j` with the Bergman kernel `K_j` positive and `C^∞`
  (step B3, `BergmanKernelSmooth.contDiffOn_toReal_bergmanSup`), and `M_δ` is `C^∞`.
* `boundedSmoothOffPole_of_smoothGerm`: the remainder of a bounded presentation of such a
  function is smooth off the zeros of the generators (it is the smooth germ minus the smooth
  `c log ∑|f_i|²`).

`exists_algebraicApproximation` is the full statement of
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`, on every
compact Kähler manifold (dimension `0` included, no connectedness).

Programme `TN.3.3.DEMPROVE`, clause (i-c) and the final assembly.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.DemaillyApproximationSmoothOffPole

noncomputable section

open Hironaka.PositiveClasses Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.GlobalAnalyticSingularities
  BergmanSupWeight QuantitativeRegularizationChartBranch QuantitativeRegularizationFixedCover
  QuantitativeRegularizationMaxGluing DemaillySymmetricGluing DemaillySymmetricGluingLimit
  DemaillyApproximationSequence DemaillyApproximationAnalyticType
  SymmetricRegularizedMax SymmetricRegularizedMaxPsh

/-! ### Upgrading a bounded presentation -/

section Upgrade

variable {n : ℕ}

/-- **A bounded-remainder presentation of a function which is a smooth real germ at each of its
finite points is an `I-0489` presentation**: off the zeros of the generators the presented
function is finite, and the remainder is the smooth germ minus `c log ∑|f_i|²`. -/
theorem boundedSmoothOffPole_of_smoothGerm {u : ComplexModel n → EReal} {c : ℝ} {k : ℕ}
    {f : Fin k → ComplexModel n → ℂ} {z : ComplexModel n}
    (hL : LogarithmicTypeAt u c f z)
    (hu : ∀ᶠ y in 𝓝 z, u y ≠ ⊥ → ∃ g : ComplexModel n → ℝ,
      (∀ᶠ v in 𝓝 y, ContDiffAt ℝ ∞ g v) ∧ u =ᶠ[𝓝 y] fun v => (g v : EReal)) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c f z := by
  obtain ⟨hc, hfhol, b, hb, heq⟩ := hL
  obtain ⟨U, hUopen, hzU, hf⟩ := hfhol
  have hsq : ContDiffOn ℝ ∞ (generatorNormSq f) U := by
    unfold generatorNormSq
    refine ContDiffOn.sum fun j _ => ?_
    exact (contDiff_norm_sq ℝ).comp_contDiffOn
      (contDiffOn_real_of_differentiableOn_complex (hf j) hUopen)
  refine ⟨hc, ⟨U, hUopen, hzU, hf⟩, b, hb, ?_, heq⟩
  have heq' : ∀ᶠ y in 𝓝 z,
      u =ᶠ[𝓝 y] fun w => (c : EReal) * generatorLog f w + (b w : EReal) :=
    eventually_eventually_nhds.mpr heq
  filter_upwards [hu, heq', hUopen.mem_nhds hzU] with y hy hyeq hyU
  intro hne
  have hpos : 0 < generatorNormSq f y :=
    lt_of_le_of_ne (generatorNormSq_nonneg f y) (Ne.symm hne)
  have hlog : ∀ w, 0 < generatorNormSq f w →
      generatorLog f w = (Real.log (generatorNormSq f w) : EReal) := fun w hw => by
    rw [generatorLog, logNormSq, generatorVector_norm_sq, ENNReal.log_ofReal_of_pos hw]
  have hufin : u y ≠ ⊥ := by
    rw [hyeq.eq_of_nhds, hlog y hpos, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  obtain ⟨g, hg, hug⟩ := hy hufin
  have hposNear : ∀ᶠ w in 𝓝 y, 0 < generatorNormSq f w :=
    (hsq.continuousOn.continuousAt (hUopen.mem_nhds hyU)).eventually (lt_mem_nhds hpos)
  have hbeq : b =ᶠ[𝓝 y] fun w => g w - c * Real.log (generatorNormSq f w) := by
    filter_upwards [hyeq, hug, hposNear] with w hw hwg hwp
    have hcoe : ((g w : ℝ) : EReal)
        = ((c * Real.log (generatorNormSq f w) + b w : ℝ) : EReal) := by
      rw [← hwg, hw, hlog w hwp, ← EReal.coe_mul, ← EReal.coe_add]
    have hreal := EReal.coe_eq_coe_iff.mp hcoe
    linarith [hreal]
  have hlogsm : ContDiffAt ℝ ∞ (fun w => c * Real.log (generatorNormSq f w)) y :=
    contDiffAt_const.mul ((hsq.contDiffAt (hUopen.mem_nhds hyU)).log hpos.ne')
  exact (hg.self_of_nhds.sub hlogsm).congr_of_eventuallyEq hbeq

end Upgrade

/-! ### The Bergman weights of the fixed cover -/

section Branch

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- The weight `e^{-m(φ ∘ e_j⁻¹ + ρ_j)}` of the `j`-th Bergman ball satisfies the hypotheses of
`BergmanKernelSmooth`. -/
theorem bergmanWeight_branch (F : FixedChartCover d Z) {ζ : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {m : ℕ} (hm : 0 < m) (j : F.t) :
    BergmanKernelSmooth.BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpsh := F.plurisubharmonicOn_correctedWeight hρ hφ j
  have hBP : ball (F.center j) (F.bergmanRadius j) ⊆ ball (F.center j) (F.potentialRadius j) :=
    ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  refine ⟨isOpen_ball, ?_, fun z hz => ?_⟩
  · exact DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      (hpsh.upperSemicontinuousOn.mono hBP) hmR.ne'
  · obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
    have hcb : closedBall z (ε / 2) ⊆ ball (F.center j) (F.bergmanRadius j) :=
      (closedBall_subset_ball (by linarith)).trans hεB
    obtain ⟨Cu, -, hCu⟩ := hpsh.exists_nonnegative_compact_upper_bound
      (isCompact_closedBall z (ε / 2)) (hcb.trans hBP)
    refine ⟨Real.exp (-((m : ℝ) * Cu)), Real.exp_pos _, ε / 2, by positivity, hcb,
      fun x hx => ?_⟩
    rw [← multiplierWeight_coe]
    exact multiplierWeight_antitone hmR.le (hCu x hx)

/-- On the patch, a branch whose Bergman kernel is positive and finite is the real number
`m⁻¹ log K_j(e_j x) - ρ_j(e_j x)`. -/
theorem branch_eq_coe (F : FixedChartCover d Z) {ρ : F.t → ComplexModel d → ℝ} {φ : Z → EReal}
    {m : ℕ} {j : F.t} {x : Z}
    (hx : x ∈ chartPatch (F.chart j) (ball (F.center j) (F.bergmanRadius j)))
    (h0 : bergmanSup (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z))
        ((F.chart j).val x) ≠ 0)
    (htop : bergmanSup (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z))
        ((F.chart j).val x) ≠ ⊤) :
    F.branch ρ φ m j x = ((((m : ℝ)⁻¹ * Real.log (bergmanSup (ball (F.center j)
      (F.bergmanRadius j)) (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z))
        ((F.chart j).val x)).toReal - ρ j ((F.chart j).val x) : ℝ)) : EReal) := by
  rw [F.branch_of_mem hx, bergmanLog]
  set K := bergmanSup (ball (F.center j) (F.bergmanRadius j))
    (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z)) ((F.chart j).val x)
  have hKpos : 0 < K.toReal := ENNReal.toReal_pos h0 htop
  have hlog : ENNReal.log K = (Real.log K.toReal : EReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.log_ofReal_of_pos hKpos
  rw [hlog, ← EReal.coe_mul, ← EReal.coe_sub]

/-- If a branch is finite at a point of its patch, its Bergman kernel is positive there. -/
theorem bergmanSup_ne_zero_of_branch_ne_bot (F : FixedChartCover d Z)
    {ρ : F.t → ComplexModel d → ℝ} {φ : Z → EReal} {m : ℕ} (hm : 0 < m) {j : F.t} {x : Z}
    (hx : x ∈ chartPatch (F.chart j) (ball (F.center j) (F.bergmanRadius j)))
    (hb : F.branch ρ φ m j x ≠ ⊥) :
    bergmanSup (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z))
        ((F.chart j).val x) ≠ 0 := by
  intro h0
  apply hb
  have hmR : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hm)
  rw [F.branch_of_mem hx, bergmanLog, h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hmR,
    EReal.bot_sub]

end Branch

/-! ### Off its poles, Demailly's approximant is a smooth real germ in every chart -/

section Seq

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **Smoothness off the poles.**  In every chart, near a point where `ψ_k` is finite, the
coordinate representative of `ψ_k` is a `C^∞` real function. -/
theorem exists_smoothGerm_seq (F : FixedChartCover d Z) {α : ClosedRealOneOneForm d Z}
    {ψ : Z → EReal} (hψ : IsThetaPshPotential α.val ψ) {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α.val (F.chart j) (ball (F.center j) (F.potentialRadius j))
      (ρ j)) (E : ℝ) (k : ℕ) (e : ComplexChart d Z) {y : ComplexModel d}
    (hy : y ∈ e.val.target) (hfin : seq F ρ ψ E k (e.val.symm y) ≠ ⊥) :
    ∃ g : ComplexModel d → ℝ, (∀ᶠ v in 𝓝 y, ContDiffAt ℝ ∞ g v) ∧
      chartFunction (seq F ρ ψ E k) e =ᶠ[𝓝 y] fun v => (g v : EReal) := by
  classical
  set m : ℕ := 2 ^ k with hmdef
  have hm : 0 < m := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := 1 / (2 * (m : ℝ)) with hδdef
  set A : ℝ := (F.CB + 1) / (m : ℝ) with hAdef
  set b : F.t → Z → EReal := F.branch ρ ψ m with hbdef
  set p : Z := e.val.symm y with hpdef
  set c₀ : ℝ := E * ((2 : ℝ) ^ k)⁻¹ with hc₀
  have hseq : ∀ q, seq F ρ ψ E k q = rglue F.cover δ b A q + (c₀ : EReal) := fun q => rfl
  -- the glue is locally `M_δ` of the branches active at `p`
  have hA : F.CB / (m : ℝ) + δ ≤ A := by
    rw [hδdef, hAdef, div_add_div _ _ hmR.ne' (by positivity), div_le_div_iff₀ (by positivity)
      hmR]
    nlinarith [F.CB_nonneg]
  have hcomp : ∀ j l, ∀ q ∈ F.cover.V j ∩ F.cover.V l, b j q ≤ b l q + ((F.CB / (m : ℝ) : ℝ) :
      EReal) := fun j l q hq => F.branch_le_branch_add hρ hψ.1 hm j l hq
  obtain ⟨N, hNo, hpN, hNV, hNeq⟩ := exists_nhds_rglue_eq F.cover b hA hcomp p
  set S : Finset F.t := activeSet F.cover p with hSdef
  -- every active branch is finite at `p`
  have hfinj : ∀ j ∈ S, b j p ≠ ⊥ := by
    intro j hj hbj
    apply hfin
    have hall : ∀ l ∈ S, F.cover.branch b A l p = ⊥ := by
      intro l hl
      have hlj := hcomp l j p ⟨(mem_activeSet F.cover).mp hl, (mem_activeSet F.cover).mp hj⟩
      rw [hbj, EReal.bot_add, le_bot_iff] at hlj
      simp only [CutoffCover.branch, hlj, EReal.bot_add]
    rw [hseq, rglue, ermax_of_bot hall, EReal.bot_add]
  -- the data of an active branch
  have hW : ∀ j, BergmanKernelSmooth.BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) ψ z)) :=
    fun j => bergmanWeight_branch F hρ hψ.1 hm j
  set K : F.t → ComplexModel d → ℝ := fun j u => (bergmanSup (ball (F.center j)
    (F.bergmanRadius j)) (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) ψ z))
      u).toReal with hKdef
  have hKsmooth : ∀ j, ContDiffOn ℝ ∞ (K j) (ball (F.center j) (F.bergmanRadius j)) := fun j =>
    BergmanKernelSmooth.contDiffOn_toReal_bergmanSup (hW j)
  set T : F.t → OpenPartialHomeomorph (ComplexModel d) (ComplexModel d) :=
    fun j => chartTransition e (F.chart j) with hTdef
  have hTapp : ∀ j v, T j v = (F.chart j).val (e.val.symm v) := fun j v => rfl
  have hTsrc : ∀ j v, v ∈ (T j).source ↔ v ∈ e.val.target ∧ e.val.symm v ∈ (F.chart j).val.source :=
    fun j v => by
      change v ∈ (e.val.symm.trans (F.chart j).val).source ↔ _
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      rfl
  set β : F.t → ComplexModel d → ℝ := fun j v =>
    (m : ℝ)⁻¹ * Real.log (K j (T j v)) - ρ j (T j v) + A * F.cover.χ j (e.val.symm v) with hβdef
  -- the good set of `j`, a neighbourhood of `y` for active `j`
  set G : F.t → Set (ComplexModel d) := fun j =>
    {v | v ∈ (T j).source ∧ T j v ∈ ball (F.center j) (F.bergmanRadius j) ∧ 0 < K j (T j v)}
    with hGdef
  have hβsmooth : ∀ j, ∀ v ∈ G j, ContDiffAt ℝ ∞ (β j) v := by
    intro j v hv
    obtain ⟨hvT, hvB, hvK⟩ := hv
    have hTc : ContDiffAt ℝ ∞ (T j) v :=
      HolomorphicMaps.chartTransition_contDiffAt_real e (F.chart j) hvT
    have hBP : ball (F.center j) (F.bergmanRadius j) ⊆ ball (F.center j) (F.potentialRadius j) :=
      ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
    have hK : ContDiffAt ℝ ∞ (fun v => K j (T j v)) v :=
      ((hKsmooth j).contDiffAt (isOpen_ball.mem_nhds hvB)).comp v hTc
    have hρc : ContDiffAt ℝ ∞ (fun v => ρ j (T j v)) v :=
      (((hρ j).2.2.1).contDiffAt (isOpen_ball.mem_nhds (hBP hvB))).comp v hTc
    have hχ : ContDiffAt ℝ ∞ (fun v => F.cover.χ j (e.val.symm v)) v :=
      (F.cover.χ_smooth j e).contDiffAt (e.val.open_target.mem_nhds ((hTsrc j v).mp hvT).1)
    exact ((contDiffAt_const.mul (hK.log hvK.ne')).sub hρc).add (contDiffAt_const.mul hχ)
  have hGnhds : ∀ j ∈ S, G j ∈ 𝓝 y := by
    intro j hj
    have hpV : p ∈ F.cover.V j := (mem_activeSet F.cover).mp hj
    have hpP := F.V_subset_chartPatch j hpV
    have hyT : y ∈ (T j).source := (hTsrc j y).mpr ⟨hy, hpP.1⟩
    have hTy : T j y ∈ ball (F.center j) (F.bergmanRadius j) := hpP.2
    have h0 := bergmanSup_ne_zero_of_branch_ne_bot F hm hpP (hfinj j hj)
    have hKy : 0 < K j (T j y) :=
      ENNReal.toReal_pos h0 (BergmanKernelSmooth.bergmanSup_ne_top (hW j) hTy)
    have hTcont : ContinuousAt (T j) y := (T j).continuousAt hyT
    have hKcont : ContinuousAt (fun v => K j (T j v)) y :=
      ((hKsmooth j).continuousOn.continuousAt (isOpen_ball.mem_nhds hTy)).comp hTcont
    filter_upwards [(T j).open_source.mem_nhds hyT, hTcont.eventually (isOpen_ball.mem_nhds hTy),
      hKcont.eventually (lt_mem_nhds hKy)] with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hGall : ∀ᶠ v in 𝓝 y, ∀ j ∈ S, v ∈ G j := by
    rw [eventually_all_finset]
    exact hGnhds
  -- the smooth germ
  set g : ComplexModel d → ℝ := fun v =>
    rmax δ S (fun j => if j ∈ S then β j v else 0) + c₀ with hgdef
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [hGall] with v hv
    refine ContDiffAt.add ?_ contDiffAt_const
    refine ((contDiff_rmax δ S).contDiffAt).comp v (contDiffAt_pi.mpr fun j => ?_)
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using hβsmooth j v (hv j hj)
    · simpa only [if_neg hj] using contDiffAt_const
  · have hsymm : ∀ᶠ v in 𝓝 y, e.val.symm v ∈ N :=
      (e.val.continuousAt_symm hy).eventually (hNo.mem_nhds hpN)
    filter_upwards [hGall, hsymm] with v hv hvN
    have hentry : ∀ j ∈ S, F.cover.branch b A j (e.val.symm v) = (β j v : EReal) := by
      intro j hj
      obtain ⟨hvT, hvB, hvK⟩ := hv j hj
      have hq : e.val.symm v ∈ chartPatch (F.chart j) (ball (F.center j) (F.bergmanRadius j)) :=
        F.V_subset_chartPatch j (hNV j ((mem_activeSet F.cover).mp hj) hvN)
      have hK0 : bergmanSup (ball (F.center j) (F.bergmanRadius j))
          (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) ψ z))
            ((F.chart j).val (e.val.symm v)) ≠ 0 := by
        intro h
        rw [hKdef] at hvK
        simp only [hTapp, h, ENNReal.toReal_zero, lt_irrefl] at hvK
      rw [CutoffCover.branch, hbdef, branch_eq_coe F hq hK0
        (BergmanKernelSmooth.bergmanSup_ne_top (hW j) hq.2), ← EReal.coe_add]
      rfl
    have htop : ∀ j ∈ S, F.cover.branch b A j (e.val.symm v) ≠ ⊤ := fun j hj => by
      rw [hentry j hj]
      exact EReal.coe_ne_top _
    have hfp : finitePart S (fun j => F.cover.branch b A j (e.val.symm v)) = S := by
      ext j
      rw [mem_finitePart]
      constructor
      · exact fun h => h.1
      · intro hj
        refine ⟨hj, ?_⟩
        rw [hentry j hj]
        exact EReal.coe_ne_bot _
    have hne : (finitePart S fun j => F.cover.branch b A j (e.val.symm v)).Nonempty := by
      rw [hfp]
      exact activeSet_nonempty F.cover p
    change seq F ρ ψ E k (e.val.symm v) = _
    rw [hseq, hNeq _ hvN, ermax_of_finite htop hne, hfp, hgdef, ← EReal.coe_add]
    congr 2
    refine rmax_congr fun j hj => ?_
    rw [hentry j hj, EReal.toReal_coe, if_pos hj]

/-- **Clause (i), chartwise form (`I-0489`): Demailly's approximants have analytic singularities
with a remainder bounded and `C^∞` off the poles**, in every chart. -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_seq (hd : 0 < d) (F : FixedChartCover d Z)
    {α : ClosedRealOneOneForm d Z} {ψ : Z → EReal} (hψ : IsThetaPshPotential α.val ψ)
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α.val (F.chart j) (ball (F.center j) (F.potentialRadius j))
      (ρ j)) (E : ℝ) (k : ℕ) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := d) (seq F ρ ψ E k) := by
  intro e z hz
  obtain ⟨c, 𝔞, hc, -, hloc⟩ := hasAnalyticSingularities_seq hd F hψ hρ E k
  obtain ⟨U, hUo, hxU, N, g, hgd, -, R, C, hR, heq⟩ := hloc (e.val.symm z)
  set U' : Set (ComplexModel d) := e.val.target ∩ e.val.symm ⁻¹' U with hU'def
  have hU'o : IsOpen U' := e.val.isOpen_inter_preimage_symm hUo
  have hzU' : z ∈ U' := ⟨hz, hxU⟩
  have hhol : ∀ i, DifferentiableOn ℂ (fun v => g i (e.val.symm v)) U' := by
    intro i v hv
    refine DifferentiableAt.differentiableWithinAt ?_
    exact mdifferentiableAt_iff_differentiableAt.mp
      (((hgd i).mdifferentiableAt (hUo.mem_nhds hv.2)).comp v
        (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel d)) e.property hv.1))
  have hL : LogarithmicTypeAt (chartFunction (seq F ρ ψ E k) e) (c : ℝ)
      (fun i v => g i (e.val.symm v)) z := by
    refine ⟨by exact_mod_cast hc, ⟨U', hU'o, hzU', hhol⟩, fun v => R (e.val.symm v),
      ⟨C, (abs_nonneg _).trans (hR _ hxU), ?_⟩, ?_⟩
    · filter_upwards [hU'o.mem_nhds hzU'] with v hv
      exact hR _ hv.2
    · filter_upwards [hU'o.mem_nhds hzU'] with v hv
      exact heq _ hv.2
  refine ⟨(c : ℝ), N, fun i v => g i (e.val.symm v), boundedSmoothOffPole_of_smoothGerm hL ?_⟩
  filter_upwards [e.val.open_target.mem_nhds hz] with v hv hne
  exact exists_smoothGerm_seq F hψ hρ E k e hv hne

end Seq

/-! ### Dimension `0` and the full statement -/

section Global

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- In dimension `0` a theta-PSH potential is, in every chart, `log |1|² + b` with `b` constant
(the potential is finite at every point). -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_of_dim_zero {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    {θ : SmoothRealForm 0 Y 2} {ψ : Y → EReal} (hψ : IsThetaPshPotential θ ψ) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := 0) ψ := by
  intro e z hz
  set x : Y := e.val.symm z with hxdef
  have hbot : ψ x ≠ ⊥ := by
    obtain ⟨y, hy, hyψ⟩ := hψ.2 x {x} (isOpen_singleton_of_dim_zero x) rfl
    rwa [mem_singleton_iff.mp hy] at hyψ
  have htop : ψ x ≠ ⊤ :=
    ManifoldQuasiPlurisubharmonic.ne_top (fun e => hψ.1.quasiPlurisubharmonic e) x
  let one : Fin 1 → ComplexModel 0 → ℂ := fun _ _ => 1
  have hsub : ∀ v w : ComplexModel 0, v = w := fun v w => by
    ext i
    exact i.elim0
  have hlog : ∀ v, generatorLog one v = 0 := fun v => by
    rw [generatorLog_eq_log_sum]
    simp [one]
  refine ⟨1, 1, one, one_pos, ⟨univ, isOpen_univ, mem_univ _, fun _ => differentiableOn_const 1⟩,
    fun _ => (ψ x).toReal, boundedRealGermAt_of_continuousAt continuousAt_const,
    Eventually.of_forall fun _ _ => contDiffAt_const, Eventually.of_forall fun v => ?_⟩
  rw [hsub v z]
  show ψ x = ((1 : ℝ) : EReal) * generatorLog one z + ((ψ x).toReal : EReal)
  rw [hlog z, mul_zero, zero_add]
  exact (EReal.coe_toReal htop hbot).symm

open Hironaka.PositiveClasses in
/-- **Demailly 1992 (`bou02-volume:2.6`, `γ = 0`), the full statement of
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation`**, on every
compact Kähler manifold (no connectedness, dimension `0` included): the explicit sequence
`seq F ρ ψ (2(D + 1/4)) k` has analytic singularities of type `(2^{-k}, 𝓘(2^k ψ))` and is smooth
off its poles in every chart, decreases to `ψ` everywhere, and is `(α + δ_k ω)`-PSH with
`δ_k = (C_B + 1) C_χ / 2^k`. -/
theorem exists_algebraicApproximation [CompactSpace Z] (omega : KahlerBackground d Z)
    (α : ClosedRealOneOneForm d Z) (ψ : Z → EReal) (hψ : IsThetaPshPotential α.val ψ) :
    ∃ (psiSeq : ℕ → Z → EReal) (delta : ℕ → ℝ),
      (∀ k, HasAnalyticSingularities (n := d) (psiSeq k)) ∧
      (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := d) (psiSeq k)) ∧
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = ψ x) ∧
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (α + delta k • omega.form).val (psiSeq k) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun _ => ψ, fun _ => 0, fun _ => hasAnalyticSingularities_of_dim_zero hψ,
      fun _ => hasManifoldAnalyticSingularitiesSmoothOffPole_of_dim_zero hψ,
      fun x => antitone_const, fun x => iInf_const, fun _ => le_rfl, tendsto_const_nhds,
      fun k => ?_⟩
    simpa only [zero_smul, add_zero] using hψ
  · obtain ⟨F⟩ := exists_fixedChartCover (Z := Z) hd
    obtain ⟨ρ, hρ⟩ := F.exists_potentials α
    obtain ⟨D, -, hD⟩ := exists_doublingConst F
    have hdouble := hD α.val ψ hψ.1 ρ hρ
    obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
      (fun j => ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j))
    refine ⟨seq F ρ ψ (2 * (D + 1 / 4)), fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ,
      fun k => hasAnalyticSingularities_seq hd F hψ hρ _ k,
      fun k => hasManifoldAnalyticSingularitiesSmoothOffPole_seq hd F hψ hρ _ k,
      fun x => antitone_seq F hdouble x, fun x => iInf_seq F hψ.1 hρ hdouble x, fun k => ?_, ?_,
      fun k => isThetaPshPotential_seq hd F omega hsemi hψ hρ _ k⟩
    · have := F.CB_nonneg
      positivity
    · have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      have h2 := h1.const_mul ((F.CB + 1) * Cχ)
      rw [mul_zero] at h2
      refine h2.congr fun k => ?_
      push_cast
      field_simp

end Global

end

end Hironaka.DemaillyApproximationSmoothOffPole
