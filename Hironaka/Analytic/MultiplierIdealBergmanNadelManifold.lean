import Hironaka.Analytic.MultiplierIdealBergmanNadelCoherence
import Hironaka.Analytic.QuantitativeRegularizationChartGermTransfer
import Hironaka.Analytic.HolomorphicBoundedQuotient
import Hironaka.Analytic.PotentialTheory.MultiplierIdeals
import Hironaka.Analytic.HolomorphicAnalytic

set_option autoImplicit false

/-!
# Nadel's coherence theorem on a complex manifold

`isCoherent_multiplierIdeal`: for a `θ`-plurisubharmonic `φ` on a complex manifold of positive
dimension and `c > 0`, the multiplier ideal sheaf `𝓘(cφ)`
(`Hironaka.HolomorphicIdealSheaves.multiplierIdeal`, read in the preferred chart at each point)
is coherent in the sense of `GermIdeal.IsCoherent`: near every point it is generated, at every
nearby stalk, by finitely many holomorphic functions.  This is Nadel's coherence theorem
(Demailly, *Analytic methods in algebraic geometry*, Prop. 5.7), the input that
TN-CLASSICAL's Step-5 assembly carries as the hypothesis `hBcoh`
(`AmbientStepFiveDataAssembly.exists_ambientStepFiveData`, `IdealComparisonResidual`) and that
clause (i) of Demailly 1992 needs for the ideal `𝓘(2^k ψ)`.

Proof: in the preferred chart `e` at `x`, `Ψ = φ ∘ e⁻¹ + ρ` is psh on the domain `W` of a smooth
local potential `ρ` of `θ`; `MultiplierIdealBergmanNadelCoherence.exists_local_generators`
gives generators `g_l` on a ball `B(e x, r) ⊆ W`; the generators on the manifold are `g_l ∘ e`.
Membership of a germ in `𝓘(cφ)_y` is read in `e` against `Ψ` by
`QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_corrected_of_mem_multiplierIdeal`;
conversely a combination `∑ a_i (g_{l_i} ∘ e)` is `L²` against `Ψ` (closure of `𝓘` under sums
and holomorphic multiples), hence against `φ ∘ e⁻¹` (`ρ` is bounded above near the point), hence
in the preferred chart at `y` (`ChartWeightedL2.multiplierIntegrableAt_chart`).
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold

namespace Hironaka.MultiplierIdealBergmanNadelManifold

noncomputable section

open Hironaka.HolomorphicIdealSheaves MultiplierIdealBergmanNadelIdeal
  MultiplierIdealBergmanNadelCoherence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Holomorphy through a chart -/

/-- A function holomorphic near `y` is holomorphic near `e y` in the coordinates of a chart
`e = chartAt x` containing `y`. -/
theorem eventually_differentiableAt_comp_chart_symm {f : M → ℂ} {x y : M}
    (hy : y ∈ (chartAt (ComplexModel n) x).source) (hf : HolomorphicAt n f y) :
    ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) x y),
      DifferentiableAt ℂ (fun z => f ((chartAt (ComplexModel n) x).symm z)) z := by
  set e := chartAt (ComplexModel n) x
  have hT : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at this
    exact this
  filter_upwards [e.open_target.mem_nhds (e.map_source hy), hT.eventually hf] with z hz hfz
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact hfz.comp z (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hz)

/-- A function holomorphic near `e y` in the coordinates of `e = chartAt x`, composed with `e`,
is holomorphic near `y`. -/
theorem holomorphicAt_comp_chart {W : ComplexModel n → ℂ} {x y : M}
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hW : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) x y), DifferentiableAt ℂ W z) :
    HolomorphicAt n (fun p => W (chartAt (ComplexModel n) x p)) y := by
  set e := chartAt (ComplexModel n) x
  filter_upwards [e.open_source.mem_nhds hy, (e.continuousAt hy).eventually hW] with p hp hWp
  have hWm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) W (e p) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hWp
  exact hWm.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp)

/-! ### Finite sums of holomorphic multiples stay in the multiplier ideal -/

/-- A finite sum of holomorphic multiples of germs `L²` for a quasi-psh weight is `L²`. -/
theorem multiplierIntegrableAt_sum_mul {d : ℕ} {Ψ : ComplexModel d → EReal} {c : ℝ} (hc : 0 < c)
    {z : ComplexModel d} (hΨ : QuasiPlurisubharmonicAt Ψ z) {N : ℕ}
    {a s : Fin N → ComplexModel d → ℂ} (ha : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (a i) w)
    (hs : ∀ i, MultiplierIntegrableAt Ψ c (s i) z volume) :
    MultiplierIntegrableAt Ψ c (fun w => ∑ i, a i w * s i w) z volume := by
  have hanalytic : ∀ i, AnalyticAt ℂ (a i) z := fun i => by
    obtain ⟨U, hU, hUo, hzU⟩ := _root_.eventually_nhds_iff.mp (ha i)
    exact HolomorphicAnalytic.analyticAt_of_differentiableOn hUo
      (fun w hw => (hU w hw).differentiableWithinAt) hzU
  have key : ∀ T : Finset (Fin N),
      MultiplierIntegrableAt Ψ c (fun w => ∑ i ∈ T, a i w * s i w) z volume := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simpa using multiplierIntegrableAt_zero Ψ hc z volume
    | insert i T hi ih =>
      have h1 := multiplierIntegrableAt_holomorphic_mul hΨ (hs i) (hanalytic i)
      have h2 := multiplierIntegrableAt_add hΨ h1 ih
      simpa [Finset.sum_insert hi] using h2
  simpa using key Finset.univ

/-! ### Coherence -/

/-- **Nadel's coherence theorem.**  For `φ` `θ`-plurisubharmonic on a complex manifold of
dimension `m + 1` and `c > 0`, the multiplier ideal sheaf `𝓘(cφ)` is coherent. -/
theorem isCoherent_multiplierIdeal {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : SmoothRealForm (m + 1) M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    {c : ℝ} (hc : 0 < c) : (multiplierIdeal (n := m + 1) c φ).IsCoherent := by
  classical
  intro x
  set e : ComplexChart (m + 1) M := complexChartAt (n := m + 1) x with hedef
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hxW, hρ, hpsh⟩ := hφ e (e.val x) (e.val.map_source hxe)
  set Ψ : ComplexModel (m + 1) → EReal := fun w => chartFunction φ e w + (ρ w : EReal) with hΨ
  let Ω : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨W, hρ.1⟩
  obtain ⟨r, hr, N, g, hballΩ, hgd, hgint, hgen⟩ :=
    exists_local_generators (Ω := Ω) (Ψ := Ψ) hpsh hc hxW
  have hballW : ball (e.val x) r ⊆ W := hballΩ
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) r, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hxe, mem_ball_self hr⟩, N, fun l p => g l (e.val p), fun l p hp => ?_, fun y hy h => ?_⟩
  · -- the generators are holomorphic
    have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (g l) (e.val p) := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hgd l).differentiableAt (isOpen_ball.mem_nhds hp.2)
    exact (hd.comp p (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hp.1)).mdifferentiableWithinAt
  have hyW : e.val y ∈ W := hballW hy.2
  have hρc : ContinuousOn ρ W := hρ.2.2.1.continuousOn
  constructor
  · -- `𝓘(cφ)_y ⊆` the span of the generators
    intro hmem
    have hΨy : MultiplierIntegrableAt Ψ c (fun w => h (e.val.symm w)) (e.val y) volume :=
      QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_corrected_of_mem_multiplierIdeal
        hφ e hρ.1 hρc hpsh hc hy.1 hyW hmem
    obtain ⟨N', s', a, hs', ha, he⟩ := hgen (e.val y) hy.2 _ hΨy
    choose l hl using hs'
    refine ⟨hmem.1, N', fun i p => s' i (e.val p), fun i p => a i (e.val p),
      fun i => ⟨l i, ?_⟩, fun i => holomorphicAt_comp_chart hy.1 (ha i), ?_⟩
    · funext p
      simp only [hl i]
    · filter_upwards [e.val.open_source.mem_nhds hy.1, (e.val.continuousAt hy.1).eventually he]
        with p hp hpe
      simp only [e.val.left_inv hp] at hpe
      exact hpe
  · -- the span of the generators `⊆ 𝓘(cφ)_y`
    rintro ⟨hhol, N', s'', a'', hs'', ha'', he''⟩
    refine ⟨hhol, ?_⟩
    choose l hl using hs''
    have hqpsh : QuasiPlurisubharmonicAt Ψ (e.val y) :=
      (hpsh (e.val y) hyW).quasiPlurisubharmonicAt
    -- integrability against `Ψ` in the chart `e`
    have hsum : MultiplierIntegrableAt Ψ c
        (fun w => ∑ i, a'' i (e.val.symm w) * g (l i) w) (e.val y) volume :=
      multiplierIntegrableAt_sum_mul hc hqpsh
        (fun i => eventually_differentiableAt_comp_chart_symm hy.1 (ha'' i))
        (fun i => hgint (l i) (e.val y) hy.2)
    have hT : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
      have := e.val.continuousAt_symm (e.val.map_source hy.1)
      rw [ContinuousAt, e.val.left_inv hy.1] at this
      exact this
    have heq : (fun w => ∑ i, a'' i (e.val.symm w) * g (l i) w) =ᶠ[𝓝 (e.val y)]
        fun w => h (e.val.symm w) := by
      filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hy.1), hT.eventually he'']
        with w hw hwe
      rw [hwe]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hl i]
      simp only [e.val.right_inv hw]
    have hΨh : MultiplierIntegrableAt Ψ c (fun w => h (e.val.symm w)) (e.val y) volume :=
      hsum.congr (EventuallyEq.refl _ _) heq
    -- from `Ψ` to `φ ∘ e⁻¹`
    have hmore : MoreSingularAt Ψ (chartFunction φ e) (e.val y) := by
      have hcont : ContinuousAt ρ (e.val y) := (hρc _ hyW).continuousAt (hρ.1.mem_nhds hyW)
      refine ⟨ρ (e.val y) + 1, ?_⟩
      filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one (ρ (e.val y))))] with w hw
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hw.le)
    have hqu : QuasiPlurisubharmonicAt (chartFunction φ e) (e.val y) :=
      hφ.quasiPlurisubharmonic e (e.val y) (e.val.map_source hy.1)
    have hφh : MultiplierIntegrableAt (chartFunction φ e) c (fun w => h (e.val.symm w))
        (e.val y) volume :=
      multiplierIntegrableAt_of_moreSingularAt hqu hmore hΨh
    -- to the preferred chart at `y`
    have husc : UpperSemicontinuousOn (chartFunction φ (complexChartAt (n := m + 1) y))
        (ChartWeightedL2.overlapDomain (complexChartAt (n := m + 1) y) e) :=
      (hφ.quasiPlurisubharmonic (complexChartAt (n := m + 1) y)).upperSemicontinuousOn.mono
        fun _ hw => hw.1
    exact ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := h)
      (complexChartAt (n := m + 1) y) e (mem_complexChartAt_source y) hy.1 husc hc.ne' hφh


/-- **Nadel's coherence theorem**, in any positive dimension `n`. -/
theorem isCoherent_multiplierIdeal_of_pos {n : ℕ} (hn : 0 < n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    {c : ℝ} (hc : 0 < c) : (multiplierIdeal (n := n) c φ).IsCoherent := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact isCoherent_multiplierIdeal hφ hc

end

end Hironaka.MultiplierIdealBergmanNadelManifold
