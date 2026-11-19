import Hironaka.Analytic.RiemannExtension
import Hironaka.Analytic.HolomorphicGermAlgebra

set_option autoImplicit false

/-!
# A bounded holomorphic quotient is holomorphic

Source: the Riemann extension theorem, Copy-4 `sec:fixed-data`
(`transcendental-nakamaye-copy4-20260911`); Demailly CADG II.

`Pending/RiemannExtension.exists_extension_euclidean` is the germ form of Riemann
extension at the origin of `ℂ^d`.  This module transports it to a complex
manifold and reads it as the statement the metered-divisor bridge needs: if `f`
and `g` are holomorphic near `x`, `g` vanishes identically on no nonempty open
set, and `‖f‖ ≤ C ‖g‖` near `x`, then `f = w g` near `x` for a holomorphic `w`.

The transport is through `rechart n x`, the preferred chart at `x` translated so
that `x` goes to the origin.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HolomorphicBoundedQuotient

noncomputable section

open Hironaka.HolomorphicIdealSheaves

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The preferred chart, recentred at the origin -/

variable (n) in
/-- The preferred chart at `x`, translated so that `x` goes to the origin. -/
def rechart (x : M) : M → ComplexModel n :=
  fun y => chartAt (ComplexModel n) x y - chartAt (ComplexModel n) x x

variable (n) in
/-- Its inverse. -/
def rechartSymm (x : M) : ComplexModel n → M :=
  fun z => (chartAt (ComplexModel n) x).symm (z + chartAt (ComplexModel n) x x)

theorem mdifferentiableAt_chartAt {x y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x) y :=
  ((contMDiffOn_chart (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) x).open_source.mem_nhds hy)).mdifferentiableAt (by simp)

theorem mdifferentiableAt_chartAt_symm {x : M} {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) x).target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x).symm z :=
  ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) x).open_target.mem_nhds hz)).mdifferentiableAt (by simp)

omit [IsComplexManifold n M] in
@[simp] theorem rechart_self (x : M) : rechart n x x = 0 := by simp [rechart]

omit [IsComplexManifold n M] in
@[simp] theorem rechartSymm_zero (x : M) : rechartSymm n x 0 = x := by
  simp [rechartSymm, (chartAt (ComplexModel n) x).left_inv (mem_chart_source (ComplexModel n) x)]

omit [IsComplexManifold n M] in
theorem tendsto_rechart (x : M) : Tendsto (rechart n x) (𝓝 x) (𝓝 0) := by
  have h : ContinuousAt (chartAt (ComplexModel n) x) x :=
    (chartAt (ComplexModel n) x).continuousAt (mem_chart_source (ComplexModel n) x)
  have h2 : Tendsto (fun z : ComplexModel n => z - chartAt (ComplexModel n) x x)
      (𝓝 (chartAt (ComplexModel n) x x)) (𝓝 0) := by
    simpa using (continuous_sub_right (chartAt (ComplexModel n) x x)).tendsto
      (chartAt (ComplexModel n) x x)
  exact h2.comp h

omit [IsComplexManifold n M] in
theorem tendsto_rechartSymm (x : M) : Tendsto (rechartSymm n x) (𝓝 0) (𝓝 x) := by
  have hmem : chartAt (ComplexModel n) x x ∈ (chartAt (ComplexModel n) x).target :=
    (chartAt (ComplexModel n) x).map_source (mem_chart_source (ComplexModel n) x)
  have h1 : Tendsto (fun z : ComplexModel n => z + chartAt (ComplexModel n) x x)
      (𝓝 0) (𝓝 (chartAt (ComplexModel n) x x)) := by
    simpa using (continuous_add_const (chartAt (ComplexModel n) x x)).tendsto
      (0 : ComplexModel n)
  have h2 : ContinuousAt (chartAt (ComplexModel n) x).symm (chartAt (ComplexModel n) x x) :=
    (chartAt (ComplexModel n) x).continuousAt_symm hmem
  have := h2.tendsto.comp h1
  rwa [(chartAt (ComplexModel n) x).left_inv (mem_chart_source (ComplexModel n) x)] at this

omit [IsComplexManifold n M] in
theorem eventually_rechartSymm_rechart (x : M) :
    ∀ᶠ y in 𝓝 x, rechartSymm n x (rechart n x y) = y := by
  filter_upwards [(chartAt (ComplexModel n) x).open_source.mem_nhds (mem_chart_source (ComplexModel n) x)]
    with y hy
  simp [rechartSymm, rechart, (chartAt (ComplexModel n) x).left_inv hy]

omit [IsComplexManifold n M] in
theorem eventually_add_mem_target (x : M) :
    ∀ᶠ z : ComplexModel n in 𝓝 0, z + chartAt (ComplexModel n) x x ∈
      (chartAt (ComplexModel n) x).target := by
  have hmem : chartAt (ComplexModel n) x x ∈ (chartAt (ComplexModel n) x).target :=
    (chartAt (ComplexModel n) x).map_source (mem_chart_source (ComplexModel n) x)
  have h1 : Tendsto (fun z : ComplexModel n => z + chartAt (ComplexModel n) x x)
      (𝓝 0) (𝓝 (chartAt (ComplexModel n) x x)) := by
    simpa using (continuous_add_const (chartAt (ComplexModel n) x x)).tendsto
      (0 : ComplexModel n)
  exact h1 ((chartAt (ComplexModel n) x).open_target.mem_nhds hmem)

omit [IsComplexManifold n M] in
theorem eventually_rechart_rechartSymm (x : M) :
    ∀ᶠ z : ComplexModel n in 𝓝 0, rechart n x (rechartSymm n x z) = z := by
  filter_upwards [eventually_add_mem_target x] with z hz
  simp [rechart, rechartSymm, (chartAt (ComplexModel n) x).right_inv hz]

/-! ### Transporting holomorphy through the recentred chart -/

theorem differentiableAt_comp_rechartSymm {f : M → ℂ} {x : M} (hf : HolomorphicAt n f x) :
    ∀ᶠ z : ComplexModel n in 𝓝 0, DifferentiableAt ℂ (fun z => f (rechartSymm n x z)) z := by
  filter_upwards [eventually_add_mem_target x, tendsto_rechartSymm x hf] with z hz hfz
  rw [← mdifferentiableAt_iff_differentiableAt]
  have hadd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun z : ComplexModel n => z + chartAt (ComplexModel n) x x) z := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (differentiable_id.add_const _).differentiableAt
  have hcomp : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      ((f ∘ (chartAt (ComplexModel n) x).symm) ∘
        fun z : ComplexModel n => z + chartAt (ComplexModel n) x x) z :=
    (hfz.comp (z + chartAt (ComplexModel n) x x)
      (mdifferentiableAt_chartAt_symm hz)).comp z hadd
  exact hcomp

theorem holomorphicAt_comp_rechart {W : ComplexModel n → ℂ} {x : M}
    (hW : ∀ᶠ z : ComplexModel n in 𝓝 0, DifferentiableAt ℂ W z) :
    HolomorphicAt n (fun y => W (rechart n x y)) x := by
  filter_upwards [(chartAt (ComplexModel n) x).open_source.mem_nhds (mem_chart_source (ComplexModel n) x),
    tendsto_rechart x hW] with y hy hWy
  have hsub : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun z : ComplexModel n => z - chartAt (ComplexModel n) x x)
      (chartAt (ComplexModel n) x y) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (differentiable_id.sub_const _).differentiableAt
  have hWm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) W
      ((fun z : ComplexModel n => z - chartAt (ComplexModel n) x x)
        (chartAt (ComplexModel n) x y)) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hWy
  have hcomp : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      ((W ∘ fun z : ComplexModel n => z - chartAt (ComplexModel n) x x) ∘
        (chartAt (ComplexModel n) x)) y :=
    (hWm.comp (chartAt (ComplexModel n) x y) hsub).comp y (mdifferentiableAt_chartAt hy)
  exact hcomp

/-! ### The bounded quotient -/

/-- If `g` vanishes identically on no nonempty open subset of `U` and `x ∈ U`, then
`g` does not vanish identically near `x`. -/
theorem not_eventually_eq_zero {g : M → ℂ} {x : M} {U : Set M} (hU : IsOpen U)
    (hx : x ∈ U)
    (hgne : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) :
    ¬ ∀ᶠ y in 𝓝 x, g y = 0 := by
  intro hev
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hev
  obtain ⟨y, hy, hy0⟩ := hgne (U ∩ V) (hU.inter hVopen) inter_subset_left ⟨x, hx, hxV⟩
  exact hy0 (hVsub hy.2)

/-- **A bounded holomorphic quotient is holomorphic** (Riemann extension).  If `f`
and `g` are holomorphic near `x`, `g` vanishes identically on no nonempty open
subset of a neighbourhood `U` of `x`, and `‖f‖ ≤ C ‖g‖` near `x`, then `f = w g`
near `x` for a germ `w` holomorphic at `x`. -/
theorem exists_holomorphicAt_eventuallyEq_mul
    {f g : M → ℂ} {x : M} {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hgne : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hbdd : ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ C * ‖g y‖) :
    ∃ w : M → ℂ, HolomorphicAt n w x ∧ f =ᶠ[𝓝 x] fun y => w y * g y := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  set Γ : ComplexModel n → ℂ := fun z => g (rechartSymm n x z) with hΓ
  set F : ComplexModel n → ℂ := fun z => f (rechartSymm n x z) with hF
  have hΓdiff : ∀ᶠ z : ComplexModel n in 𝓝 0, DifferentiableAt ℂ Γ z :=
    differentiableAt_comp_rechartSymm hg
  have hFdiff : ∀ᶠ z : ComplexModel n in 𝓝 0, DifferentiableAt ℂ F z :=
    differentiableAt_comp_rechartSymm hf
  -- `Γ` does not vanish identically near the origin
  have hΓne : ¬ ∀ᶠ z : ComplexModel n in 𝓝 0, Γ z = 0 := by
    intro hev
    refine not_eventually_eq_zero hU hx hgne ?_
    filter_upwards [tendsto_rechart x hev, eventually_rechartSymm_rechart (n := n) x] with y hy hy'
    have : g (rechartSymm n x (rechart n x y)) = 0 := hy
    rwa [hy'] at this
  -- the quotient is holomorphic and bounded off the zero set of `Γ`
  have hQdiff : ∀ᶠ z : ComplexModel n in 𝓝 0,
      Γ z ≠ 0 → DifferentiableAt ℂ (fun z => F z / Γ z) z := by
    filter_upwards [hFdiff, hΓdiff] with z hFz hΓz hz0
    simp only [div_eq_mul_inv]
    exact hFz.mul (hΓz.inv hz0)
  have hCbound : ∀ᶠ z : ComplexModel n in 𝓝 0, ‖F z‖ ≤ C * ‖Γ z‖ :=
    tendsto_rechartSymm x hC
  have hQbdd : ∃ D : ℝ, ∀ᶠ z : ComplexModel n in 𝓝 0,
      Γ z ≠ 0 → ‖F z / Γ z‖ ≤ D := by
    refine ⟨C, ?_⟩
    filter_upwards [hCbound] with z hz hz0
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]
    exact hz
  obtain ⟨W, hWdiff, hWeq⟩ :=
    RiemannExtension.exists_extension_euclidean hΓdiff hΓne hQdiff hQbdd
  refine ⟨fun y => W (rechart n x y), holomorphicAt_comp_rechart hWdiff, ?_⟩
  -- the identity `f = w g` holds where `g ≠ 0`, hence everywhere by density
  have hwhol : HolomorphicAt n (fun y => W (rechart n x y)) x :=
    holomorphicAt_comp_rechart hWdiff
  have hgood : ∀ᶠ y in 𝓝 x, g y ≠ 0 →
      f y = W (rechart n x y) * g y := by
    filter_upwards [tendsto_rechart x hWeq, eventually_rechartSymm_rechart (n := n) x] with y hy hy' hy0
    have hΓy : Γ (rechart n x y) = g y := by
      show g (rechartSymm n x (rechart n x y)) = g y
      rw [hy']
    have hFy : F (rechart n x y) = f y := by
      show f (rechartSymm n x (rechart n x y)) = f y
      rw [hy']
    have hW := hy (by rw [hΓy]; exact hy0)
    rw [hW, hFy, hΓy, div_mul_cancel₀ _ hy0]
  -- assemble an open neighbourhood on which everything above holds
  obtain ⟨N₀, hN₀sub, hN₀open, hxN₀⟩ := mem_nhds_iff.mp
    (hgood.and (hf.eventually.and (hg.eventually.and hwhol.eventually)))
  set N : Set M := U ∩ N₀ with hN
  have hNopen : IsOpen N := hU.inter hN₀open
  have hxN : x ∈ N := ⟨hx, hxN₀⟩
  have hcontf : ContinuousOn f N := fun y hy =>
    ((hN₀sub hy.2).2.1.continuousAt).continuousWithinAt
  have hcontg : ContinuousOn g N := fun y hy =>
    ((hN₀sub hy.2).2.2.1.continuousAt).continuousWithinAt
  have hcontw : ContinuousOn (fun y => W (rechart n x y) * g y) N := by
    refine ContinuousOn.mul (fun y hy => ?_) hcontg
    exact ((hN₀sub hy.2).2.2.2.continuousAt).continuousWithinAt
  have hdense : N ⊆ closure (N ∩ {y | g y ≠ 0}) := by
    intro y hy
    rw [mem_closure_iff]
    intro o hoopen hyo
    obtain ⟨z, hz, hz0⟩ := hgne (N ∩ o) (hNopen.inter hoopen)
      (inter_subset_left.trans inter_subset_left) ⟨y, hy, hyo⟩
    exact ⟨z, hz.2, hz.1, hz0⟩
  have heq : EqOn f (fun y => W (rechart n x y) * g y) N := by
    refine Set.EqOn.of_subset_closure ?_ hcontf hcontw inter_subset_left hdense
    rintro y ⟨hyN, hy0⟩
    exact (hN₀sub hyN.2).1 hy0
  exact eventually_of_mem (hNopen.mem_nhds hxN) heq

end

end Hironaka.HolomorphicBoundedQuotient
