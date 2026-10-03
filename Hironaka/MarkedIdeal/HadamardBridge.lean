/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Hadamard bridge: an ideal of order `≥ μ` along a smooth centre lies in `𝓘_C^μ`

Source: Włodarczyk 2005 §2.2 (the lemma `𝓘 ⊂ 𝓘_C^μ` for a smooth centre `C ⊂ supp(𝓘, μ)`, used to define the
controlled transform).

Let `𝔞` be a coherent ideal sheaf on a complex manifold `M` and `C ⊆ M` a closed complex submanifold contained in
the cosupport `cosupp(𝔞, μ) = {x | ord_x 𝔞 ≥ μ}`. Then `𝔞 ⊆ 𝓘_C^μ`
(`le_idealPow_vanishingIdeal_of_subset_cosupport`).

## Proof

Off `C`, `𝓘_C` contains `1`. At `y ∈ C`, take flattening coordinates `ψ = Φ ∘ e` (`RegularAtDim`) with `C = ψ⁻¹(ℂᵏ ×
0)` and `ψ y = 0`, and `F = f ∘ ψ⁻¹` for `f ∈ 𝔞_y`. By coherence `f ∈ 𝔞_z` for `z` near `y`; for `z ∈ C` this gives
`f ∈ 𝔪_z^μ`, hence `F ∈ 𝔪_{ψ z}^μ` (pullback of powers of the maximal ideal along a holomorphic map,
`comp_mem_idealPow_pointIdeal`), hence every iterated derivative of order `< μ` of `F` vanishes at `ψ z`
(`OrderTaylor.iterChartDeriv_eq_zero_of_mem_idealPow` on `ℂⁿ`).
`HolomorphicTaylorTail.inNormalPow_of_iterDeriv_eq_zero` turns this into "`F` lies in the `μ`-th power of the ideal
of the normal coordinates", and `OrderTaylor.mem_idealPow_of_inNormalPow` pulls that back to `f ∈ 𝓘_C^μ` at `y`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HadamardBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Pulling back powers of the maximal ideal -/

section Pullback

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]

/-- A holomorphic germ composed with a holomorphic map is holomorphic. -/
theorem holomorphicAt_comp_map {φ : Y → M} {u : Y} {f : M → ℂ}
    (hφ : ∀ᶠ w in 𝓝 u, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ w)
    (hf : HolomorphicAt n f (φ u)) : HolomorphicAt m (f ∘ φ) u := by
  filter_upwards [hφ, hφ.self_of_nhds.continuousAt.eventually hf] with w hw hfw
  exact hfw.comp w hw

/-- **Powers of the maximal ideal pull back**: if `φ` is holomorphic near `u` and `f ∈ 𝔪_{φ u}^μ`, then
`f ∘ φ ∈ 𝔪_u^μ`. -/
theorem comp_mem_idealPow_pointIdeal {φ : Y → M} {u : Y}
    (hφ : ∀ᶠ w in 𝓝 u, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) φ w) :
    ∀ (μ : ℕ) {f : M → ℂ}, (idealPow (pointIdeal n (φ u)) μ).mem (φ u) f →
      (idealPow (pointIdeal m u) μ).mem u (f ∘ φ)
  | 0, f, hf => holomorphicAt_comp_map hφ hf
  | μ + 1, f, hf => by
    obtain ⟨hfhol, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp hf
    choose a b ha hb hab using hr
    have hcont : ContinuousAt φ u := hφ.self_of_nhds.continuousAt
    refine mem_idealPow_succ_iff.mpr ⟨holomorphicAt_comp_map hφ hfhol, K,
      fun k => (a k ∘ φ) * (b k ∘ φ), fun k => c k ∘ φ,
      fun k => ⟨a k ∘ φ, b k ∘ φ, comp_mem_idealPow_pointIdeal hφ μ (ha k), ?_, rfl⟩,
      fun k => holomorphicAt_comp_map hφ (hc k), ?_⟩
    · exact mem_pointIdeal_of_apply_eq_zero (holomorphicAt_comp_map hφ (hb k).1)
        (show b k (φ u) = 0 from apply_eq_zero_of_mem_pointIdeal (n := n) (hb k))
    · filter_upwards [hcont.eventually hsum] with w hw
      simp only [Function.comp_apply, hw, hab, Pi.mul_apply]

end Pullback

/-! ### Coherent ideals: germs propagate to nearby points -/

/-- A germ of a coherent ideal at `y` is a germ of the ideal at every point near `y`. -/
theorem eventually_mem_of_isCoherent {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {y : M} {f : M → ℂ}
    (hf : 𝔞.mem y f) : ∀ᶠ z in 𝓝 y, 𝔞.mem z f := by
  obtain ⟨U, hU, hyU, N, s, -, hgen⟩ := h𝔞 y
  obtain ⟨hfhol, K, t, a, ht, ha, hsum⟩ := (hgen y hyU f).mp hf
  filter_upwards [hU.mem_nhds hyU, eventually_all.mpr fun i => (ha i).eventually,
    hfhol.eventually, hsum.eventually_nhds] with z hzU hza hzf hzsum
  exact (hgen z hzU f).mpr ⟨hzf, K, t, a, ht, hza, hzsum⟩

/-- If `I` contains `1` at `y`, every holomorphic germ at `y` lies in every power of `I`. -/
theorem mem_idealPow_of_one_mem {I : GermIdeal n M} {y : M} (h1 : I.mem y fun _ => 1) {f : M → ℂ}
    (hf : HolomorphicAt n f y) : ∀ μ : ℕ, (idealPow I μ).mem y f
  | 0 => hf
  | μ + 1 => by
    have := mul_mem_idealPow_succ (mem_idealPow_of_one_mem h1 hf μ) h1
      (hf.mul (holomorphicAt_const 1))
    exact mem_idealPow_congr this (Eventually.of_forall fun p => mul_one (f p))

/-! ### The bridge -/

/-- **The Hadamard bridge** (`hir:hadamard-bridge`; Włodarczyk 2005 §2.2): if `𝔞` is coherent and the
closed submanifold `C` lies in the cosupport `cosupp(𝔞, μ)` (orders taken on `M` itself), then
`𝔞 ⊆ 𝓘_C^μ`. -/
theorem le_idealPow_vanishingIdeal_of_subset_cosupport {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    {C : Set M} (hC : IsClosedSubmanifold n C) {μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 μ) :
    𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ) := by
  intro y f hf
  have hfhol : HolomorphicAt n f y := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hf
  by_cases hyC : y ∉ C
  · -- off `C`, `𝓘_C` is the unit ideal
    refine mem_idealPow_of_one_mem (I := vanishingIdeal (n := n) C) ⟨holomorphicAt_const 1, ?_⟩ hfhol μ
    filter_upwards [hC.1.isOpen_compl.mem_nhds hyC] with z hz hzC
    exact absurd hzC hz
  rw [not_not] at hyC
  obtain ⟨k, -, -, Φ, hΦsrc, hΦy, hflat⟩ := hC.2 y hyC
  set e := chartAt (ComplexModel n) y
  have hy : y ∈ flatDomain Φ := mem_flatDomain_self Φ
  -- the flattening coordinates `ψ = Φ ∘ e` and `F = f ∘ ψ⁻¹`
  set ψ : M → ComplexModel n := fun p => Φ.toFun (e p)
  set φ : ComplexModel n → M := fun w => e.symm (Φ.invFun w)
  set F : ComplexModel n → ℂ := f ∘ φ
  have hψy : ψ y = 0 := hΦy
  have hq : (0 : ComplexModel n) ∈ complexCoordinatePlane n k := fun i _ => rfl
  have hTnhds : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ Φ.target := by
    rw [← hψy]
    exact Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hy.2)
  have hφT : Tendsto φ (𝓝 0) (𝓝 y) := by
    rw [← hψy]
    exact tendsto_flatInverse Φ hy
  have hφd : ∀ w ∈ Φ.target,
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun w :=
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
    exact (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hw))).comp w h1
  -- `F` is holomorphic near `0`
  have hFd : ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F w := by
    filter_upwards [hTnhds.eventually_nhds, hφT.eventually hfhol.eventually] with w hw hfw
    have hφw : ∀ᶠ w' in 𝓝 w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w' :=
      hw.mono fun w' hw' => hφd w' hw'
    exact mdifferentiableAt_iff_differentiableAt.mp
      (holomorphicAt_comp_map hφw hfw).self_of_nhds
  -- the derivatives of order `< μ` of `F` vanish along `ℂᵏ × 0`
  have hvan : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n k →
      ∀ L : List (ComplexModel n), L.length < μ → iterDeriv L F w = 0 := by
    filter_upwards [hTnhds.eventually_nhds, hφT.eventually (eventually_mem_of_isCoherent h𝔞 hf)]
      with w hw hfw hwk L hL
    obtain ⟨hmem, hΦw⟩ := flatInverse_mem Φ hw.self_of_nhds hΦsrc
    have hzC : φ w ∈ C := (hflat hmem.1 hmem.2).mpr (by
      change Φ.toFun (e (e.symm (Φ.invFun w))) ∈ _
      rw [hΦw]
      exact hwk)
    have hfz : (idealPow (pointIdeal n (φ w)) μ).mem (φ w) f :=
      mem_idealPow_of_vanishesToOrderOn_univ ((hsub hzC).2 f hfw)
    have hφw : ∀ᶠ w' in 𝓝 w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w' :=
      hw.mono fun w' hw' => hφd w' hw'
    have hFw : (idealPow (pointIdeal n w) μ).mem w F := comp_mem_idealPow_pointIdeal hφw μ hfz
    set e₀ := complexChartAt (n := n) w
    have hw₀ : w ∈ e₀.val.source := mem_complexChartAt_source w
    have h0 := iterChartDeriv_eq_zero_of_mem_idealPow hw₀ hFw L hL
    rw [iterChartDeriv_eq_iterDeriv e₀ F L hw₀] at h0
    simpa [e₀, complexChartAt, chartAt_self_eq] using h0
  have hNP : InNormalPow k 0 μ F := inNormalPow_of_iterDeriv_eq_zero μ hq hFd hvan
  -- pull back along the flattening coordinates
  have hψ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun (e p) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp.2)).mdifferentiableAt
    exact h1.comp p (mdifferentiableAt_chart hp.1)
  have hψI : ∀ i : Fin n, k ≤ i.1 → (vanishingIdeal (n := n) C).mem y (fun p => ψ p i) :=
    fun i hi => flatCoord_mem_vanishingIdeal Φ hflat hi hy
  refine mem_idealPow_of_inNormalPow hψy hψ hψI μ hNP ?_
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp
  simp only [F, φ, ψ, Function.comp_apply]
  rw [flatInverse_flat Φ hp]

/-! ### Consumers: admissible centres and the controlled transform -/

section Consumers

open BlowupExceptionalDivisor BlowupControlledTransform MarkedIdeals

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **Admissible centres of a marked ideal with `N = M`**: if the ideal is coherent and `C` is an
admissible centre of `(M, M, E, 𝔞, d)`, then `𝔞 ⊆ 𝓘_C^d`. -/
theorem ideal_le_idealPow_of_isAdmissibleCentre {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C) :
    𝔪.ideal.Le (idealPow (vanishingIdeal (n := n) C) 𝔪.d) :=
  le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hC.1
    (by have h := hC.2.1; rwa [MarkedIdeal.cosupp, hN] at h)

end Consumers

end

end Hironaka.HadamardBridge
