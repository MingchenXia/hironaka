/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NestedFlattening
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Hadamard bridge along a submanifold

Source: Włodarczyk 2005 §2.2 (the lemma `𝓘 ⊂ 𝓘_C^μ` for a smooth centre `C ⊂ supp(𝓘, μ)`), applied on the
submanifold `N` of a marked ideal `(M, N, E, 𝓘, d)` (Bierstone--Milman 2008, Definitions 2.1--2.2: `𝓘` is an ideal
of `𝒪_N`).

Let `𝔞` be a coherent ideal on `M`, `N` a closed submanifold and `C ⊆ N` a closed submanifold contained in the
cosupport of `𝔞` ALONG `N`, `cosupp(𝔞|_N, μ)`.  Then `𝔞|_N ⊆ 𝓘_C^μ|_N`, i.e. `RestrictLe N 𝔞 𝓘_C^μ`
(`restrictLe_idealPow_vanishingIdeal_of_subset_cosupport`).  For `N = M` this is
`HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport`.

Consumer: the transformed ideal of the corrected transform is coherent for EVERY admissible centre of a marked ideal
with `N` a closed submanifold and coherent ideal (`isCoherent_geoTransform_ideal_of_isAdmissibleCentre`), which with
`MarkedIdeal.isClosedSubmanifold_geoTransform_N` is the submanifold-and-ideal half of "admissible blowups preserve
well-formedness".

## Proof

At `x ∈ C` take nested flattening coordinates `ψ = Φ ∘ e` (`NestedFlattening.exists_nested_flattening`: `C =
ψ⁻¹(ℂ^{k_C} × 0)`, `N = ψ⁻¹(ℂ^{k_N} × 0)`, `ψ x = 0`) and the linear retraction `P` of `ℂⁿ` onto `ℂ^{k_N} × 0`
(`planeRetract`). For `g ∈ 𝔞_x`, the function `ĝ = g ∘ ψ⁻¹ ∘ P ∘ ψ` agrees with `g` on `N` near `x`. At a point `w`
of `ℂ^{k_C} × 0` near `0`, `z = ψ⁻¹ w ∈ C` and (coherence) `g ∈ 𝔞_z`, so `g` agrees on `N` near `z` with some `h ∈
𝔪_z^μ`; since `ψ⁻¹ ∘ P` maps into `N` and sends `w` to `z`, `F̂ = g ∘ ψ⁻¹ ∘ P` agrees near `w` with `h ∘ ψ⁻¹ ∘ P ∈
𝔪_w^μ`. So all derivatives of order `< μ` of `F̂` vanish along `ℂ^{k_C} × 0`, and Taylor lemma
(`HolomorphicTaylorTail.inNormalPow_of_iterDeriv_eq_zero`) with `OrderTaylor.mem_idealPow_of_inNormalPow` gives `ĝ ∈
𝓘_C^μ` at `x`. Off `C`, `𝓘_C` contains `1`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HadamardBridgeAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates Hironaka.HadamardBridge Hironaka.RestrictedIdealWeight

noncomputable section

/-! ### The retraction of `ℂⁿ` onto `ℂᵏ × 0` -/

section Retract

variable {n : ℕ}

/-- The linear retraction of `ℂⁿ` onto the coordinate plane `ℂᵏ × 0` (zero the coordinates `≥ k`). -/
def planeRetract (k : ℕ) : ComplexModel n →L[ℂ] ComplexModel n :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.1 < k),
    (EuclideanSpace.proj (𝕜 := ℂ) i).smulRight (EuclideanSpace.single i (1 : ℂ))

theorem planeRetract_apply (k : ℕ) (w : ComplexModel n) (j : Fin n) :
    planeRetract k w j = if j.1 < k then w j else 0 := by
  simp only [planeRetract, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, PiLp.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, EuclideanSpace.proj, PiLp.proj_apply]
  rw [Finset.sum_ite_eq]
  simp

theorem planeRetract_mem (k : ℕ) (w : ComplexModel n) :
    planeRetract k w ∈ complexCoordinatePlane n k := fun j hj => by
  rw [planeRetract_apply, if_neg (by omega)]

theorem planeRetract_of_mem {k : ℕ} {w : ComplexModel n} (hw : w ∈ complexCoordinatePlane n k) :
    planeRetract k w = w := by
  ext j
  rw [planeRetract_apply]
  split_ifs with hj
  · rfl
  · exact (hw j (by omega)).symm

theorem planeRetract_zero (k : ℕ) : planeRetract (n := n) k 0 = 0 := map_zero _

end Retract

/-! ### The bridge along `N` -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The Hadamard bridge along a submanifold** (`hir:hadamard-bridge-along`): if `𝔞` is coherent, `N` a closed
submanifold and `C ⊆ N` a closed submanifold contained in `cosupp(𝔞|_N, μ)`, then `𝔞|_N ⊆ 𝓘_C^μ|_N`. -/
theorem restrictLe_idealPow_vanishingIdeal_of_subset_cosupport {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    {N C : Set M} (hN : IsClosedSubmanifold n N) (hC : IsClosedSubmanifold n C) (hCN : C ⊆ N) {μ : ℕ}
    (hsub : C ⊆ cosupport n N 𝔞 μ) :
    RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) μ) := by
  intro y hyN f hf
  have hfhol : HolomorphicAt n f y :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hf
  -- it suffices to find a germ `ĝ ∈ 𝓘_C^μ` at `y` agreeing with `f` on `N`
  suffices H : ∃ g : M → ℂ, (idealPow (vanishingIdeal (n := n) C) μ).mem y g ∧
      ∀ᶠ p in 𝓝 y, p ∈ N → f p = g p by
    obtain ⟨g, hg, hfg⟩ := H
    refine ⟨1, fun _ => g, fun _ => 1, fun _ => hg, fun _ => holomorphicAt_const 1, ?_⟩
    filter_upwards [hfg] with p hp hpN
    simp [hp hpN]
  by_cases hyC : y ∉ C
  · -- off `C`, `𝓘_C` is the unit ideal
    refine ⟨f, mem_idealPow_of_one_mem (I := vanishingIdeal (n := n) C) ⟨holomorphicAt_const 1, ?_⟩ hfhol μ,
      Eventually.of_forall fun _ _ => rfl⟩
    filter_upwards [hC.1.isOpen_compl.mem_nhds hyC] with z hz hzC
    exact absurd hzC hz
  rw [not_not] at hyC
  obtain ⟨kC, hkC⟩ := hC.2 y hyC
  obtain ⟨kN, hkN⟩ := hN.2 y hyN
  obtain ⟨Φ, hΦsrc, hΦy, hflat⟩ := NestedFlattening.exists_nested_flattening
    (BlowupStrictSubmanifold.le_of_regularAtDim_subset hkC hkN hCN) hkC hkN hCN
  set e := chartAt (ComplexModel n) y
  have hy : y ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflatC : ∀ {p : M}, p ∈ e.source → e p ∈ Φ.source →
      (p ∈ C ↔ Φ.toFun (e p) ∈ complexCoordinatePlane n kC) := fun hp hpΦ => (hflat hp hpΦ).1
  have hflatN : ∀ {p : M}, p ∈ e.source → e p ∈ Φ.source →
      (p ∈ N ↔ Φ.toFun (e p) ∈ complexCoordinatePlane n kN) := fun hp hpΦ => (hflat hp hpΦ).2
  have hkCN : kC ≤ kN := BlowupStrictSubmanifold.le_of_regularAtDim_subset hkC hkN hCN
  set P := planeRetract (n := n) kN
  set ψ : M → ComplexModel n := fun p => Φ.toFun (e p)
  set φ : ComplexModel n → M := fun w => e.symm (Φ.invFun w)
  set F : ComplexModel n → ℂ := fun w => f (φ (P w))
  have hψy : ψ y = 0 := hΦy
  have hq : (0 : ComplexModel n) ∈ complexCoordinatePlane n kC := fun i _ => rfl
  have hTnhds : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ Φ.target := by
    rw [← hψy]
    exact Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hy.2)
  have hPT : Tendsto P (𝓝 0) (𝓝 0) := by
    have := P.continuous.tendsto 0
    rwa [planeRetract_zero] at this
  have hTP : ∀ᶠ w in 𝓝 (0 : ComplexModel n), P w ∈ Φ.target := hPT.eventually hTnhds
  have hφT : Tendsto φ (𝓝 0) (𝓝 y) := by
    rw [← hψy]
    exact tendsto_flatInverse Φ hy
  have hφd : ∀ w ∈ Φ.target,
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ w := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun w :=
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
    exact (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hw))).comp w h1
  -- `φ ∘ P` is holomorphic where `P` lands in `Φ.target`
  have hφPd : ∀ w, P w ∈ Φ.target →
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (φ ∘ P) w := by
    intro w hw
    exact (hφd _ hw).comp w P.differentiableAt.mdifferentiableAt
  -- `F` is holomorphic near `0`
  have hFd : ∀ᶠ w in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F w := by
    have hPφT : Tendsto (φ ∘ P) (𝓝 0) (𝓝 y) := hφT.comp hPT
    filter_upwards [hTP.eventually_nhds, hPφT.eventually hfhol.eventually] with w hw hfw
    have hφw : ∀ᶠ w' in 𝓝 w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (φ ∘ P) w' :=
      hw.mono fun w' hw' => hφPd w' hw'
    exact mdifferentiableAt_iff_differentiableAt.mp
      (holomorphicAt_comp_map hφw hfw).self_of_nhds
  -- the derivatives of order `< μ` of `F` vanish along `ℂ^{k_C} × 0`
  have hvan : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ complexCoordinatePlane n kC →
      ∀ L : List (ComplexModel n), L.length < μ → iterDeriv L F w = 0 := by
    filter_upwards [hTnhds.eventually_nhds, hTP.eventually_nhds,
      hφT.eventually (eventually_mem_of_isCoherent h𝔞 hf)] with w hw hwP hfw hwk L hL
    obtain ⟨hmem, hΦw⟩ := flatInverse_mem Φ hw.self_of_nhds hΦsrc
    have hwN : w ∈ complexCoordinatePlane n kN := fun i hi => hwk i (le_trans hkCN hi)
    have hPw : P w = w := planeRetract_of_mem hwN
    have hzC : φ w ∈ C := (hflatC hmem.1 hmem.2).mpr (by
      change Φ.toFun (e (e.symm (Φ.invFun w))) ∈ _
      rw [hΦw]
      exact hwk)
    -- `f` agrees on `N` near `z = φ w` with a germ `h ∈ 𝔪_z^μ`
    obtain ⟨h, hh, hfh⟩ := (hsub hzC).2 f hfw
    -- `φ ∘ P` maps a neighbourhood of `w` into `N`, near `z`
    have hφPw : (φ ∘ P) w = φ w := by simp only [Function.comp_apply, hPw]
    have hPφT : Tendsto (φ ∘ P) (𝓝 w) (𝓝 (φ w)) := by
      have := (hφPd w (by rw [hPw]; exact hw.self_of_nhds)).continuousAt.tendsto
      rwa [hφPw] at this
    have hFeq : F =ᶠ[𝓝 w] h ∘ (φ ∘ P) := by
      filter_upwards [hwP, hPφT.eventually hfh] with w' hw'P hw'
      refine hw' ?_
      obtain ⟨hmem', hΦw'⟩ := flatInverse_mem Φ hw'P hΦsrc
      refine (hflatN hmem'.1 hmem'.2).mpr ?_
      change Φ.toFun (e (e.symm (Φ.invFun (P w')))) ∈ _
      rw [hΦw']
      exact planeRetract_mem kN w'
    have hφPw' : ∀ᶠ w' in 𝓝 w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (φ ∘ P) w' :=
      hwP.mono fun w' hw' => hφPd w' hw'
    have hh' : (idealPow (pointIdeal n ((φ ∘ P) w)) μ).mem ((φ ∘ P) w) h := by
      rw [hφPw]; exact hh
    have hFw : (idealPow (pointIdeal n w) μ).mem w F :=
      mem_idealPow_congr (comp_mem_idealPow_pointIdeal hφPw' μ hh') hFeq.symm
    set e₀ := complexChartAt (n := n) w
    have hw₀ : w ∈ e₀.val.source := mem_complexChartAt_source w
    have h0 := iterChartDeriv_eq_zero_of_mem_idealPow hw₀ hFw L hL
    rw [iterChartDeriv_eq_iterDeriv e₀ F L hw₀] at h0
    simpa [e₀, complexChartAt, chartAt_self_eq] using h0
  have hNP : InNormalPow kC 0 μ F := inNormalPow_of_iterDeriv_eq_zero μ hq hFd hvan
  -- pull back along the flattening coordinates
  have hψ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun (e p) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp.2)).mdifferentiableAt
    exact h1.comp p (mdifferentiableAt_chart hp.1)
  have hψI : ∀ i : Fin n, kC ≤ i.1 → (vanishingIdeal (n := n) C).mem y (fun p => ψ p i) :=
    fun i hi => flatCoord_mem_vanishingIdeal Φ hflatC hi hy
  refine ⟨fun p => F (ψ p), mem_idealPow_of_inNormalPow hψy hψ hψI μ hNP
    (Eventually.of_forall fun _ => rfl), ?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with p hp hpN
  have hψN : ψ p ∈ complexCoordinatePlane n kN := (hflatN hp.1 hp.2).mp hpN
  simp only [F, φ, ψ, P, planeRetract_of_mem hψN]
  rw [flatInverse_flat Φ hp]

/-! ### Consumer: coherence of the corrected transform -/

open MarkedIdeals MarkedIdeals.MarkedIdeal in
/-- **The transformed ideal is coherent for every admissible centre** of a marked ideal whose `N` is a closed
submanifold and whose ideal is coherent. -/
theorem isCoherent_geoTransform_ideal_of_isAdmissibleCentre {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {𝔪 : MarkedIdeal n X} {C : Set X}
    {π : Y → X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) :
    (𝔪.geoTransform C π).ideal.IsCoherent :=
  isCoherent_geoTransform_ideal h𝔞 hN hπ hC.subset_N
    (restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hC.1 hC.subset_N hC.2.1)

end

end Hironaka.HadamardBridgeAlong
