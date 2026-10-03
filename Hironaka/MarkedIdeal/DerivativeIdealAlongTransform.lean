/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.HolomorphicMaps
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals along a submanifold under a blowup

Sources: Włodarczyk 2005, Lemma `le:inclusions` (`σ^c(𝓓^r(𝔞), μ) ⊆ 𝓓^r(σ^c(𝔞, μ + r))`) and §2.6; Bierstone--Milman
2008, Lemmas 3.1--3.3 (for the marked ideal `(M, N, E, 𝓘, d)` the derivatives are those of `𝓘 ⊆ 𝒪_N`, i.e. along
`N`).

Let `π : Y → X` be the blowup along `C`, `N ⊇ C` a closed submanifold with strict transform `N'`, and `(X, N, E, 𝔞, d)`
a marked ideal with `𝔞` coherent and `C` admissible.  Then on `N'`

  `[𝓓_N^j(𝔞)]' ⊆ 𝓓_{N'}^j(𝔞')`, `j ≤ d`,

where `[𝓓_N^j(𝔞)]'` is the transform of `(X, N, E, 𝓓_N^j 𝔞, d - j)` and `𝔞'` that of `(X, N, E, 𝔞, d)`.

## Method

The ambient proof writes `y · (∂f) ∘ π = D'(f ∘ π)` for a derivation `D'` of the blowup with `D'(y) ∈ (y)` (`y` a
local generator of `𝒪(-D)`). Here:

* `derivationData_of_coordinates_uniform`, `IsUniformDerivationGenerator`, `exists_isUniformDerivationGenerator`:
  the same data with `D'` chosen independently of `f` (the coefficients of the ambient construction never depended
  on `f`; the statements are re-proved in this uniform form);
* tangency: if the field `ξ` is tangent to `N` at `π z`, the lifted derivation `D'` is tangent to `N'` at `z`
  (`π^*𝓘_N = 𝒪(-D) · 𝓘_{N'}`, `BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul`, and the points of `π⁻¹(N \ C)`,
  where `y ≠ 0`, are dense in `N'`);
* then the ambient argument runs on `N'`, the cancellation of `y^{μ+1}` on `N'` again by density.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.DerivativeIdealAlongTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps GermIdealOrder DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient BlowupExceptionalDivisor BlowupControlledTransform BlowupDerivativeIdeal

noncomputable section

/-! ### The derivation `y σ^*(Der)`, uniformly in the function -/

section Assembly

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Chart derivatives in flattening coordinates, uniformly in the function**. If `Φ` is a local biholomorphism at `e
x` (`e` a chart at `x`), every chart derivative of `f` near `x` is a holomorphic combination of the coordinate
derivatives of `F = f ∘ e⁻¹ ∘ Φ⁻¹` at `Φ (e q)`. -/
theorem chartDeriv_eventuallyEq_sum_flat_uniform {x : X} (e : ComplexChart n X) (hxs : x ∈ e.val.source)
    (Φ : LocalHolomorphicEquivAt (n := n) (e.val x)) (e' : ComplexChart n X) (hx' : x ∈ e'.val.source)
    (v : ComplexModel n) :
    ∃ α : Fin n → X → ℂ, (∀ i, HolomorphicAt n (α i) x) ∧ ∀ {f : X → ℂ}, HolomorphicAt n f x →
      chartDeriv e' v f =ᶠ[𝓝 x] fun q => ∑ i, α i q *
        fderiv ℂ (f ∘ e.val.symm ∘ Φ.invFun) (Φ.toFun (e.val q)) (EuclideanSpace.single i 1) := by
  classical
  refine ⟨fun i q => ∑ l, transitionCoeff e e' v l q *
    fderiv ℂ Φ.toFun (e.val q) (EuclideanSpace.single l 1) i, fun i => ?_, fun {f} hf => ?_⟩
  · refine HolomorphicAt.sum _ fun l _ => (holomorphicAt_transitionCoeff e e' hxs hx' l).mul ?_
    have hdi := Hironaka.differentiableOn_fderiv_apply_of_isOpen Φ.toFun_holomorphic
      Φ.isOpen_source (EuclideanSpace.single l (1 : ℂ))
    refine holomorphicAt_comp_chart e
      (W := fun ζ => fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1) i) hxs ?_
    filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with ζ hζ
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp ζ
      ((hdi ζ hζ).differentiableAt (Φ.isOpen_source.mem_nhds hζ))
  · set F := f ∘ e.val.symm ∘ Φ.invFun with hF
    have hsrc : ∀ᶠ q in 𝓝 x, q ∈ e.val.source ∧ e.val q ∈ Φ.source :=
      Filter.Eventually.and (e.val.open_source.mem_nhds hxs)
        ((e.val.continuousAt hxs).preimage_mem_nhds
          (Φ.isOpen_source.mem_nhds Φ.center_mem_source))
    filter_upwards [chartDeriv_eventuallyEq_sum (v := v) e e' hxs hx' hf, hsrc,
      hf.eventually_nhds] with q hq hqs hfq
    rw [hq]
    obtain ⟨hqe, hqΦ⟩ := hqs
    set ζ := e.val q with hζ
    have hT : Φ.toFun ζ ∈ Φ.target := Φ.mapsTo_toFun hqΦ
    have hΦd : DifferentiableAt ℂ Φ.toFun ζ :=
      (Φ.toFun_holomorphic ζ hqΦ).differentiableAt (Φ.isOpen_source.mem_nhds hqΦ)
    have hId : DifferentiableAt ℂ Φ.invFun (Φ.toFun ζ) :=
      (Φ.invFun_holomorphic _ hT).differentiableAt (Φ.isOpen_target.mem_nhds hT)
    have hfe : DifferentiableAt ℂ (f ∘ e.val.symm) (Φ.invFun (Φ.toFun ζ)) := by
      rw [Φ.left_inv ζ hqΦ]
      exact (eventually_differentiableAt_comp_symm e hqe hfq).self_of_nhds
    have hFd : DifferentiableAt ℂ F (Φ.toFun ζ) := hfe.comp _ hId
    have hloc : f ∘ e.val.symm =ᶠ[𝓝 ζ] F ∘ Φ.toFun := by
      filter_upwards [Φ.isOpen_source.mem_nhds hqΦ] with ζ' hζ'
      simp only [hF, Function.comp_apply, Φ.left_inv ζ' hζ']
    have hl : ∀ l, chartDeriv e (EuclideanSpace.single l 1) f q =
        ∑ i, fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1) i *
          fderiv ℂ F (Φ.toFun ζ) (EuclideanSpace.single i 1) := fun l => by
      simp only [chartDeriv, ← hζ, hloc.fderiv_eq, fderiv_comp ζ hFd hΦd,
        ContinuousLinearMap.comp_apply]
      conv_lhs => rw [← sum_smul_single (fderiv ℂ Φ.toFun ζ (EuclideanSpace.single l 1))]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    simp only [hl, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The derivation data at a point of a holomorphic map, from local coordinates.** Let `π: Y → X` be holomorphic, `z
∈ Y`, `x = π z`, `Φ` a local biholomorphism at `e_x x`, `W` a local holomorphic coordinate system at `z` with `Φ ∘
e_x ∘ π = Ψ ∘ W` near `z`, and suppose that the function `Q` (read through `W`) satisfies the two identities of the
source's `y σ^*(Der)`: `Q (∂ᵢ F) ∘ Ψ = ∑ₗ Pᵢₗ ∂ₗ (F ∘ Ψ)` and `∑ₗ Pᵢₗ ∂ₗ Q = Rᵢ Q`. Then for every chart `e'` at `x`
and every `v` there is ONE derivation `D' = ∑ₘ bₘ ∂^{e_z}_{eₘ}` with holomorphic coefficients and `D'(y) ∈ (y)` such
that `y · (∂^{e'}_v f) ∘ π = D'(f ∘ π)` (`y = Q ∘ W`) for EVERY `f` holomorphic near `x` (whose coefficients do not
depend on `f`). -/
theorem derivationData_of_coordinates_uniform {π : Y → X}
    (hπs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {z : Y}
    (ex : ComplexChart n X) (hxs : π z ∈ ex.val.source)
    (Φ : LocalHolomorphicEquivAt (n := n) (ex.val (π z)))
    {W : Y → ComplexModel n} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hzN : (complexChartAt (n := n) z).val z ∈ N)
    (hFd : DifferentiableOn ℂ (W ∘ (complexChartAt (n := n) z).val.symm) N)
    (hinj : Function.Injective
      (fderiv ℂ (W ∘ (complexChartAt (n := n) z).val.symm) ((complexChartAt (n := n) z).val z)))
    {Ψ : ComplexModel n → ComplexModel n} (hΨ : Differentiable ℂ Ψ)
    (hΦW : ∀ᶠ p in 𝓝 z, π p ∈ ex.val.source ∧ ex.val (π p) ∈ Φ.source ∧
      Φ.toFun (ex.val (π p)) = Ψ (W p))
    {Q : ComplexModel n → ℂ} (hQ : Differentiable ℂ Q)
    {P : Fin n → Fin n → ComplexModel n → ℂ} (hP : ∀ i l, Differentiable ℂ (P i l))
    (hPΨ : ∀ (F : ComplexModel n → ℂ) (w : ComplexModel n), DifferentiableAt ℂ F (Ψ w) →
      ∀ i, Q w * fderiv ℂ F (Ψ w) (EuclideanSpace.single i 1) =
        ∑ l, P i l w * fderiv ℂ (F ∘ Ψ) w (EuclideanSpace.single l 1))
    {R : Fin n → ComplexModel n → ℂ} (hR : ∀ i, Differentiable ℂ (R i))
    (hPQ : ∀ i w, ∑ l, P i l w * fderiv ℂ Q w (EuclideanSpace.single l 1) = R i w * Q w)
    (e' : ComplexChart n X) (hx' : π z ∈ e'.val.source) (v : ComplexModel n) :
    ∃ b : Fin n → Y → ℂ, (∀ m, HolomorphicAt n (b m) z) ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => Q (W p) * chartDeriv e' v f (π p)) =ᶠ[𝓝 z] (fun p =>
          ∑ m, b m p * chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (f ∘ π) p)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        (fun p => ∑ m, b m p *
          chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (Q ∘ W) p)
          =ᶠ[𝓝 z] fun p => ρ p * Q (W p) := by
  classical
  set ez := complexChartAt (n := n) z with hez
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  obtain ⟨α, hα, hαeq⟩ := chartDeriv_eventuallyEq_sum_flat_uniform ex hxs Φ e' hx' v
  obtain ⟨c, hc, hceq⟩ := exists_coordDeriv_coeff hN hzN hFd hinj
  -- `W` is continuous at `z`, and functions of `W` are holomorphic at `z`
  have hWhol : ∀ H : ComplexModel n → ℂ, Differentiable ℂ H → HolomorphicAt n (fun p => H (W p)) z := by
    intro H hH
    refine (holomorphicAt_comp_chart ez (W := H ∘ (W ∘ ez.val.symm)) hzs ?_).congr ?_
    · filter_upwards [hN.mem_nhds hzN] with ζ hζ
      exact (hH _).comp ζ ((hFd ζ hζ).differentiableAt (hN.mem_nhds hζ))
    · filter_upwards [ez.val.open_source.mem_nhds hzs] with p hp
      simp only [Function.comp_apply, ez.val.left_inv hp]
  have hWc : ContinuousAt W z := by
    have hcomp : ContinuousAt (fun p => (W ∘ ez.val.symm) (ez.val p)) z :=
      ((hFd _ hzN).differentiableAt (hN.mem_nhds hzN)).continuousAt.comp
        (ez.val.continuousAt hzs)
    refine hcomp.congr ?_
    filter_upwards [ez.val.open_source.mem_nhds hzs] with p hp
    simp only [Function.comp_apply, ez.val.left_inv hp]
  -- along `π`, `Φ ∘ e_x ∘ π = Ψ ∘ W` tends to `Φ (e_x (π z))`
  have hΨWz : Ψ (W z) = Φ.toFun (ex.val (π z)) := hΦW.self_of_nhds.2.2.symm
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  refine ⟨fun m p => ∑ i, α i (π p) * ∑ l, P i l (W p) * c l m p, fun m => ?_, fun f hf => ?_,
    fun p => ∑ i, α i (π p) * R i (W p), ?_, ?_⟩
  · refine HolomorphicAt.sum _ fun i _ => ?_
    refine HolomorphicAt.mul ((hα i).comp_contMDiff (Eventually.of_forall fun p => hπs p))
      (HolomorphicAt.sum _ fun l _ => (hWhol _ (hP i l)).mul (hc l m))
  · set F := f ∘ ex.val.symm ∘ Φ.invFun with hF
    -- `F` is differentiable near `Φ (e_x (π z))`
    have hFev : ∀ᶠ w in 𝓝 (Φ.toFun (ex.val (π z))), DifferentiableAt ℂ F w := by
      have hT : Φ.toFun (ex.val (π z)) ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
      have hIc : ContinuousAt Φ.invFun (Φ.toFun (ex.val (π z))) :=
        ((Φ.invFun_holomorphic _ hT).differentiableAt (Φ.isOpen_target.mem_nhds hT)).continuousAt
      have hId : Φ.invFun (Φ.toFun (ex.val (π z))) = ex.val (π z) :=
        Φ.left_inv _ Φ.center_mem_source
      have h1 := eventually_differentiableAt_comp_symm ex hxs hf
      rw [← hId] at h1
      filter_upwards [hIc.eventually h1, Φ.isOpen_target.mem_nhds hT] with w hw hwT
      exact hw.comp w ((Φ.invFun_holomorphic w hwT).differentiableAt (Φ.isOpen_target.mem_nhds hwT))
    have hFΨ : ∀ᶠ w in 𝓝 (W z), DifferentiableAt ℂ (F ∘ Ψ) w := by
      have hΨc : ContinuousAt Ψ (W z) := (hΨ (W z)).continuousAt
      rw [ContinuousAt, hΨWz] at hΨc
      filter_upwards [hΨc.eventually hFev] with w hw
      exact hw.comp w (hΨ w)
    have hFp : ∀ᶠ p in 𝓝 z, DifferentiableAt ℂ F (Ψ (W p)) := by
      have hc' : ContinuousAt (fun p => Ψ (W p)) z := (hΨ (W z)).continuousAt.comp hWc
      rw [ContinuousAt, hΨWz] at hc'
      exact hc'.eventually hFev
    -- `(F ∘ Ψ) ∘ W = f ∘ π` near `z`
    have hGW : (F ∘ Ψ) ∘ W =ᶠ[𝓝 z] f ∘ π := by
      filter_upwards [hΦW] with p hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      simp only [hF, Function.comp_apply, ← hp3, Φ.left_inv _ hp2, ex.val.left_inv hp1]
    have hDm : ∀ m, chartDeriv ez (EuclideanSpace.single m 1) ((F ∘ Ψ) ∘ W) =ᶠ[𝓝 z]
        chartDeriv ez (EuclideanSpace.single m 1) (f ∘ π) := fun m => chartDeriv_congr hzs hGW
    have hαz : ∀ᶠ p in 𝓝 z, chartDeriv e' v f (π p) = ∑ i, α i (π p) *
        fderiv ℂ F (Φ.toFun (ex.val (π p))) (EuclideanSpace.single i 1) := hπc.eventually (hαeq hf)
    filter_upwards [hαz, hΦW, hFp, eventually_all.2 (hceq (F ∘ Ψ) hFΨ),
      eventually_all.2 hDm] with p hp1 hp2 hp3 hp4 hp5
    rw [hp1, hp2.2.2, Finset.mul_sum]
    have h1 : ∀ i, Q (W p) * (α i (π p) * fderiv ℂ F (Ψ (W p)) (EuclideanSpace.single i 1)) =
        α i (π p) * ∑ l, P i l (W p) * ∑ m, c l m p *
          chartDeriv ez (EuclideanSpace.single m 1) (f ∘ π) p := fun i => by
      rw [mul_left_comm, hPΨ F (W p) hp3 i]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hp4 l]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by rw [hp5 m]
    simp only [h1]
    exact sum_triple _ _ _ _
  · exact HolomorphicAt.sum _ fun i _ =>
      ((hα i).comp_contMDiff (Eventually.of_forall fun p => hπs p)).mul (hWhol _ (hR i))
  · filter_upwards [eventually_all.2 (hceq Q (Eventually.of_forall fun w => hQ w))] with p hp
    have hp' : ∀ l, ∑ m, c l m p * chartDeriv ez (EuclideanSpace.single m 1) (Q ∘ W) p =
        fderiv ℂ Q (W p) (EuclideanSpace.single l 1) := fun l => (hp l).symm
    rw [← sum_triple]
    simp only [hp', hPQ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

end Assembly

section PointData

open BlowupFlatCoordinates BlowupMonomialCharts

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

variable (n) in
/-- **The data of the derivation `y σ^*(Der)` near a point `z` of the blowup, uniformly in the function**: an open `U ∋
z` on which `y` generates `π^*𝓘_C = 𝒪_Y(-D)` and vanishes identically on no nonempty open set, and, for every chart
`e'` at `π z` and every `v`, ONE derivation `D' = ∑ₘ bₘ ∂^{e_z}_{eₘ}` with holomorphic coefficients and `D'(y) ∈
(y)` near `z` such that `y · (∂^{e'}_v f) ∘ π = D'(f ∘ π)` near `z` for every `f` holomorphic near `π z`. -/
structure IsUniformDerivationGenerator (π : Y → X) (C : Set X) (z : Y) (U : Set Y) (y : Y → ℂ) :
    Prop where
  isOpen : IsOpen U
  mem : z ∈ U
  holomorphicAt : ∀ p ∈ U, HolomorphicAt n y p
  generates : ∀ p ∈ U, ∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem p g ↔
    IsInSpanAt (n := n) (· = y) p g
  exists_ne_zero : ∀ V : Set Y, IsOpen V → V ⊆ U → V.Nonempty → ∃ p ∈ V, y p ≠ 0
  derivation : ∀ e' : ComplexChart n X, π z ∈ e'.val.source → ∀ v : ComplexModel n,
    ∃ b : Fin n → Y → ℂ, (∀ m, HolomorphicAt n (b m) z) ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => y p * chartDeriv e' v f (π p)) =ᶠ[𝓝 z] (fun p =>
          ∑ m, b m p * chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) (f ∘ π) p)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        (fun p => ∑ m, b m p *
          chartDeriv (complexChartAt (n := n) z) (EuclideanSpace.single m 1) y p)
          =ᶠ[𝓝 z] fun p => ρ p * y p

/-- **Away from the centre**: `y = 1`, and `W = e_x ∘ π` is a local coordinate system. -/
theorem isUniformDerivationGenerator_of_notMem (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∉ C) :
    IsUniformDerivationGenerator n π C z (π ⁻¹' Cᶜ) (fun _ => 1) := by
  classical
  have hπs := hπ.contMDiff
  have hUo : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπs.continuous
  refine ⟨hUo, hz, fun p _ => holomorphicAt_const 1, fun p hp g => ?_, fun V _ _ hV => ?_,
    fun e' hx' v => ?_⟩
  · constructor
    · intro hg
      exact isInSpanAt_of_eq_mul rfl hg.1 hg.1 (Eventually.of_forall fun q => by simp)
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      have h1 : (vanishingIdeal (n := n) C).mem (π p) (fun _ => 1) :=
        ⟨holomorphicAt_const 1, by
          filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hp] with q hq hqC
          exact absurd hqC hq⟩
      show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π)
        p g
      exact isInSpanAt_of_eq_mul ⟨fun _ => 1, h1, rfl⟩ hgh hc hgc
  · obtain ⟨p, hp⟩ := hV
    exact ⟨p, hp, one_ne_zero⟩
  · -- local coordinates `W = e_x ∘ π` at `z`
    set ex := complexChartAt (n := n) (π z) with hex
    set ez := complexChartAt (n := n) z with hez
    have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
    have hxs : π z ∈ ex.val.source := mem_complexChartAt_source (π z)
    set N := coordinateDomain π ez ex with hN
    have hNo : IsOpen N := coordinateDomain_isOpen hπs ez ex
    have hzN : ez.val z ∈ N := mem_coordinateDomain hzs hxs
    have hFd : DifferentiableOn ℂ ((fun p => ex.val (π p)) ∘ ez.val.symm) N := fun ζ hζ =>
      ((coordinateMap_contDiffAt hπs ez ex hζ).differentiableAt (by simp)).differentiableWithinAt
    have hinj : Function.Injective
        (fderiv ℂ ((fun p => ex.val (π p)) ∘ ez.val.symm) (ez.val z)) := by
      have hbij : Function.Bijective
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z) := by
        by_contra h
        exact hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
      have hd : DifferentiableAt ℂ (coordinateMap π ez ex) (ez.val z) :=
        (coordinateMap_contDiffAt hπs ez ex hzN).differentiableAt (by simp)
      refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
      have h0 : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z w = 0 := by
        rw [← BlowupFibreDirection.fderiv_coordinateMap_eq_mfderiv hπs z w]
        change fderiv ℝ (coordinateMap π ez ex) (ez.val z) w = 0
        rw [hd.fderiv_restrictScalars ℝ]
        exact hw
      exact (injective_iff_map_eq_zero
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z)).mp hbij.1 w h0
    have hT : ex.val (π z) ∈ ex.val.target := ex.val.map_source hxs
    obtain ⟨b, hb, hbeq, ρ, hρ, hρeq⟩ := derivationData_of_coordinates_uniform hπs ex hxs
      (idOn ex.val.target ex.val.open_target hT) hNo hzN hFd hinj (Ψ := id) differentiable_id
      (by
        filter_upwards [(hπs z).continuousAt.preimage_mem_nhds
          (ex.val.open_source.mem_nhds hxs)] with p hp
        exact ⟨hp, ex.val.map_source hp, rfl⟩)
      (Q := fun _ => 1) (differentiable_const 1)
      (P := fun i l _ => if i = l then 1 else 0) (fun i l => differentiable_const _)
      (fun F w _ i => by simp [Finset.sum_ite_eq])
      (R := fun _ _ => 0) (fun _ => differentiable_const 0)
      (fun i w => by simp)
      e' hx' v
    exact ⟨b, hb, hbeq, ρ, hρ, hρeq⟩

/-- **Over the centre**: in a monomial chart `j` with local inverse `W` (`σⱼ ∘ W = Φ ∘ e_x ∘ π`),
`y = Wⱼ` generates `π^*𝓘_C` and `y σ^*(Der)` is the derivation `wⱼ σⱼ^*(∂)` of the source. -/
theorem exists_isUniformDerivationGenerator_of_mem (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∈ C) :
    ∃ (U : Set Y) (y : Y → ℂ), IsUniformDerivationGenerator n π C z U y := by
  classical
  have hπs := hπ.contMDiff
  obtain ⟨k, hk⟩ := hπ.1.2 (π z) hz
  obtain ⟨-, -, Φ, hΦt, -, hflat⟩ := hk
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    BlowupLocalSurjectivity.exists_monomialLocalInverse hπ hΦt hflat hz'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ hΦt hflat hj
  -- the coordinate reading of `W` at `z`
  set ez := chartAt (ComplexModel n) z with hez
  set Nset : Set (ComplexModel n) := ez.target ∩ ez.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := ez.continuousOn_symm.isOpen_inter_preimage ez.open_target hO
  have hzN : ez z ∈ Nset :=
    ⟨ez.map_source (mem_chart_source _ z), by
      show ez.symm (ez z) ∈ O
      rw [ez.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ (W ∘ ez.symm) Nset := by
    intro ζ hζ
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) hζ.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (ez.symm ζ) :=
      (hWs _ hζ.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)).differentiableWithinAt
  have hFinj : Function.Injective (fderiv ℂ (W ∘ ez.symm) (ez z)) := by
    have hdiff : DifferentiableAt ℂ (W ∘ ez.symm) (ez z) :=
      (hFd _ hzN).differentiableAt (hNo.mem_nhds hzN)
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply BlowupFibreDirection.fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs
      (hℓ ℓ hℓs hℓπ) hzO hv0
    rw [show (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) = W ∘ ez.symm from rfl,
      hdiff.fderiv_restrictScalars ℝ]
    exact hv
  -- `Wⱼ = (flat coordinate j) ∘ π` on `O`
  have hWj : ∀ q ∈ O, W q j = flatCoord Φ j (π q) := fun q hq => by
    show W q j = Φ.toFun (chartAt (ComplexModel n) (π z) (π q)) j
    rw [← (hWeq q hq).2, monomial_apply]
    simp
  have hyhol : ∀ q ∈ O, HolomorphicAt n (fun p => W p j) q := fun q hq => by
    filter_upwards [hO.mem_nhds hq] with q' hq'
    exact (((EuclideanSpace.proj (𝕜 := ℂ) j : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
      q' (hWs q' hq')).mdifferentiableAt (by simp))
  refine ⟨O, fun p => W p j, ⟨hO, hzO, hyhol, fun p hp g => ?_, fun V hVo hVO hV => ?_,
    fun e' hx' v => ?_⟩⟩
  · -- `Wⱼ` generates `π^*𝓘_C` on `O`
    constructor
    · intro hg
      refine IsInSpanAt.of_forall_eq_mul ?_ (show IsInSpanAt (n := n)
        (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π) p g from hg)
      rintro s ⟨a, ha, rfl⟩
      obtain ⟨bb, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦt hflat (hWeq p hp).1 ha
      refine ⟨fun q => ∑ i, bb i (π q) * (if i = j then 1 else W q i), ?_, ?_⟩
      · refine HolomorphicAt.sum _ fun i _ => ?_
        refine ((hbh i).comp_contMDiff (Eventually.of_forall fun q => hπs q)).mul ?_
        split_ifs
        · exact holomorphicAt_const 1
        · filter_upwards [hO.mem_nhds hp] with q' hq'
          exact (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
            q' (hWs q' hq')).mdifferentiableAt (by simp))
      · filter_upwards [(hπs p).continuousAt.eventually hbeq, hO.mem_nhds hp] with q hq hqO
        simp only [Function.comp_apply, hq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfc : flatCoord Φ i (π q) = monomial k j (W q) i := by
          show Φ.toFun (chartAt (ComplexModel n) (π z) (π q)) i = _
          rw [← (hWeq q hqO).2]
        rw [hfc, monomial_apply]
        by_cases hki : k ≤ i.1
        · by_cases hij : i = j
          · subst hij; simp
          · simp [hki, hij]; ring
        · have : bb i = 0 := hb0 i (by omega)
          simp [this]
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π)
        p g
      refine isInSpanAt_of_eq_mul ⟨flatCoord Φ j,
        flatCoord_mem_vanishingIdeal Φ hflat hj (hWeq p hp).1, rfl⟩ hgh hc ?_
      filter_upwards [hgc, hO.mem_nhds hp] with q hq hqO
      rw [hq, Function.comp_apply, hWj q hqO]
  · -- `Wⱼ` vanishes identically on no nonempty open subset of `O`
    by_contra hall
    push Not at hall
    have hsub : V ⊆ π ⁻¹' C := fun p hp => by
      have hpO := hVO hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hWeq p hpO
      refine (hflat hp1 hp2).mpr ?_
      change Φ.toFun (chartAt (ComplexModel n) (π z) (π p)) ∈ _
      rw [← hp3]
      intro i hi
      rw [monomial_apply, hall p hp]
      split_ifs with h
      · ring
      · have : i = j := by by_contra hne; exact h ⟨hi, hne⟩
        rw [this, hall p hp]
    have := interior_maximal hsub hVo
    rw [ExceptionalFibres.interior_preimage_eq_empty hπ] at this
    obtain ⟨p, hp⟩ := hV
    exact this hp
  · -- the derivation `wⱼ σⱼ^*(∂)`
    have hΦW : ∀ᶠ p in 𝓝 z, π p ∈ (complexChartAt (n := n) (π z)).val.source ∧
        (complexChartAt (n := n) (π z)).val (π p) ∈ Φ.source ∧
        Φ.toFun ((complexChartAt (n := n) (π z)).val (π p)) = monomial k j (W p) := by
      filter_upwards [hO.mem_nhds hzO] with p hp
      exact ⟨(hWeq p hp).1.1, (hWeq p hp).1.2, (hWeq p hp).2.symm⟩
    have hproj : ∀ w : ComplexModel n, ∀ l : Fin n,
        fderiv ℂ (fun w : ComplexModel n => w j) w (EuclideanSpace.single l 1) =
          if l = j then 1 else 0 := fun w l => by
      have h : (fun w : ComplexModel n => w j) = ⇑(EuclideanSpace.proj (𝕜 := ℂ) j) := by
        funext w; rfl
      rw [h, ContinuousLinearMap.fderiv]
      simp [PiLp.single_apply, eq_comm]
    obtain ⟨b, hb, hbeq, ρ, hρ, hρeq⟩ := derivationData_of_coordinates_uniform hπs
      (complexChartAt (n := n) (π z)) (mem_complexChartAt_source _) Φ hNo hzN hFd hFinj
      (Ψ := monomial k j) ((contDiff_monomial k j).differentiable (by simp)) hΦW
      (Q := fun w => w j) (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable
      (P := monomialCoeff k j) (differentiable_monomialCoeff k j)
      (fun F w hF i => mul_fderiv_monomial hj hF i)
      (R := fun i _ => if i = j then 1 else 0) (fun i => differentiable_const _)
      (fun i w => by
        simp only [hproj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, monomialCoeff_self]
        split_ifs <;> simp)
      e' hx' v
    exact ⟨b, hb, hbeq, ρ, hρ, hρeq⟩

/-- At every point of the blowup the data of `y σ^*(Der)` exist. -/
theorem exists_isUniformDerivationGenerator (hπ : IsBlowupAlong n C π) (z : Y) :
    ∃ (U : Set Y) (y : Y → ℂ), IsUniformDerivationGenerator n π C z U y := by
  by_cases hz : π z ∈ C
  · exact exists_isUniformDerivationGenerator_of_mem hπ hz
  · exact ⟨_, _, isUniformDerivationGenerator_of_notMem hπ hz⟩

end PointData

/-! ### The lifted derivation is tangent to the strict transform -/

section Tangent

open DerivativeIdealAlong DerivativeIdealAlongCoherent BlowupStrictSubmanifold

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {z : Y} {U : Set Y} {y : Y → ℂ}

/-- The generator `y` of `𝒪(-D)` does not vanish off `D`. -/
theorem IsUniformDerivationGenerator.ne_zero (hπ : IsBlowupAlong n C π)
    (hy : IsUniformDerivationGenerator n π C z U y) {p : Y} (hp : p ∈ U) (hpC : π p ∉ C) : y p ≠ 0 := by
  have h1 : (vanishingIdeal (n := n) C).mem (π p) (fun _ => 1) :=
    ⟨holomorphicAt_const 1, by
      filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hpC] with q hq hqC
      exact absurd hqC hq⟩
  have h2 : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem p (fun _ => 1) := by
    show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π) p
      (fun _ => 1)
    exact isInSpanAt_of_eq_mul ⟨fun _ => 1, h1, rfl⟩ (holomorphicAt_const 1) (holomorphicAt_const 1)
      (Eventually.of_forall fun q => by simp)
  obtain ⟨-, c, -, hc⟩ := isInSpanAt_eq_iff.mp ((hy.generates p hp _).mp h2)
  intro h0
  have := hc.self_of_nhds
  simp [h0] at this

/-- **Cancellation of `y^q` on the strict transform**: the points of `π⁻¹(N \ C)`, where `y ≠ 0`, are dense in
`N' = closure (π⁻¹(N \ C))`; so if `y^q g = y^q G` on `N'` near `z`, with `g`, `G` continuous near `z`, then `g = G` on
`N'` near `z`. -/
theorem eventually_eq_on_of_pow_mul (hπ : IsBlowupAlong n C π) {N : Set X}
    (hy : IsUniformDerivationGenerator n π C z U y) (q : ℕ) {g G : Y → ℂ}
    (hg : ∀ᶠ p in 𝓝 z, ContinuousAt g p) (hG : ∀ᶠ p in 𝓝 z, ContinuousAt G p)
    (h : ∀ᶠ p in 𝓝 z, p ∈ geoStrictTransform π C N → y p ^ q * g p = y p ^ q * G p) :
    ∀ᶠ p in 𝓝 z, p ∈ geoStrictTransform π C N → g p = G p := by
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.mp ((hg.and hG).and (h.and (hy.isOpen.mem_nhds hy.mem)))
  filter_upwards [hVo.mem_nhds hzV] with p hp hpN
  by_contra hne
  have hcont : ContinuousAt (fun p => g p - G p) p := (hV p hp).1.1.sub (hV p hp).1.2
  have hopen : ∀ᶠ p' in 𝓝 p, g p' - G p' ≠ 0 :=
    hcont.eventually (isOpen_ne.mem_nhds (sub_ne_zero.mpr hne))
  obtain ⟨p', ⟨hp'ne, hp'V⟩, hp'NC⟩ := mem_closure_iff_nhds.mp hpN _ (hopen.and (hVo.mem_nhds hp))
  have hp'N : p' ∈ geoStrictTransform π C N := subset_closure hp'NC
  have h1 := (hV p' hp'V).2.1 hp'N
  have hy' := hy.ne_zero hπ (hV p' hp'V).2.2 hp'NC.2
  have h2 : y p' ^ q * (g p' - G p') = 0 := by rw [mul_sub, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hy' (pow_eq_zero_iff'.mp h3).1
  · exact hp'ne h3

/-- **The lift of a field tangent to `N` is tangent to `N'`** (`N ⊇ C` a closed submanifold, `z ∈ N'`): if `ξ` is
tangent to `N` at `π z`, the derivation `D' = ∑ₗ Bₗ ∂_l` with `y · (ξ f) ∘ π = D'(f ∘ π)` for every `f` (uniform
data) is tangent to `N'` at `z`, and `D'(y) ∈ (y)`. For `w ∈ 𝓘_{N'}`, `y w ∈ 𝒪(-D) 𝓘_{N'} = π^*𝓘_N`
(`BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul`), so `y w = ∑ cᵢ (tᵢ ∘ π)` with `tᵢ ∈ 𝓘_N`; then `ρ y w + y
D'(w) = D'(y w) = ∑ D'(cᵢ) (tᵢ ∘ π) + cᵢ y (ξ tᵢ) ∘ π` vanishes on `N'`, so `y D'(w) = 0` on `N'` and `D'(w) = 0` on
`N'` by density. -/
theorem exists_tangent_lift (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N)
    (hy : IsUniformDerivationGenerator n π C z U y) {e : ComplexChart n X} {ξ : Fin n → X → ℂ}
    (hξ : IsTangentField N e ξ (π z)) :
    ∃ B : Fin n → Y → ℂ, IsTangentField (geoStrictTransform π C N) (complexChartAt (n := n) z) B z ∧
      (∀ f : X → ℂ, HolomorphicAt n f (π z) →
        (fun p => y p * fieldDeriv e ξ f (π p)) =ᶠ[𝓝 z] fieldDeriv (complexChartAt (n := n) z) B (f ∘ π)) ∧
      ∃ ρ : Y → ℂ, HolomorphicAt n ρ z ∧
        fieldDeriv (complexChartAt (n := n) z) B y =ᶠ[𝓝 z] fun p => ρ p * y p := by
  classical
  set ez := complexChartAt (n := n) z with hez
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  have hπs := hπ.contMDiff
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  choose b hb hbeq ρ hρ hρeq using fun m : Fin n =>
    hy.derivation e hξ.mem_source (EuclideanSpace.single m 1)
  have hξπ : ∀ m, HolomorphicAt n (fun p => ξ m (π p)) z := fun m =>
    (hξ.holomorphicAt m).comp_contMDiff (Eventually.of_forall fun p => hπs p)
  set B : Fin n → Y → ℂ := fun l p => ∑ m, ξ m (π p) * b m l p with hB
  have hBhol : ∀ l, HolomorphicAt n (B l) z := fun l =>
    HolomorphicAt.sum _ fun m _ => (hξπ m).mul (hb m l)
  have hlift : ∀ f : X → ℂ, HolomorphicAt n f (π z) →
      (fun p => y p * fieldDeriv e ξ f (π p)) =ᶠ[𝓝 z] fieldDeriv ez B (f ∘ π) := by
    intro f hf
    filter_upwards [eventually_all.2 fun m => hbeq m f hf] with p hp
    have hp' : ∀ m, y p * chartDeriv e (EuclideanSpace.single m 1) f (π p) =
        ∑ l, b m l p * chartDeriv ez (EuclideanSpace.single l 1) (f ∘ π) p := fun m => hp m
    simp only [fieldDeriv, hB, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show y p * (ξ m (π p) * chartDeriv e (EuclideanSpace.single m 1) f (π p)) =
      ξ m (π p) * (y p * chartDeriv e (EuclideanSpace.single m 1) f (π p)) by ring, hp' m, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  set ρ' : Y → ℂ := fun p => ∑ m, ξ m (π p) * ρ m p with hρ'
  have hρ'hol : HolomorphicAt n ρ' z := HolomorphicAt.sum _ fun m _ => (hξπ m).mul (hρ m)
  have hρ'eq : fieldDeriv ez B y =ᶠ[𝓝 z] fun p => ρ' p * y p := by
    filter_upwards [eventually_all.2 hρeq] with p hp
    have hp' : ∀ m, ∑ l, b m l p * chartDeriv ez (EuclideanSpace.single l 1) y p = ρ m p * y p :=
      fun m => hp m
    simp only [fieldDeriv, hB, hρ', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show ξ m (π p) * ρ m p * y p = ξ m (π p) * (ρ m p * y p) by ring, ← hp' m, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨B, ⟨hzs, hBhol, fun w hw => ⟨holomorphicAt_fieldDeriv hzs hBhol hw.1, ?_⟩⟩, hlift, ρ', hρ'hol,
    hρ'eq⟩
  -- `y w ∈ π^*𝓘_N`
  have hymem : (exceptionalDivisor hπ).ideal.mem z y :=
    (hy.generates z hy.mem y).mpr (isInSpanAt_of_eq_mul rfl hyz (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp))
  have hyw : ((exceptionalDivisor hπ).ideal.mul
      (vanishingIdeal (n := n) (geoStrictTransform π C N))).mem z (fun p => y p * w p) := by
    show IsInSpanAt (n := n) (fun s => ∃ a b, (exceptionalDivisor hπ).ideal.mem z a ∧
      (vanishingIdeal (n := n) (geoStrictTransform π C N)).mem z b ∧ s = a * b) z (fun p => y p * w p)
    exact isInSpanAt_of_eq_mul ⟨y, w, hymem, hw, rfl⟩ (hyz.mul hw.1) (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  rw [← BlowupStrictIdeal.pullback_vanishingIdeal_eq_mul hπ hN hCN] at hyw
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hyw
  choose t ht hst using hs
  have htπ : ∀ i, HolomorphicAt n (fun p => t i (π p)) z := fun i =>
    (ht i).1.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  have hsum' : (fun p => y p * w p) =ᶠ[𝓝 z] fun p => ∑ i, c i p * t i (π p) := by
    filter_upwards [hsum] with p hp
    rw [hp]
    exact Finset.sum_congr rfl fun i _ => by rw [hst i]; rfl
  have h1 := fieldDeriv_eventuallyEq_sum_mul (ξ := B) (K := 1) (a := fun _ => y) (s := fun _ => w)
    (f := fun p => y p * w p) hzs (fun _ => hyz) (fun _ => hw.1) (Eventually.of_forall fun p => by simp)
  have h2 := fieldDeriv_eventuallyEq_sum_mul (ξ := B) (f := fun p => y p * w p) hzs hc htπ hsum'
  have h3 : ∀ i, fieldDeriv ez B (fun p => t i (π p)) =ᶠ[𝓝 z]
      fun p => y p * fieldDeriv e ξ (t i) (π p) := fun i => (hlift (t i) (ht i).1).symm
  have ht0 : ∀ i, ∀ᶠ p in 𝓝 z, p ∈ geoStrictTransform π C N → t i (π p) = 0 := fun i => by
    filter_upwards [hπc.eventually (ht i).2] with p hp hpN
    exact hp (geoStrictTransform_subset_preimage hπs.continuous hN.1 hpN)
  have hξt0 : ∀ i, ∀ᶠ p in 𝓝 z, p ∈ geoStrictTransform π C N → fieldDeriv e ξ (t i) (π p) = 0 := fun i => by
    filter_upwards [hπc.eventually (hξ.preserves (t i) (ht i)).2] with p hp hpN
    exact hp (geoStrictTransform_subset_preimage hπs.continuous hN.1 hpN)
  have hkey : ∀ᶠ p in 𝓝 z, p ∈ geoStrictTransform π C N →
      y p ^ 1 * fieldDeriv ez B w p = y p ^ 1 * 0 := by
    filter_upwards [h1, h2, eventually_all.2 h3, eventually_all.2 ht0, eventually_all.2 hξt0, hw.2, hρ'eq]
      with p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hpN
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hp1
    have hsum0 : ∑ i, (fieldDeriv ez B (c i) p * t i (π p) + c i p * fieldDeriv ez B (fun p => t i (π p)) p) =
        0 := Finset.sum_eq_zero fun i _ => by rw [hp4 i hpN, hp3 i, hp5 i hpN]; ring
    rw [hp2, hsum0, hp7, hp6 hpN] at hp1
    simp only [pow_one, mul_zero]
    linear_combination -hp1
  have hcont : ∀ᶠ p in 𝓝 z, ContinuousAt (fieldDeriv ez B w) p :=
    (holomorphicAt_fieldDeriv hzs hBhol hw.1).eventually.mono fun p hp => hp.continuousAt
  filter_upwards [eventually_eq_on_of_pow_mul hπ hy 1 hcont (Eventually.of_forall fun p => continuousAt_const)
    hkey] with p hp hpN
  exact hp hpN

end Tangent

/-! ### `le:inclusions` along `N`, one derivative -/

section Inclusion

open DerivativeIdealAlong DerivativeIdealAlongCoherent BlowupStrictSubmanifold RestrictedIdealExtension RestrictedIdealQuotient RestrictedIdealWeight RelativePrincipalizationSpan

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Power rule along a vector field: `ξ(y^{q+1}) = (q+1) y^q ξ(y)`. -/
theorem fieldDeriv_pow {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {y : M → ℂ} {p₀ : M}
    (hp₀ : p₀ ∈ e.val.source) (hy : HolomorphicAt n y p₀) (q : ℕ) :
    fieldDeriv e ξ (fun p => y p ^ (q + 1)) =ᶠ[𝓝 p₀] fun p => ((q : ℂ) + 1) * y p ^ q * fieldDeriv e ξ y p := by
  filter_upwards [eventually_all.2 fun m => chartDeriv_pow (v := EuclideanSpace.single m 1) hp₀ hy q] with p hp
  simp only [fieldDeriv, hp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- A vector field kills constants. -/
theorem fieldDeriv_const (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (c : ℂ) (p : M) :
    fieldDeriv e ξ (fun _ => c) p = 0 := by
  simp [fieldDeriv, chartDeriv, Function.comp_def]

/-- Derivative of `f = ∑ aₖ sₖ + t` (`t = f - ∑ aₖ sₖ`) along a field. -/
theorem fieldDeriv_eventuallyEq_add_sum {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M} {f : M → ℂ}
    (hx : x ∈ e.val.source) {K : ℕ} {a s : Fin K → M → ℂ} (ha : ∀ k, HolomorphicAt n (a k) x)
    (hs : ∀ k, HolomorphicAt n (s k) x) (hf : HolomorphicAt n f x) :
    fieldDeriv e ξ f =ᶠ[𝓝 x] fun p => ∑ k, (fieldDeriv e ξ (a k) p * s k p + a k p * fieldDeriv e ξ (s k) p) +
      fieldDeriv e ξ (fun q => f q - ∑ k, a k q * s k q) p := by
  have hS : HolomorphicAt n (fun q => ∑ k, a k q * s k q) x := HolomorphicAt.sum _ fun k _ => (ha k).mul (hs k)
  have ht : HolomorphicAt n (fun q => f q - ∑ k, a k q * s k q) x := GiraudAlong.holomorphicAt_sub hf hS
  have h2 := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ) (K := 2) (a := ![fun _ => 1, fun _ => 1])
    (s := ![fun q => ∑ k, a k q * s k q, fun q => f q - ∑ k, a k q * s k q]) (f := f) hx
    (fun i => by fin_cases i <;> simp [holomorphicAt_const]) (fun i => by fin_cases i <;> simp [hS, ht])
    (Eventually.of_forall fun p => by simp [Fin.sum_univ_two])
  have h1 := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ) (f := fun q => ∑ k, a k q * s k q) hx ha hs
    (Eventually.of_forall fun p => rfl)
  filter_upwards [h1, h2] with p hp1 hp2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, fieldDeriv_const, zero_mul, one_mul,
    zero_add] at hp2
  rw [hp2, hp1]

/-- A field lowers the power of an ideal of holomorphic germs by at most one. -/
theorem fieldDeriv_mem_idealPow {𝔟 : GermIdeal n M} (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y)
    {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {x : M} (hx : x ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) x)
    {q : ℕ} {g : M → ℂ} (hg : (idealPow 𝔟 (q + 1)).mem x g) : (idealPow 𝔟 q).mem x (fieldDeriv e ξ g) :=
  mem_idealPow_of_isInSpanAt (IsInSpanAt.sum _ fun m _ => IsInSpanAt.mul_left (hξ m)
    (InvertibleIdealQuotient.isInSpanAt_self (chartDeriv_mem_idealPow' h𝔟 hx q g hg)
      (holomorphicAt_chartDeriv hx (holomorphicAt_of_mem_idealPow hg))))

/-- `RestrictLe` is reflexive on ideals of holomorphic germs. -/
theorem restrictLe_refl {W : Set M} {𝔟 : GermIdeal n M} (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y) :
    RestrictLe W 𝔟 𝔟 := fun x _ g hg =>
  IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg (h𝔟 x g hg))

/-- `RestrictLe` is transitive. -/
theorem restrictLe_trans {W : Set M} {𝔞 𝔟 𝔠 : GermIdeal n M} (h₁ : RestrictLe W 𝔞 𝔟) (h₂ : RestrictLe W 𝔟 𝔠) :
    RestrictLe W 𝔞 𝔠 := fun x hx g hg =>
  IsInSpanOnAt.trans (fun s hs => h₂ x hx s hs) (h₁ x hx g hg)

/-- **Derivatives along `N` lower the restricted power of `𝓘_C` by one**: `𝔞|_N ⊆ 𝓘_C^{q+1}|_N` implies
`𝓓_N(𝔞)|_N ⊆ 𝓘_C^q|_N` (`𝔞 = ∑ aₖ hₖ + t` with `hₖ ∈ 𝓘_C^{q+1}` and `t ∈ 𝓘_N`; a field tangent to `N` keeps `t` in
`𝓘_N`). -/
theorem restrictLe_derivIdealAlong_idealPow {N C : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {q : ℕ}
    (hle : RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (q + 1))) :
    RestrictLe N (derivIdealAlong N 𝔞) (idealPow (vanishingIdeal (n := n) C) q) := by
  have hC : ∀ y g, (vanishingIdeal (n := n) C).mem y g → HolomorphicAt n g y := fun _ _ h => h.1
  intro x hx u hu
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hu)
  rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact IsInSpanOnAt.mono (fun s hs => idealPow_succ_le hC q x s hs) (hle x hx σ hσ)
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    filter_upwards [hσ.2] with p hp hpN
    simp [hp hpN]
  · obtain ⟨K, h, a, hh, ha, hsum⟩ := hle x hx f hf
    have hhhol : ∀ k, HolomorphicAt n (h k) x := fun k => holomorphicAt_of_mem_idealPow (hh k)
    have htN : (vanishingIdeal (n := n) N).mem x (fun q => f q - ∑ k, a k q * h k q) :=
      ⟨GiraudAlong.holomorphicAt_sub (h𝔞 x f hf) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hhhol k)), by
        filter_upwards [hsum] with p hp hpN
        rw [hp hpN, sub_self]⟩
    have hmem : (idealPow (vanishingIdeal (n := n) C) q).mem x
        (fun p => ∑ k, (fieldDeriv e ξ (a k) p * h k p + a k p * fieldDeriv e ξ (h k) p)) := by
      refine mem_idealPow_of_isInSpanAt (IsInSpanAt.sum _ fun k _ => IsInSpanAt.add ?_ ?_)
      · exact IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (ha k))
          (InvertibleIdealQuotient.isInSpanAt_self (idealPow_succ_le hC q x _ (hh k)) (hhhol k))
      · have h1 := fieldDeriv_mem_idealPow hC hξ.mem_source hξ.holomorphicAt (hh k)
        exact IsInSpanAt.mul_left (ha k) (InvertibleIdealQuotient.isInSpanAt_self h1
          (holomorphicAt_of_mem_idealPow h1))
    refine IsInSpanOnAt.congr_right (IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem
      (holomorphicAt_of_mem_idealPow hmem))) ?_
    filter_upwards [fieldDeriv_eventuallyEq_add_sum (ξ := ξ) hξ.mem_source ha hhhol (h𝔞 x f hf),
      (hξ.preserves _ htN).2] with p hp1 hp2 hpN
    rw [hp1, hp2 hpN, add_zero]

/-- Iterated: `𝔞|_N ⊆ 𝓘_C^{q+r}|_N` implies `𝓓_N^r(𝔞)|_N ⊆ 𝓘_C^q|_N`. -/
theorem restrictLe_iterDerivIdealAlong_idealPow {N C : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {q : ℕ} :
    ∀ r, RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (q + r)) →
      RestrictLe N (iterDerivIdealAlong N 𝔞 r) (idealPow (vanishingIdeal (n := n) C) q)
  | 0, hle => hle
  | r + 1, hle => by
    refine restrictLe_derivIdealAlong_idealPow (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 r)
      (restrictLe_iterDerivIdealAlong_idealPow h𝔞 r ?_)
    rwa [show q + 1 + r = q + (r + 1) by omega]

/-- **`𝓓_W` respects restricted inclusions**: `𝔟₁|_W ⊆ 𝔟₂|_W` implies `𝓓_W(𝔟₁)|_W ⊆ 𝓓_W(𝔟₂)|_W` (for `f = ∑ aₖ gₖ + t`
with `gₖ ∈ 𝔟₂` and `t ∈ 𝓘_W`, a field tangent to `W` gives `ξ f = ∑ ξ(aₖ) gₖ + aₖ ξ(gₖ) + ξ(t)`, `ξ(t) ∈ 𝓘_W`). -/
theorem restrictLe_derivIdealAlong {W : Set M} {𝔟₁ 𝔟₂ : GermIdeal n M}
    (h₁ : ∀ y g, 𝔟₁.mem y g → HolomorphicAt n g y) (h₂ : ∀ y g, 𝔟₂.mem y g → HolomorphicAt n g y)
    (h : RestrictLe W 𝔟₁ 𝔟₂) : RestrictLe W (derivIdealAlong W 𝔟₁) (derivIdealAlong W 𝔟₂) := by
  intro x hx u hu
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hu)
  rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact IsInSpanOnAt.mono (fun s hs => le_derivIdealAlong h₂ x s hs) (h x hx σ hσ)
  · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self
      (vanishingIdeal_le_derivIdealAlong x σ hσ) hσ.1)
  · obtain ⟨K, g, a, hg, ha, hsum⟩ := h x hx f hf
    have hghol : ∀ k, HolomorphicAt n (g k) x := fun k => h₂ x _ (hg k)
    have htW : (vanishingIdeal (n := n) W).mem x (fun q => f q - ∑ k, a k q * g k q) :=
      ⟨GiraudAlong.holomorphicAt_sub (h₁ x f hf) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hghol k)), by
        filter_upwards [hsum] with p hp hpW
        rw [hp hpW, sub_self]⟩
    have hgen : ∀ s, DerivGenAlong W 𝔟₂ x s → (derivIdealAlong W 𝔟₂).mem x s := fun s hs =>
      InvertibleIdealQuotient.isInSpanAt_self hs (by
        rcases hs with hs | hs | ⟨e', ξ', f', hξ', hf', rfl⟩
        · exact h₂ x s hs
        · exact hs.1
        · exact holomorphicAt_fieldDeriv hξ'.mem_source hξ'.holomorphicAt (h₂ x f' hf'))
    have hmem : (derivIdealAlong W 𝔟₂).mem x (fun p => ∑ k, (fieldDeriv e ξ (a k) p * g k p +
        a k p * fieldDeriv e ξ (g k) p) + fieldDeriv e ξ (fun q => f q - ∑ k, a k q * g k q) p) := by
      refine IsInSpanAt.add (IsInSpanAt.sum _ fun k _ => IsInSpanAt.add ?_ ?_) ?_
      · exact IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (ha k))
          (InvertibleIdealQuotient.isInSpanAt_self (Or.inl (hg k)) (hghol k))
      · exact IsInSpanAt.mul_left (ha k) (InvertibleIdealQuotient.isInSpanAt_self
          (Or.inr (Or.inr ⟨e, ξ, g k, hξ, hg k, rfl⟩))
          (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (hghol k)))
      · exact InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inl (hξ.preserves _ htW)))
          (hξ.preserves _ htW).1
    have hξf : HolomorphicAt n (fieldDeriv e ξ f) x :=
      holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt (h₁ x f hf)
    have heq := fieldDeriv_eventuallyEq_add_sum (ξ := ξ) hξ.mem_source ha hghol (h₁ x f hf)
    have hmem' : (derivIdealAlong W 𝔟₂).mem x (fieldDeriv e ξ f) := isInSpanAt_congr hmem heq.symm
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem' hξf)

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`le:inclusions` along a submanifold, one derivative** (Włodarczyk 2005, Lemma `le:inclusions`, for the ideal
`𝔞|_N` of `𝒪_N`; Bierstone--Milman 2008, Lemmas 3.1--3.3): let `N ⊇ C` be a closed submanifold, `N'` its strict
transform, and `𝔞|_N ⊆ 𝓘_C^{μ+1}|_N`.  Then on `N'`
`(π^* 𝓓_N(𝔞) : 𝒪(-μD))|_{N'} ⊆ 𝓓_{N'}((π^*𝔞 : 𝒪(-(μ+1)D))|_{N'})`, the colons taken along `N'` as in the transform of a
marked ideal (`MarkedIdeal.geoTransform`).  At `z ∈ N'` with `y` a generator of `𝒪(-D)`: every `s ∈ 𝔞_{π z}` is
`s ∘ π = y^{μ+1} H + t ∘ π` with `H` in the transform and `t ∈ 𝓘_N` (from `𝔞 ⊆ 𝓘_C^{μ+1}` on `N`); for a generator
`ξ(f)` of `𝓓_N(𝔞)` (`ξ` tangent to `N`) the tangent lift `D'` gives `y (ξ f) ∘ π = D'(f ∘ π) =
y^{μ+1}((μ+1) ρ H + D'(H))` on `N'`; then `y^{μ+1}` is cancelled on `N'` (`eventually_eq_on_of_pow_mul`). -/
theorem restrictLe_colonAlong_derivIdealAlong (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {𝔞 : GermIdeal n X}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ}
    (hle : RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (μ + 1))) :
    RestrictLe (geoStrictTransform π C N)
      (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π (derivIdealAlong N 𝔞))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) μ))
      (derivIdealAlong (geoStrictTransform π C N)
        (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (μ + 1)))) := by
  classical
  intro z hzN g hg
  set N' := geoStrictTransform π C N with hN'
  set J := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with hJ
  set 𝔠 := colonAlong n N' (GermIdeal.pullback (m := n) π 𝔞) (idealPow J (μ + 1)) with h𝔠
  set ez := complexChartAt (n := n) z with hez
  have hπs := hπ.contMDiff
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have hπat : ∀ᶠ p in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π p :=
    Eventually.of_forall fun p => (hπs p).mdifferentiableAt (by simp)
  have hcomp : ∀ {f : X → ℂ}, HolomorphicAt n f (π z) → HolomorphicAt n (fun p => f (π p)) z := fun hf =>
    hf.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  have hxN : π z ∈ N := geoStrictTransform_subset_preimage hπs.continuous hN.1 hzN
  obtain ⟨U, y, hy⟩ := exists_isUniformDerivationGenerator hπ z
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  have hpow : ∀ q, ∀ p ∈ U, ∀ g, (idealPow J q).mem p g ↔
      IsInSpanAt (n := n) (· = fun p => y p ^ q) p g :=
    idealPow_mem_iff_of_generator hy.holomorphicAt hy.generates
  have hpow_self : ∀ q, (idealPow J q).mem z (fun p => y p ^ q) := fun q =>
    (hpow q z hy.mem _).mpr (isInSpanAt_of_eq_mul rfl (holomorphicAt_pow hyz q) (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp))
  have h𝔠hol : ∀ p H, 𝔠.mem p H → HolomorphicAt n H p := fun _ _ hH => hH.1
  -- pullbacks of germs vanishing on `N` vanish on `N'`
  have hvan : ∀ t, (vanishingIdeal (n := n) N).mem (π z) t →
      ∀ᶠ p in 𝓝 z, p ∈ N' → t (π p) = 0 := fun t ht => by
    filter_upwards [hπc.eventually ht.2] with p hp hpN
    exact hp (geoStrictTransform_subset_preimage hπs.continuous hN.1 hpN)
  -- Claim C: `s ∘ π = y^{μ+1} H + t ∘ π` with `H ∈ 𝔠` and `t ∈ 𝓘_N`
  have hC : ∀ s, 𝔞.mem (π z) s → ∃ H t, 𝔠.mem z H ∧ (vanishingIdeal (n := n) N).mem (π z) t ∧
      (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p + t (π p) := by
    intro s hs
    obtain ⟨K, h, a, hh, ha, hsum⟩ := hle (π z) hxN s hs
    have hhhol : ∀ k, HolomorphicAt n (h k) (π z) := fun k => holomorphicAt_of_mem_idealPow (hh k)
    set t : X → ℂ := fun q => s q - ∑ k, a k q * h k q with ht
    have hthol : HolomorphicAt n t (π z) :=
      GiraudAlong.holomorphicAt_sub (h𝔞 _ _ hs) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hhhol k))
    have htN : (vanishingIdeal (n := n) N).mem (π z) t := ⟨hthol, by
      filter_upwards [hsum] with q hq hqN
      simp only [ht, hq hqN, sub_self]⟩
    have hHk : ∀ k, ∃ Hk : Y → ℂ, HolomorphicAt n Hk z ∧
        (fun p => h k (π p)) =ᶠ[𝓝 z] fun p => Hk p * y p ^ (μ + 1) := by
      intro k
      have h1 : (GermIdeal.pullback (m := n) π (idealPow (vanishingIdeal (n := n) C) (μ + 1))).mem z
          (fun p => h k (π p)) :=
        comp_mem_pullback (hh k) (hcomp (hhhol k)) (holomorphicAt_const 1)
          (Eventually.of_forall fun p => by simp)
      have h2 := pullback_le_idealPow_exceptionalDivisor hπ (fun _ _ h => h) z _ h1
      obtain ⟨-, Hk, hHk, hHkeq⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem _).mp h2)
      exact ⟨Hk, hHk, hHkeq⟩
    choose Hk hHk hHkeq using hHk
    set H : Y → ℂ := fun p => ∑ k, a k (π p) * Hk k p with hHdef
    have hHhol : HolomorphicAt n H z := HolomorphicAt.sum _ fun k _ => (hcomp (ha k)).mul (hHk k)
    have hsH : (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p + t (π p) := by
      filter_upwards [eventually_all.2 hHkeq] with p hp
      have e1 : ∑ k, a k (π p) * h k (π p) = y p ^ (μ + 1) * H p := by
        simp only [hHdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hp k]; ring
      simp only [ht, e1]
      ring
    have hsπ : (GermIdeal.pullback (m := n) π 𝔞).mem z (fun p => s (π p)) :=
      comp_mem_pullback hs (hcomp (h𝔞 _ _ hs)) (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp)
    refine ⟨H, t, ⟨hHhol, fun ℓ hℓ => ⟨(holomorphicAt_of_mem_idealPow hℓ).mul hHhol, ?_⟩⟩, htN, hsH⟩
    obtain ⟨-, d, hd, hℓd⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem ℓ).mp hℓ)
    refine IsInSpanOnAt.congr_right (g := fun p => d p * s (π p))
      (IsInSpanAt.restrict (isInSpanAt_of_eq_mul hsπ (hd.mul (hcomp (h𝔞 _ _ hs))) hd
        (Eventually.of_forall fun p => rfl))) ?_
    filter_upwards [hℓd, hsH, hvan t htN] with p hp1 hp2 hp3 hpN
    rw [hp1, hp2, hp3 hpN]
    ring
  -- the predicate carried through combinations
  let P : (Y → ℂ) → Prop := fun u => ∃ K : Y → ℂ, HolomorphicAt n K z ∧
    IsInSpanOnAt (n := n) N' ((derivIdealAlong N' 𝔠).mem z) z K ∧
    ∀ᶠ p in 𝓝 z, p ∈ N' → y p * u p = y p ^ (μ + 1) * K p
  have hinD : ∀ H, 𝔠.mem z H → IsInSpanOnAt (n := n) N' ((derivIdealAlong N' 𝔠).mem z) z H := fun H hH =>
    IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (le_derivIdealAlong h𝔠hol z H hH) hH.1)
  -- Claim B: the generators of `𝓓_N(𝔞)` at `π z`
  have hB : ∀ σ, DerivGenAlong N 𝔞 (π z) σ → P (fun p => σ (π p)) := by
    rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
    · obtain ⟨H, t, hH, ht, hsH⟩ := hC σ hσ
      refine ⟨fun p => y p * H p, hyz.mul hH.1, IsInSpanOnAt.mul_left hyz (hinD H hH), ?_⟩
      filter_upwards [hsH, hvan t ht] with p hp1 hp2 hpN
      rw [hp1, hp2 hpN]
      ring
    · refine ⟨fun _ => 0, holomorphicAt_const 0, IsInSpanAt.restrict BlowupStrictIdeal.isInSpanAt_zero, ?_⟩
      filter_upwards [hvan σ hσ] with p hp hpN
      rw [hp hpN]
      ring
    · obtain ⟨H, t, hH, ht, hsH⟩ := hC f hf
      obtain ⟨B, hBtan, hlift, ρ, hρ, hρeq⟩ := exists_tangent_lift hπ hN hCN hy hξ
      have hBhol := hBtan.holomorphicAt
      have hgen : (derivIdealAlong N' 𝔠).mem z (fieldDeriv ez B H) :=
        InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inr ⟨ez, B, H, hBtan, hH, rfl⟩))
          (holomorphicAt_fieldDeriv hzs hBhol hH.1)
      refine ⟨fun p => ((μ : ℂ) + 1) * ρ p * H p + fieldDeriv ez B H p,
        (((holomorphicAt_const _).mul hρ).mul hH.1).add (holomorphicAt_fieldDeriv hzs hBhol hH.1),
        IsInSpanOnAt.add (IsInSpanOnAt.mul_left ((holomorphicAt_const _).mul hρ) (hinD H hH))
          (IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hgen
            (holomorphicAt_fieldDeriv hzs hBhol hH.1))), ?_⟩
      -- `D'(f ∘ π) = D'(y^{μ+1}) H + y^{μ+1} D'(H) + D'(1) (t ∘ π) + D'(t ∘ π)`
      have hsum2 := fieldDeriv_eventuallyEq_sum_mul (ξ := B) (K := 2)
        (a := ![fun p => y p ^ (μ + 1), fun _ => 1]) (s := ![H, fun p => t (π p)])
        (f := f ∘ π) hzs (fun i => by fin_cases i <;> simp [holomorphicAt_pow hyz, holomorphicAt_const])
        (fun i => by fin_cases i <;> simp [hH.1, hcomp ht.1])
        (by filter_upwards [hsH] with p hp; simp [Fin.sum_univ_two, hp])
      filter_upwards [hlift f (h𝔞 _ _ hf), hsum2, fieldDeriv_pow (ξ := B) hzs hyz μ, hρeq, hlift t ht.1,
        hvan t ht, hvan _ (hξ.preserves t ht)] with p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hpN
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hp2
      have hp5' : fieldDeriv ez B (fun p => t (π p)) p = y p * fieldDeriv e ξ t (π p) := hp5.symm
      rw [hp1, hp2, hp3, hp4, fieldDeriv_const, hp5', hp7 hpN]
      ring
  -- Claim A: elements of `𝓓_N(𝔞)` at `π z`
  have hA : ∀ u, (derivIdealAlong N 𝔞).mem (π z) u → P (fun p => u (π p)) := by
    intro u hu
    obtain ⟨-, K, σ, a, hσ, ha, hsum⟩ := hu
    choose Kσ hKσ hKσspan hKσeq using fun i => hB (σ i) (hσ i)
    refine ⟨fun p => ∑ i, a i (π p) * Kσ i p, HolomorphicAt.sum _ fun i _ => (hcomp (ha i)).mul (hKσ i),
      IsInSpanOnAt.sum _ fun i _ => IsInSpanOnAt.mul_left (hcomp (ha i)) (hKσspan i), ?_⟩
    filter_upwards [hπc.eventually hsum, eventually_all.2 hKσeq] with p hp1 hp2 hpN
    rw [hp1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show y p * (a i (π p) * σ i (π p)) = a i (π p) * (y p * σ i (π p)) by ring, hp2 i hpN]
      ring
  -- Claim A': elements of `π^*𝓓_N(𝔞)` at `z`
  have hA' : ∀ v, (GermIdeal.pullback (m := n) π (derivIdealAlong N 𝔞)).mem z v → P v := by
    intro v hv
    obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hv
    choose u hu hsu using hs
    choose Ku hKu hKuspan hKueq using fun j => hA (u j) (hu j)
    refine ⟨fun p => ∑ j, c j p * Ku j p, HolomorphicAt.sum _ fun j _ => (hc j).mul (hKu j),
      IsInSpanOnAt.sum _ fun j _ => IsInSpanOnAt.mul_left (hc j) (hKuspan j), ?_⟩
    filter_upwards [hsum, eventually_all.2 hKueq] with p hp1 hp2 hpN
    rw [hp1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hsu j, show y p * (c j p * (u j ∘ π) p) = c j p * (y p * u j (π p)) by
        simp only [Function.comp_apply]; ring, hp2 j hpN]
      ring
  -- the main computation
  obtain ⟨hgh, hgall⟩ := hg
  obtain ⟨K, v, c, hv, hc, hsum⟩ := (hgall _ (hpow_self μ)).2
  choose Kv hKv hKvspan hKveq using fun j => hA' (v j) (hv j)
  have hKtot : HolomorphicAt n (fun p => ∑ j, c j p * Kv j p) z :=
    HolomorphicAt.sum _ fun j _ => (hc j).mul (hKv j)
  have hcanc := eventually_eq_on_of_pow_mul hπ hy (N := N) (μ + 1) (g := g)
    (G := fun p => ∑ j, c j p * Kv j p) (hgh.eventually.mono fun p hp => hp.continuousAt)
    (hKtot.eventually.mono fun p hp => hp.continuousAt) (by
      filter_upwards [hsum, eventually_all.2 hKveq] with p hp1 hp2 hpN
      rw [show y p ^ (μ + 1) * g p = y p * (y p ^ μ * g p) by ring, hp1 hpN, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show y p * (c j p * v j p) = c j p * (y p * v j p) by ring, hp2 j hpN]
        ring)
  exact IsInSpanOnAt.congr_right (IsInSpanOnAt.sum _ fun j _ => IsInSpanOnAt.mul_left (hc j) (hKvspan j))
    hcanc

/-- **`le:inclusions` along a submanifold** (Włodarczyk 2005, Lemma `le:inclusions`, along `N`): if
`𝔞|_N ⊆ 𝓘_C^{μ+r}|_N`, then on `N'`
`(π^* 𝓓_N^r(𝔞) : 𝒪(-μD))|_{N'} ⊆ 𝓓_{N'}^r((π^*𝔞 : 𝒪(-(μ+r)D))|_{N'})`.  Induction on `r`: the case `r = 1`
(`restrictLe_colonAlong_derivIdealAlong`) applied to `𝓓_N^r(𝔞) ⊆ 𝓘_C^{μ+1}` on `N`
(`restrictLe_iterDerivIdealAlong_idealPow`), then `𝓓_{N'}` of the induction hypothesis
(`restrictLe_derivIdealAlong`). -/
theorem restrictLe_colonAlong_iterDerivIdealAlong (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {𝔞 : GermIdeal n X}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ r μ : ℕ, RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (μ + r)) →
      RestrictLe (geoStrictTransform π C N)
        (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π (iterDerivIdealAlong N 𝔞 r))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) μ))
        (iterDerivIdealAlong (geoStrictTransform π C N)
          (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
            (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (μ + r))) r)
  | 0, μ, _ => restrictLe_refl fun _ _ hg => hg.1
  | r + 1, μ, hle => by
    have hhol := GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong (N := N) h𝔞 r
    have h1 : RestrictLe N (iterDerivIdealAlong N 𝔞 r) (idealPow (vanishingIdeal (n := n) C) (μ + 1)) :=
      restrictLe_iterDerivIdealAlong_idealPow h𝔞 r (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    have h2 := restrictLe_colonAlong_derivIdealAlong hπ hN hCN hhol h1
    have h3 := restrictLe_colonAlong_iterDerivIdealAlong hπ hN hCN h𝔞 r (μ + 1)
      (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    rw [show μ + 1 + r = μ + (r + 1) by omega] at h3
    refine restrictLe_trans h2 (restrictLe_derivIdealAlong ?_ ?_ h3)
    · exact fun _ _ hg => hg.1
    · have hcol : ∀ x g, (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (μ + (r + 1)))).mem x g →
          HolomorphicAt n g x := fun _ _ hg => hg.1
      exact GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong hcol r

/-- **Item (2) of `hir:along-calculus`: transforms of the derivative marked ideals along `N`** (Włodarczyk 2005, Lemma
`le:inclusions`; Bierstone--Milman 2008, Lemmas 3.1--3.3): for a marked ideal `𝔪 = (X, N, E, 𝔞, d)` with `N` a
closed submanifold and `𝔞` coherent, an admissible centre `C` and `j ≤ d`, on the strict transform `N'` `[𝓓_N^j(𝔪)]'
⊆ 𝓓_{N'}^j(𝔪')`, where `𝓓_N^j(𝔪) = (X, N, E, 𝓓_N^j 𝔞, d - j)` (`HomogenizedIdealAlong.derivMarkedAlong`). -/
theorem restrictLe_geoTransform_derivMarkedAlong (𝔪 : MarkedIdeals.MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) {j : ℕ} (hj : j ≤ 𝔪.d) :
    RestrictLe (geoStrictTransform π C 𝔪.N)
      ((HomogenizedIdealAlong.derivMarkedAlong 𝔪 j).geoTransform C π).ideal
      (iterDerivIdealAlong (geoStrictTransform π C 𝔪.N) (𝔪.geoTransform C π).ideal j) := by
  have hle : RestrictLe 𝔪.N 𝔪.ideal (idealPow (vanishingIdeal (n := n) C) (𝔪.d - j + j)) := by
    rw [Nat.sub_add_cancel hj]
    exact HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hC.1
      hC.subset_N hC.2.1
  have h := restrictLe_colonAlong_iterDerivIdealAlong hπ hN hC.subset_N
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) j (𝔪.d - j) hle
  rw [Nat.sub_add_cancel hj] at h
  exact h

/-- **Maximal order along `N` is preserved** (`hir:along-calculus` (2), "in particular"; Villamayor's lemma along `N`):
if `𝔪 = (X, N, E, 𝔞, d)` has maximal order along `N` (no point of `N` of order `≥ d + 1` along `N`), so has its
transform by an admissible blowup. With `j = d`: a germ `u ∈ 𝓓_N^d(𝔞)` with `u(π z) ≠ 0` gives `u ∘ π` in the
transform of `(X, N, E, 𝓓_N^d 𝔞, 0)`, hence in `𝓓_{N'}^d(𝔞')` on `N'`, so `z` is not a zero of `𝓓_{N'}^d(𝔞')`
(`HomogenizedIdealAlong.isMaximalOrderAlong_iff_inter_zeroLocus` on both sides). -/
theorem isMaximalOrderAlong_geoTransform (𝔪 : MarkedIdeals.MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hC : 𝔪.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) (hmax : HomogenizedIdealAlong.IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    HomogenizedIdealAlong.IsMaximalOrderAlong (𝔪.geoTransform C π).N (𝔪.geoTransform C π).ideal 𝔪.d := by
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hN' := MarkedIdeals.MarkedIdeal.isClosedSubmanifold_geoTransform_N hN hC hπ
  rw [HomogenizedIdealAlong.isMaximalOrderAlong_iff_inter_zeroLocus h𝔞hol hN.2] at hmax
  have h𝔞'hol : ∀ x g, (𝔪.geoTransform C π).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  rw [HomogenizedIdealAlong.isMaximalOrderAlong_iff_inter_zeroLocus h𝔞'hol hN'.2]
  refine Set.eq_empty_iff_forall_notMem.mpr fun z ⟨hzN, hz0⟩ => ?_
  have hπs := hπ.contMDiff
  have hxN : π z ∈ 𝔪.N := geoStrictTransform_subset_preimage hπs.continuous hN.1 hzN
  have hx : π z ∉ (iterDerivIdealAlong 𝔪.N 𝔪.ideal 𝔪.d).zeroLocus := fun hx =>
    (Set.eq_empty_iff_forall_notMem.mp hmax) (π z) ⟨hxN, hx⟩
  simp only [GermIdeal.zeroLocus, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨u, hu, hux⟩ := hx
  have huhol : HolomorphicAt n u (π z) := GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞hol 𝔪.d _ _ hu
  have huπ : HolomorphicAt n (fun p => u (π p)) z :=
    huhol.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  -- `u ∘ π` lies in the transform of `(X, N, E, 𝓓_N^d 𝔞, 0)`
  have hmem : ((HomogenizedIdealAlong.derivMarkedAlong 𝔪 𝔪.d).geoTransform C π).ideal.mem z (fun p => u (π p)) := by
    refine ⟨huπ, fun h hh => ⟨(holomorphicAt_of_mem_idealPow hh).mul huπ, ?_⟩⟩
    exact IsInSpanAt.restrict (isInSpanAt_of_eq_mul (comp_mem_pullback (𝔟 := iterDerivIdealAlong 𝔪.N 𝔪.ideal 𝔪.d)
      hu huπ (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp))
      ((holomorphicAt_of_mem_idealPow hh).mul huπ) (holomorphicAt_of_mem_idealPow hh)
      (Eventually.of_forall fun p => rfl))
  obtain ⟨K, s, a, hs, -, hsum⟩ :=
    restrictLe_geoTransform_derivMarkedAlong 𝔪 hN h𝔞 hC hπ le_rfl z hzN _ hmem
  have h1 := hsum.self_of_nhds hzN
  simp only at h1
  rw [Finset.sum_eq_zero fun i _ => by rw [hz0 _ (hs i), mul_zero]] at h1
  exact hux h1

end Inclusion

end

end Hironaka.DerivativeIdealAlongTransform
