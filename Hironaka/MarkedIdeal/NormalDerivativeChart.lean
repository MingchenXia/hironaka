/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalTaylorOrder
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Flat charts along a submanifold and normal derivatives

Source: Włodarczyk 2005, proof of Lemma `le:S`; GGT 2008, proof of Proposition 5.6.4 (the coefficients `c_α|_S =
(α!)⁻¹ (∂^α_x f)|_S` lie in `𝓓^{|α|}(𝓘)|_S`).

* `FlatChart n S p k`: coordinates `ψ = Φ ∘ e` at `p` (`e` the preferred chart, `Φ` a local biholomorphism with
  `Φ (e p) = 0`) in which `S` is the plane `ℂᵏ × 0` near `p` -- the data of `RegularAtDim`.  Its inverse `inv`,
  and the **normal derivatives** `nd c L f = ∂^L (f ∘ inv) ∘ ψ` along lists `L` of coordinate directions.
* `FlatChart.mem_idealPow_of_vanishesToOrderOn`: `f ∈ 𝔪_p^μ` as soon as each normal derivative `∂^L f`
  (`L` normal, `|L| < μ`) vanishes to order `μ - |L|` along `S` (from `NormalTaylorOrder`).
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.NormalDerivativeChart

open Hironaka.HolomorphicIdealSheaves HolomorphicTaylorTail GermIdealOrder IdealWeightPowers NormalTaylorOrder DerivativeIdeal BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n) in
/-- **A flat chart** at `p` for `S` of dimension `k`: a local biholomorphism `Φ` at `e p` (`e` the preferred chart),
with `Φ (e p) = 0`, in which `S` is the plane `ℂᵏ × 0` near `p`. -/
structure FlatChart (S : Set M) (p : M) (k : ℕ) where
  /-- The flattening. -/
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p)
  src : Φ.source ⊆ (chartAt (ComplexModel n) p).target
  zero : Φ.toFun (chartAt (ComplexModel n) p p) = 0
  flat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ Φ.source →
    (y ∈ S ↔ Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n k)

/-- Membership in a coherent ideal only depends on the germ. -/
theorem mem_congr_of_isCoherent {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {g g' : M → ℂ} (hg : 𝔞.mem x g)
    (h : g =ᶠ[𝓝 x] g') : 𝔞.mem x g' :=
  GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞 (isInSpanAt_of_eq_mul hg
    ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg).congr h)
    (holomorphicAt_const 1) (h.symm.mono fun p hp => by simp [hp]))

namespace FlatChart

variable {S : Set M} {p : M} {k : ℕ} (c : FlatChart n S p k)

/-- The coordinates `ψ = Φ ∘ e`. -/
def ψ : M → ComplexModel n := fun y => c.Φ.toFun (chartAt (ComplexModel n) p y)

/-- The inverse `u ↦ e⁻¹ (Φ⁻¹ u)`. -/
def inv : ComplexModel n → M := fun u => (chartAt (ComplexModel n) p).symm (c.Φ.invFun u)

/-- **The normal derivative** `∂^L f = ∂_{e_{l₁}} ⋯ ∂_{e_{l_m}} (f ∘ inv) ∘ ψ` along `L = [l₁, …, l_m]`. -/
def nd (L : List (Fin n)) (f : M → ℂ) : M → ℂ :=
  fun y => iterDeriv (L.map bv) (fun u => f (c.inv u)) (c.ψ y)

/-- A flat chart from `RegularAtDim`. -/
def ofRegularAtDim (h : RegularAtDim (n := n) S p k) : FlatChart n S p k where
  Φ := h.2.2.choose
  src := h.2.2.choose_spec.1
  zero := h.2.2.choose_spec.2.1
  flat := h.2.2.choose_spec.2.2

theorem mem_flatDomain : p ∈ flatDomain c.Φ := mem_flatDomain_self c.Φ

theorem ψ_self : c.ψ p = 0 := c.zero

theorem zero_mem_target : (0 : ComplexModel n) ∈ c.Φ.target := by
  rw [← c.zero]; exact c.Φ.mapsTo_toFun c.Φ.center_mem_source

theorem inv_zero : c.inv 0 = p := by
  rw [← c.zero]; exact flatInverse_flat c.Φ c.mem_flatDomain

theorem eventually_mem_flatDomain : ∀ᶠ y in 𝓝 p, y ∈ flatDomain c.Φ :=
  (isOpen_flatDomain c.Φ).mem_nhds c.mem_flatDomain

theorem mdifferentiableAt_ψ {y : M} (hy : y ∈ flatDomain c.Φ) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.ψ y := by
  have hΦ : DifferentiableAt ℂ c.Φ.toFun (chartAt (ComplexModel n) p y) :=
    c.Φ.toFun_holomorphic.differentiableAt (c.Φ.isOpen_source.mem_nhds hy.2)
  exact hΦ.mdifferentiableAt.comp y (mdifferentiableAt_chart hy.1)

theorem eventually_mdifferentiableAt_ψ :
    ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.ψ y := by
  filter_upwards [c.eventually_mem_flatDomain] with y hy using c.mdifferentiableAt_ψ hy

theorem mdifferentiableAt_inv {u : ComplexModel n} (hu : u ∈ c.Φ.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv u := by
  have h1 : c.Φ.invFun u ∈ c.Φ.source := c.Φ.mapsTo_invFun hu
  have hΦ : DifferentiableAt ℂ c.Φ.invFun u :=
    c.Φ.invFun_holomorphic.differentiableAt (c.Φ.isOpen_target.mem_nhds hu)
  exact (mdifferentiableAt_chart_symm (c.src h1)).comp u hΦ.mdifferentiableAt

theorem eventually_mdifferentiableAt_inv :
    ∀ᶠ u in 𝓝 (0 : ComplexModel n), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv u := by
  filter_upwards [c.Φ.isOpen_target.mem_nhds c.zero_mem_target] with u hu using c.mdifferentiableAt_inv hu

theorem eventually_inv_ψ : ∀ᶠ y in 𝓝 p, c.inv (c.ψ y) = y := by
  filter_upwards [c.eventually_mem_flatDomain] with y hy using flatInverse_flat c.Φ hy

theorem eventually_ψ_inv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), c.ψ (c.inv u) = u := by
  filter_upwards [c.Φ.isOpen_target.mem_nhds c.zero_mem_target] with u hu
  exact (flatInverse_mem c.Φ hu c.src).2

theorem eventually_flat : ∀ᶠ y in 𝓝 p, (y ∈ S ↔ c.ψ y ∈ complexCoordinatePlane n k) := by
  filter_upwards [c.eventually_mem_flatDomain] with y hy using c.flat hy.1 hy.2

theorem tendsto_inv : Tendsto c.inv (𝓝 (0 : ComplexModel n)) (𝓝 p) := by
  have h := c.eventually_mdifferentiableAt_inv.self_of_nhds.continuousAt.tendsto
  rwa [c.inv_zero] at h

theorem tendsto_ψ : Tendsto c.ψ (𝓝 p) (𝓝 (0 : ComplexModel n)) := by
  have h := c.eventually_mdifferentiableAt_ψ.self_of_nhds.continuousAt.tendsto
  rwa [c.ψ_self] at h

/-- `f ∘ inv` is holomorphic near `0` for `f` holomorphic at `p`. -/
theorem eventually_differentiableAt_comp_inv {f : M → ℂ} (hf : HolomorphicAt n f p) :
    ∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun u => f (c.inv u)) u := by
  filter_upwards [c.eventually_mdifferentiableAt_inv, c.tendsto_inv.eventually hf] with u hu hfu
  exact mdifferentiableAt_iff_differentiableAt.mp (hfu.comp u hu)

/-- **The order from the normal derivatives** (`NormalTaylorOrder.mem_idealPow_of_normalDeriv` in a flat chart). -/
theorem mem_idealPow_of_vanishesToOrderOn {f : M → ℂ} (hf : HolomorphicAt n f p) {μ : ℕ}
    (hL : ∀ L : List (Fin n), NormalIdx k L → L.length < μ →
      VanishesToOrderOn n S p (μ - L.length) (c.nd L f)) :
    (idealPow (pointIdeal n p) μ).mem p f :=
  mem_idealPow_of_normalDeriv c.eventually_mdifferentiableAt_ψ c.ψ_self c.eventually_mdifferentiableAt_inv
    c.inv_zero c.eventually_inv_ψ c.eventually_ψ_inv c.eventually_flat hf hL

/-- The differential of `Φ` is injective. -/
theorem injective_fderiv_Φ {z : ComplexModel n} (hz : z ∈ c.Φ.source) :
    Function.Injective (fderiv ℂ c.Φ.toFun z) := by
  have hzt : c.Φ.toFun z ∈ c.Φ.target := c.Φ.mapsTo_toFun hz
  have hT : DifferentiableAt ℂ c.Φ.toFun z := c.Φ.toFun_holomorphic.differentiableAt (c.Φ.isOpen_source.mem_nhds hz)
  have hI : DifferentiableAt ℂ c.Φ.invFun (c.Φ.toFun z) :=
    c.Φ.invFun_holomorphic.differentiableAt (c.Φ.isOpen_target.mem_nhds hzt)
  have hcomp : HasFDerivAt (fun w => c.Φ.invFun (c.Φ.toFun w))
      ((fderiv ℂ c.Φ.invFun (c.Φ.toFun z)).comp (fderiv ℂ c.Φ.toFun z)) z :=
    hI.hasFDerivAt.comp z hT.hasFDerivAt
  have hid : HasFDerivAt (fun w => c.Φ.invFun (c.Φ.toFun w)) (ContinuousLinearMap.id ℂ (ComplexModel n)) z := by
    refine (hasFDerivAt_id z).congr_of_eventuallyEq ?_
    filter_upwards [c.Φ.isOpen_source.mem_nhds hz] with w hw using c.Φ.left_inv w hw
  have heq := hcomp.unique hid
  intro v w hvw
  have := congrArg (fderiv ℂ c.Φ.invFun (c.Φ.toFun z)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, heq] at this
  exact this

end FlatChart

end

end Hironaka.NormalDerivativeChart
