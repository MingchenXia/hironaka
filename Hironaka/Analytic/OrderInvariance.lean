import Hironaka.MarkedIdeal.CoherentOrderUpperSemicontinuity
import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Invariant.IdealOrderArithmetic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Invariance and semicontinuity of the order

Blueprint `hir:order-invariance` (`blueprint/src/hironaka.tex`, Hironaka phase H1).  Sources: Włodarczyk 2005
§2.4 (functoriality of the invariants under étale maps, here biholomorphisms) and §2.1 (`supp(𝓘, μ)` is closed,
i.e. `ord_x 𝓘` is upper semicontinuous).

* `cosupport_pullback_eq`: for a biholomorphism `φ : M' → M` (holomorphic with holomorphic inverse) and an ideal
  `𝔞` of holomorphic germs, `cosupp(φ^*𝔞, μ) = φ⁻¹(cosupp(𝔞, μ))` (`N = M`); `order_pullback_eq`:
  `ord_{x'}(φ^*𝔞) = ord_{φ x'}(𝔞)`.
* `eventually_order_le`: for a coherent ideal the order is upper semicontinuous:
  `ord_y 𝔞 ≤ ord_x 𝔞` for `y` near `x`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.OrderInvariance

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.OrderTaylor Hironaka.HadamardBridge
  Hironaka.IdealOrderArithmetic

open Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The cosupport is invariant under biholomorphisms**: `cosupp(φ^*𝔞, μ) = φ⁻¹(cosupp(𝔞, μ))`. -/
theorem cosupport_pullback_eq {φ : M' → M} {ψ : M → M'}
    (hφ : ∀ x', MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ x')
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ x', ψ (φ x') = x')
    {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    cosupport n univ (GermIdeal.pullback (m := n) φ 𝔞) μ = φ ⁻¹' cosupport n univ 𝔞 μ := by
  ext x'
  constructor
  · rintro ⟨-, hx'⟩
    refine ⟨mem_univ _, fun a ha => ⟨a, ?_, Eventually.of_forall fun _ _ => rfl⟩⟩
    have haφ : (GermIdeal.pullback (m := n) φ 𝔞).mem x' (a ∘ φ) :=
      RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr <| isInSpanAt_of_eq_mul ⟨a, ha, rfl⟩
        (holomorphicAt_comp_map (Eventually.of_forall hφ) (h𝔞 _ _ ha)) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    have h1 : (idealPow (pointIdeal n x') μ).mem x' (a ∘ φ) :=
      mem_idealPow_of_vanishesToOrderOn_univ (hx' _ haφ)
    rw [← hψφ x'] at h1
    have h2 := comp_mem_idealPow_pointIdeal (φ := ψ) (u := φ x') (Eventually.of_forall hψ) μ h1
    have h3 : (a ∘ φ) ∘ ψ = a := funext fun x => by simp [hφψ x]
    rwa [h3] at h2
  · intro hx
    refine ⟨mem_univ _, fun g hg => IsInSpanAt.vanishesToOrderOn
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg) ?_⟩
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a ∘ φ, comp_mem_idealPow_pointIdeal (Eventually.of_forall hφ) μ
      (mem_idealPow_of_vanishesToOrderOn_univ (hx.2 a ha)), Eventually.of_forall fun _ _ => rfl⟩

/-- **The order is invariant under biholomorphisms**: `ord_{x'}(φ^*𝔞) = ord_{φ x'}(𝔞)`. -/
theorem order_pullback_eq {φ : M' → M} {ψ : M → M'}
    (hφ : ∀ x', MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ x')
    (hψ : ∀ x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ x', ψ (φ x') = x')
    {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x' : M') :
    order n univ (GermIdeal.pullback (m := n) φ 𝔞) x' = order n univ 𝔞 (φ x') := by
  have hiff : ∀ q : ℕ, OrderGE n univ (GermIdeal.pullback (m := n) φ 𝔞) x' q ↔
      OrderGE n univ 𝔞 (φ x') q := fun q => by
    have h := congrArg (fun S => x' ∈ S) (cosupport_pullback_eq hφ hψ hφψ hψφ h𝔞 q)
    simp only [cosupport, mem_univ, true_and, mem_preimage, eq_iff_iff] at h
    exact h
  simp only [order, hiff]


end
end Hironaka.OrderInvariance
