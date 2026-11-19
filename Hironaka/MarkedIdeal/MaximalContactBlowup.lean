import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFunctionTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Tangent directions under a blowup (Giraud)

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:giraud-transform`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.7, Lemma `le:Gi` (1).

Let `π : Y → X` be a blowup along `C`, `h` a local equation of the exceptional divisor on `U`
(`BlowupFunctionTransform.IsLocalEquation`), and `(𝔞, μ + 1)` a coherent marked ideal with
`𝔞 ⊆ 𝓘_C^{μ+1}` (for instance `C ⊆ cosupp(𝔞, μ + 1)`).  For a germ `u` of
`T(𝔞) = 𝓓^μ(𝔞)` at `π z` (a tangent direction when it has multiplicity one), its controlled
transform `u' = h^{-1} π^* u` (`u ∘ π = h · u'`, TN3's `BlowupFunctionTransform.exists_eq_pow_mul`)
lies in `T(σ^c(𝔞, μ + 1)) = 𝓓^μ(σ^c(𝔞, μ + 1))`:

* `mem_iterDerivIdeal_controlledTransform` (**Giraud, `le:Gi` (1)**), from
  `BlowupDerivativeIdeal.controlledTransform_iterDerivIdeal_le` with `r = μ` and mark `1`;
* `exists_controlledTransform_mem_iterDerivIdeal`: the transform exists and lies there;
* `..._of_subset_cosupport`: the same under the source's hypothesis `C ⊆ cosupp(𝔞, μ + 1)`.

Parts (2) (multiplicity one of `u'`) and (3) (`V(u')` is the strict transform of `V(u)`, TN3's
`BlowupFunctionTransform.vanishingIdeal_geoStrictTransform_mem_iff` for a closed hypersurface) are
not in this module.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.MaximalContactBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  DerivativeIdeal IdealWeightPowers BlowupControlledTransform BlowupFunctionTransform
  BlowupDerivativeIdeal

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {hπ : IsBlowupAlong n C π}
  {U : Set Y} {h : Y → ℂ}

/-- **Giraud, `le:Gi` (1)**: the controlled transform `u'` (`u ∘ π = h · u'`) of a germ `u` of
`𝓓^μ(𝔞)` lies in `𝓓^μ(σ^c(𝔞, μ + 1))`, for a coherent `𝔞 ⊆ 𝓘_C^{μ+1}`. -/
theorem mem_iterDerivIdeal_controlledTransform {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) (μ + 1)))
    (hh : IsLocalEquation hπ U h) {z : Y} (hz : z ∈ U) {u : X → ℂ}
    (hu : (iterDerivIdeal 𝔞 μ).mem (π z) u) {u' : Y → ℂ} (hu' : HolomorphicAt n u' z)
    (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) :
    (iterDerivIdeal (controlledTransform hπ 𝔞 (μ + 1)) μ).mem z u' := by
  have h1 : (controlledTransform hπ (iterDerivIdeal 𝔞 μ) 1).mem z u' :=
    mem_controlledTransform_of_eq_pow_mul hh hz hu hu' (by simpa using heq)
  have h2 := controlledTransform_iterDerivIdeal_le hπ h𝔞 μ 1 (by rwa [Nat.add_comm 1 μ])
  rw [Nat.add_comm 1 μ] at h2
  exact h2 z u' h1

/-- The controlled transform of a germ of `T(𝔞) = 𝓓^μ(𝔞)` exists and lies in
`T(σ^c(𝔞, μ + 1))`. -/
theorem exists_controlledTransform_mem_iterDerivIdeal {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    {μ : ℕ} (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) (μ + 1)))
    (hh : IsLocalEquation hπ U h) {z : Y} (hz : z ∈ U) {u : X → ℂ}
    (hu : (iterDerivIdeal 𝔞 μ).mem (π z) u) :
    ∃ u' : Y → ℂ, HolomorphicAt n u' z ∧ ((u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) ∧
      (iterDerivIdeal (controlledTransform hπ 𝔞 (μ + 1)) μ).mem z u' := by
  have hC : ∀ y g, (vanishingIdeal (n := n) C).mem y g → HolomorphicAt n g y := fun _ _ h => h.1
  have hu1 : (idealPow (vanishingIdeal (n := n) C) 1).mem (π z) u :=
    iterDerivIdeal_le_idealPow hC μ (by rwa [Nat.add_comm 1 μ]) (π z) u hu
  obtain ⟨u', hu', heq⟩ := exists_eq_pow_mul hh hz hu1
  have heq' : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y := by simpa using heq
  exact ⟨u', hu', heq', mem_iterDerivIdeal_controlledTransform h𝔞 hle hh hz hu hu' heq'⟩

/-- `le:Gi` (1) under the source's hypothesis `C ⊆ cosupp(𝔞, μ + 1)`. -/
theorem exists_controlledTransform_mem_iterDerivIdeal_of_subset_cosupport
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hsub : C ⊆ cosupport n univ 𝔞 (μ + 1)) (hh : IsLocalEquation hπ U h) {z : Y} (hz : z ∈ U)
    {u : X → ℂ} (hu : (iterDerivIdeal 𝔞 μ).mem (π z) u) :
    ∃ u' : Y → ℂ, HolomorphicAt n u' z ∧ ((u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y) ∧
      (iterDerivIdeal (controlledTransform hπ 𝔞 (μ + 1)) μ).mem z u' :=
  exists_controlledTransform_mem_iterDerivIdeal h𝔞
    (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 hsub) hh hz hu

end

end Hironaka.MaximalContactBlowup
