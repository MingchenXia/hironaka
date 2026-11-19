import Hironaka.Analytic.QuantitativeRegularizationBergmanOverlap

set_option autoImplicit false

/-!
# A germ of the weighted space is dominated by the Bergman sup-weight

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`).

Step 4 of Copy-4 needs the lower bound `φ_{j,m} ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)` near a point.  Copy-4
gets it from `\cite[Proposition 1.2]{DEL00}`: the multiplier ideal is *generated* on `B_j` by
the orthonormal basis of `H_{j,m}`.  The Lean statement of the regularization lemma is weaker —
it only asks that every finite family of germs of `𝓘(mφ)` at a point be dominated — and that
weaker form follows from the *same* point extension as Step 2, applied at each point of a small
ball instead of once at the centre.

`normSq_le_bergmanSup` is that statement: if `g` is holomorphic on a neighbourhood `U` of the
cut-off support and its weighted `L²` norm `N` over `tsupport θ` is finite, then at every `y`
close to `x`

  `|g y|² ≤ (C · N + 1) · bergmanSup B_j e^{-ϕ} y`,

with `C = pointExtensionConst d (r/2) Mθ (2S) S` depending only on the cut-off and the size of
`B_j`.  Dividing by `m` and taking logarithms (`ϕ = m Ψ`) this is
`m⁻¹ log|g|² ≤ Ψ_{j,m} + O(1)` for the common-weight kernel `Ψ_{j,m}` of
`Hironaka.QuantitativeRegularizationBergmanOverlap`; the passage to Copy-4's own-weight
`ψ_{j,m}` needs the same holomorphic-multiplier isometry recorded there.

The trick is that the extension point may vary: `θ ≡ 1` on `ball x r` also gives `θ ≡ 1` on
`ball y (r/2)` for every `y ∈ ball x (r/2)`, so one fixed cut-off serves every `y`, and the
constant does not move with `y`.

As in the rest of Step 2 the weight `ϕ` here is smooth and bounded below; see
`Hironaka.QuantitativeRegularizationPointExtension` for those restrictions and why the lower
bound is the one that really costs something.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.QuantitativeRegularizationGermDomination

noncomputable section

open BergmanSupWeight
open QuantitativeRegularizationPointExtension

variable {d : ℕ}

/-- **A germ of the weighted space is dominated by the Bergman sup-weight**
(Copy-4, `lem:regularization`, Step 4). -/
theorem normSq_le_bergmanSup (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {r : ℝ} (hr : 0 < r)
    {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθ1 : ∀ z ∈ ball x r, θ z = 1) (hθle : ∀ z, |θ z| ≤ 1)
    {U : Set (ComplexModel d)} (hUo : IsOpen U) (hts : tsupport θ ⊆ U)
    (htsD : tsupport θ ⊆ D) {g : ComplexModel d → ℂ} (hg : DifferentiableOn ℂ g U)
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcD : Bjc ⊆ D)
    {B S : ℝ} (hϕupper : ∀ z ∈ Bj, ϕ z ≤ B) (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    (hN : ∫⁻ z in tsupport θ, ENNReal.ofReal (‖g z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-ϕ z)) ≠ ⊤)
    {y : ComplexModel d} (hyBj : y ∈ Bj) (hyx : ‖y - x‖ < r / 2) :
    ENNReal.ofReal (‖g y‖ ^ 2) ≤
      (ENNReal.ofReal (pointExtensionConst d (r / 2) Mθ (2 * S) S) *
        (∫⁻ z in tsupport θ, ENNReal.ofReal (‖g z‖ ^ 2) *
          ENNReal.ofReal (Real.exp (-ϕ z))) + 1) *
        bergmanSup Bj (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) y := by
  set N : ℝ≥0∞ := ∫⁻ z in tsupport θ, ENNReal.ofReal (‖g z‖ ^ 2) *
    ENNReal.ofReal (Real.exp (-ϕ z)) with hNdef
  set C : ℝ := pointExtensionConst d (r / 2) Mθ (2 * S) S with hC
  -- the fixed cut-off is still `1` on the half-ball around the shifted centre
  have hθ1' : ∀ z ∈ ball y (r / 2), θ z = 1 := by
    intro z hz
    refine hθ1 z ?_
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have hsplit : z - x = (z - y) + (y - x) := (sub_add_sub_cancel z y x).symm
    calc ‖z - x‖ = ‖(z - y) + (y - x)‖ := by rw [hsplit]
      _ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hz hyx
      _ = r := by ring
  have hSnn : 0 ≤ S := le_trans (norm_nonneg y) (hnormS y hyBj)
  have hyS : ‖y‖ ≤ S := hnormS y hyBj
  have hnormR : ∀ z ∈ Bj, ‖z - y‖ ≤ 2 * S := by
    intro z hz
    calc ‖z - y‖ ≤ ‖z‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ S + S := add_le_add (hnormS z hz) hyS
      _ = 2 * S := by ring
  obtain ⟨F, hF1, hF2, hF3⟩ :=
    exists_pointExtension_lintegral_of_smooth_weight hd hDo hDc hDb hϕ hϕL hBϕ y
      (by linarith : (0:ℝ) < r / 2) hθ hθcs hθ1' hθle hUo hts htsD hg hMθ hBjo hBjBjc hBjc
      hBjcD hyBj hϕupper hnormR hnormS
  have hCpos : 0 < C := pointExtensionConst_pos (by linarith)
  have hA0 : ENNReal.ofReal C * N + 1 ≠ 0 := by simp
  have hAtop : ENNReal.ofReal C * N + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN, by simp⟩
  have hFbound : ∫⁻ z in Bj, ENNReal.ofReal (‖F z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-ϕ z)) ≤ ENNReal.ofReal C * N + 1 :=
    hF3.trans le_self_add
  have hkey := bergmanSup_extremal hF1 hA0 hAtop hFbound y
  rwa [hF2] at hkey

end

end Hironaka.QuantitativeRegularizationGermDomination
