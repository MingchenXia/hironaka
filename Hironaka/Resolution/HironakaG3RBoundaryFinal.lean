import Hironaka.Resolution.HironakaG3RBoundaryGlobal
import Hironaka.Resolution.HironakaG3RPureFinal

/-! # G3 under target (A): the final statement with embedded resolution relative to a boundary

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-boundary-final.tex`.

**`g3_final_global_boundary`**: on every complex manifold `X` (not necessarily compact),
(a), (b), (c) as in `HironakaG3RPureFinal.g3_final_global_pure` (glued canonical resolutions of marked ideals; glued
embedded resolution of every closed analytic set of pure dimension relative to the empty boundary; dimension parts);
(d) **embedded resolution relative to a simple normal crossings boundary**: for every closed analytic `W` of pure dimension
`d < n` (possibly reducible) and every divisor `E₀` with simple normal crossings in the convention of the domain (a finite list
of closed sets, `IsSNCDivisor n E₀`) such that no member of `E₀` contains a nonempty relatively open subset of `W`, with
`W_sing = W \ regularLocus W d` and `F = W_sing ∪ (W ∩ |E₀|)`: the glued embedded resolution `P : X' → X` of `W` relative to
`E₀` exists, is unique up to unique biholomorphism over `X` and is a single stopped canonical prefix over every relatively
compact open set; `P` is holomorphic, proper and surjective, `P⁻¹ W_sing ⊆ Exc P ⊆ P⁻¹ F`, `P` is an isomorphism over
`X ∖ F`, the strict transform of `W` is a closed submanifold of dimension `d` at each of its points, and the total transform
of `E₀` together with the exceptional locus, `P⁻¹|E₀| ∪ Exc P = P⁻¹(|E₀| ∪ W_sing)`, is the union of a locally finite
indexed simple normal crossings family of nonempty closed sets with which the strict transform has only normal crossings;
(e) for `E₀ = []` the glued resolution of (d) is the one of (b).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RBoundaryFinal

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RGluedUniqueness HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RBoundaryEmbedded
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)
open HironakaActualLocallyFiniteBoundary (IsLocallyFiniteSNCDivisor)
open HironakaEmbeddedDimensionParts (dimensionPart)

variable {n : ℕ}

/-- **The total transform of the boundary together with the exceptional locus is the preimage of `|E₀| ∪ W_sing`.** -/
theorem preimage_union_eq {X : CMfd.{u} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {X' : CMfd.{u} n} {P : X' → X}
    (h : IsGluedBoundaryResolution W d E₀ X' P) :
    P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P = P ⁻¹' ((⋃ H ∈ E₀, H) ∪ W \ regularLocus (n := n) W d) := by
  apply Subset.antisymm
  · rintro z (hz | hz)
    · exact Or.inl hz
    · rcases exceptionalLocus_subset hWa hd hpure hE₀ hE₀W h hz with hs | ⟨-, hb⟩
      · exact Or.inr hs
      · exact Or.inl hb
  · rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (preimage_sing_subset_exceptionalLocus hWa hd hpure hE₀ hE₀W h hz)

/-- **The final G3 theorem under target (A), with embedded resolution relative to a simple normal crossings boundary**;
(a)–(c) are `HironakaG3RPureFinal.g3_final_global_pure`. -/
theorem g3_final_global_boundary (X : CMfd.{u} n) :
    (∀ M : MarkedIdeal n X, IsInvDomain n M →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K → ∃ c : GluedChart M X' P, c.U = U) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = HironakaG3RGluedBoundary.gluedBoundary M X' P) ∧
        (M.N = univ → M.d = 1 →
          (GermIdeal.pullback (m := n) P M.ideal).IsInvertible ∧
            (GermIdeal.pullback (m := n) P M.ideal).zeroLocus = P ⁻¹' M.ideal.zeroLocus ∧
            IsIsomorphismOver n P M.ideal.zeroLocusᶜ)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W → ∀ d : ℕ, W ⊆ closure (regularLocus (n := n) W d) →
      ∃ (X' : CMfd.{u} n) (P : X' → X),
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
        exceptionalLocus n P = P ⁻¹' (W \ regularLocus (n := n) W d) ∧
        IsIsomorphismOver n P (W \ regularLocus (n := n) W d)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P W) ∧
        (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = exceptionalLocus n P ∧ HasNormalCrossingsWithBoundary (strictTransform n P W) D) ∧
        (d < n → IsGluedPureResolution W d X' P ∧
          (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedPureResolution W d X'' P' →
            ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
          (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
            ∃ c : TowerChart (embeddedClass W d) X' P, c.U = U)) ∧
        (n ≤ d → IsOpen W ∧ W \ regularLocus (n := n) W d = ∅ ∧
          ∃ Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X, ∀ z, Φ z = P z)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W →
      W = ⋃ k : Fin (n + 1), dimensionPart (n := n) W k ∧
        ∀ k : Fin (n + 1), IsComplexAnalyticSubset (n := n) (dimensionPart (n := n) W k) ∧
          dimensionPart (n := n) W k ⊆ W ∧
          dimensionPart (n := n) W k ⊆ closure (regularLocus (n := n) (dimensionPart (n := n) W k) k)) ∧
    (∀ W : Set X, IsComplexAnalyticSubset (n := n) W → ∀ d : ℕ, d < n → W ⊆ closure (regularLocus (n := n) W d) →
      ∀ E₀ : List (Set X), IsSNCDivisor n E₀ → W ⊆ closure (W \ ⋃ H ∈ E₀, H) →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedBoundaryResolution W d E₀ X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedBoundaryResolution W d E₀ X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
          ∃ c : TowerChart (bdryClass W d E₀) X' P, c.U = U) ∧
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
        P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
        exceptionalLocus n P ⊆ P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
        IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P W) ∧
        (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
        ∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P ∧
          (⋃ i, D i) = P ⁻¹' ((⋃ H ∈ E₀, H) ∪ W \ regularLocus (n := n) W d) ∧
          HasNormalCrossingsWithBoundary (strictTransform n P W) D) ∧
    (∀ (W : Set X) (d : ℕ) (X' : CMfd.{u} n) (P : X' → X),
      IsGluedBoundaryResolution W d [] X' P ↔ IsGluedPureResolution W d X' P) := by
  refine ⟨(HironakaG3RPureFinal.g3_final_global_pure X).1, (HironakaG3RPureFinal.g3_final_global_pure X).2.1,
    (HironakaG3RPureFinal.g3_final_global_pure X).2.2, fun W hWa d hd hpure E₀ hE₀ hE₀W => ?_,
    isGluedBoundaryResolution_nil⟩
  obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedBoundaryResolution hWa hd hpure hE₀ hE₀W
  obtain ⟨ι, D, hD, hne, hU, hnc⟩ := HironakaG3RBoundaryGlobal.exists_globalBoundary hWa hd hpure hE₀ hE₀W h
  exact ⟨X', P, h, huniq, fun U K hK hUK => exists_chart_of_subset_isCompact hWa hd hpure hE₀ hE₀W h U hK hUK,
    h.1, h.2.1, h.2.2.1, preimage_sing_subset_exceptionalLocus hWa hd hpure hE₀ hE₀W h,
    exceptionalLocus_subset hWa hd hpure hE₀ hE₀W h, isIsomorphismOver hWa hd hpure hE₀ hE₀W h,
    strictTransform_isClosedSubmanifold hWa hd hpure hE₀ hE₀W h, regularAtDim_strictTransform hWa hd hpure hE₀ hE₀W h,
    ι, D, hD, hne, hU, hU.trans (preimage_union_eq hWa hd hpure hE₀ hE₀W h), hnc⟩

end

end Hironaka.HironakaG3RBoundaryFinal
