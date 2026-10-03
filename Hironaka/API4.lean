/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The public statements of the Hironaka library, IV: analytic sets over relatively compact open sets; restriction to opens

`Hironaka.API`, `Hironaka.API2` and `Hironaka.API3` are unchanged; this module adds, in the same form (over an
unbundled complex manifold, without marked ideals, towers, invariants or domain conditions):

## Embedded resolution of an arbitrary analytic set over an open set contained in a compact set

For an analytic set `W ⊆ X` with empty interior (its components may have different dimensions; `W` need NOT be compact), with
`W_sing = W \ ⋃ k, Reg_k W` and `W⁽ᵏ⁾ = closure (Reg_k W)` (`HironakaEmbeddedDimensionParts.dimensionPart`), and an open set
`X₀` contained in a compact set:

* `exists_embeddedResolution_analytic_of_subset_isCompact`: ONE admissible sequence of `(X₀, [])` with centres over
  `W_sing ∩ X₀`, `E` SNC, `Exc f = ⋃ E = f⁻¹(W_sing ∩ X₀)`, `f` an isomorphism over `X₀ \ W_sing`, the strict transform `W'` of
  `W ∩ X₀` a closed submanifold which is the union of the pairwise disjoint strict transforms of the `W⁽ᵏ⁾ ∩ X₀` (`k < n`), of
  dimension `k` along the strict transform of `W⁽ᵏ⁾ ∩ X₀`, with normal crossings with `E`;
* `exists_embeddedResolution_analytic_local`: the same over a relatively compact open neighbourhood `U` of a given compact set;
* `exists_embeddedResolution_analytic_boundary_of_subset_isCompact`, `exists_embeddedResolution_analytic_boundary_local`: the
  same relative to a simple normal crossings divisor `E₀` none of whose members contains a nonempty relatively open subset of
  `W`, with centres over `(W_sing ∪ (W ∩ |E₀|)) ∩ X₀`.

## Tools

* `exists_separation_of_subset_isCompact`: principalization of `𝓘_A + 𝓘_B` over an open set contained in a compact set makes the
  strict transforms of `A ∩ X₀` and `B ∩ X₀` disjoint (no compactness of `A ∩ B`);
* `exists_restrict_opens`: an admissible sequence restricts to an admissible sequence over any open subset `O` (the restricted
  total space is embedded onto `f⁻¹(O)`; exceptional loci and strict transforms correspond).

These are restatements of theorems of `HironakaEmbeddedAnalyticLocal` and `HironakaBaseChange`; their proofs are one line.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence Hironaka.HironakaEmbeddedDimensionParts

noncomputable section

variable {n : ℕ}

/-! ### Embedded resolution of an analytic set over relatively compact open sets -/

section Analytic

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Embedded resolution of an arbitrary analytic set over an open set contained in a compact set, by one admissible
sequence** (Hironaka; Bierstone--Milman 1997, Theorem 1.6 over relatively compact open sets): `W ⊆ X` analytic with empty
interior, its components of any dimensions, not necessarily compact; `X₀ ⊆ X` open, contained in a compact set;
`W_sing = W \ ⋃ k, Reg_k W`.  One admissible sequence `f` of `(X₀, [])` with centres over `W_sing ∩ X₀`, with divisor `E`: `E`
has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing ∩ X₀)`, `f` is an isomorphism over `X₀ \ W_sing`, the strict transform of
`W ∩ X₀` is a closed submanifold, the union of the pairwise disjoint strict transforms of the `W⁽ᵏ⁾ ∩ X₀` (`k < n`), of
dimension `k` at each point of the strict transform of `W⁽ᵏ⁾ ∩ X₀`, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_of_subset_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) (X₀ : Opens X) {K : Set X} (hK : IsCompact K)
    (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E :=
  HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_of_subset_isCompact hWa hint X₀ hK hX₀

/-- **Local embedded resolution of an arbitrary analytic set by one admissible sequence**: for a compact `K ⊆ X`, a relatively
compact open neighbourhood `U` of `K` and the conclusions of `exists_embeddedResolution_analytic_of_subset_isCompact` over
`U`. -/
theorem exists_embeddedResolution_analytic_local {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : U → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E :=
  HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_local hWa hint hK

/-- **Embedded resolution of an arbitrary analytic set over an open set contained in a compact set, relative to a simple normal
crossings boundary, by one admissible sequence**: `W` analytic with empty interior (not necessarily compact), `E₀` a divisor
with simple normal crossings with `W ⊆ closure (W \ |E₀|)`, `F = W_sing ∪ (W ∩ |E₀|)`, `X₀` open and contained in a compact
set.  One admissible sequence `f` of `(X₀, E₀|X₀)` with centres over `F ∩ X₀`, with divisor `E` (the strict transforms of the
members of `E₀|X₀`, then the new members): `E` has simple normal crossings, `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹(F ∩ X₀)`,
`f⁻¹(W_sing ∩ X₀) ⊆ Exc f`, `f` is an isomorphism over `X₀ \ F`, and the strict transform of `W ∩ X₀` is as in
`exists_embeddedResolution_analytic_of_subset_isCompact`, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_boundary_of_subset_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) (X₀ : Opens X) {K : Set X} (hK : IsCompact K)
    (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E :=
  HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_boundary_of_subset_isCompact hWa hint hE₀ hE₀W X₀ hK hX₀

/-- **Local embedded resolution of an arbitrary analytic set relative to a simple normal crossings boundary**: for a compact
`K ⊆ X`, a relatively compact open neighbourhood `U` of `K` and the conclusions of
`exists_embeddedResolution_analytic_boundary_of_subset_isCompact` over `U`. -/
theorem exists_embeddedResolution_analytic_boundary_local {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' ((Subtype.val : U → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : U → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E :=
  HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_boundary_local hWa hint hE₀ hE₀W hK

end Analytic

/-! ### Tools -/

section Tools

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Separation over an open set contained in a compact set, relative to a boundary**: `A, B ⊆ X` analytic, `A` with empty
interior, `A ⊆ closure (A \ B)`, `B ⊆ closure (B \ A)` (no compactness), `E₀` a divisor with simple normal crossings, `X₀` an
open set contained in a compact set. There is an admissible blowup sequence of `(X₀, E₀|X₀)` with centres over `A ∩ B ∩ X₀`,
with a divisor with simple normal crossings, after which the strict transforms of `A ∩ X₀` and `B ∩ X₀` are disjoint. -/
theorem exists_separation_of_subset_isCompact {A B : Set X} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hint : interior A = ∅) (hAB : A ⊆ closure (A \ B))
    (hBA : B ⊆ closure (B \ A)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (X₀ : Opens X) {K : Set X}
    (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (A ∩ B)) X₀' f E ∧ IsSNCDivisor n E ∧
      Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' A))
        (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' B)) :=
  HironakaEmbeddedAnalyticLocal.exists_separation_of_subset_isCompact hAa hBa hint hAB hBA hE₀ X₀ hK hX₀

/-- **Restriction of an admissible blowup sequence to an open subset**: if `f : Y → X` is an admissible blowup sequence of
`(X, E₀)` with centres over `F` and divisor `E`, and `O ⊆ X` is open, there are an admissible blowup sequence `f' : Y' → O` of
`(O, E₀|O)` with centres over `F ∩ O` and divisor `j⁻¹E`, and a holomorphic open embedding `j : Y' → Y` without exceptional
points, onto `f⁻¹(O)`, with `f ∘ j = f'` (as maps to `X`), `Exc f' = j⁻¹ Exc f`, and for every `S ⊆ X` the strict transform of
`S ∩ O` by `f'` is `j⁻¹` of the strict transform of `S` by `f`. -/
theorem exists_restrict_opens {E₀ : List (Set X)} {F : Set X} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n X E₀ F Y f E) (O : Opens X) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y') (_ : IsComplexManifold n Y')
      (f' : Y' → O) (j : Y' → Y),
      IsAdmissibleBlowupSequence n O (E₀.map ((Subtype.val : O → X) ⁻¹' ·)) ((Subtype.val : O → X) ⁻¹' F) Y' f'
        (E.map (j ⁻¹' ·)) ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ j ∧ Topology.IsOpenEmbedding j ∧
      exceptionalLocus n j = ∅ ∧ (∀ y, f (j y) = f' y) ∧ range j = f ⁻¹' O ∧
      exceptionalLocus n f' = j ⁻¹' exceptionalLocus n f ∧
      ∀ S : Set X, strictTransform n f' ((Subtype.val : O → X) ⁻¹' S) = j ⁻¹' strictTransform n f S :=
  HironakaBaseChange.IsAdmissibleBlowupSequence.exists_restrict_opens hf O

end Tools

end

end Hironaka
