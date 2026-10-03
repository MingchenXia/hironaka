/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Resolution.HironakaSeparation
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The public statements of the Hironaka library, III: analytic sets whose components have different dimensions

`Hironaka.API` (`hir:public-statements`) and `Hironaka.API2` (`hir:public-statements-complete`) are unchanged; this
module adds, in the same form (over an unbundled complex manifold, without marked ideals, towers, invariants or
domain conditions):

## Embedded resolution of an arbitrary analytic set by one sequence (Hironaka; Bierstone--Milman 1997, Theorem 1.6)

For a compact analytic set `W` with empty interior (its components may have different dimensions), with
`W_sing = W \ ⋃ k, Reg_k W` (the points at which `W` is not a submanifold of any dimension) and the dimension parts
`W⁽ᵏ⁾ = closure (Reg_k W)` (`HironakaEmbeddedDimensionParts.dimensionPart`):

* `exists_embeddedResolution_analytic_of_isCompact` (`W` compact, any `X`) and `exists_embeddedResolution_analytic` (`X`
  compact): ONE admissible sequence of `(X, [])` with centres over `W_sing`, `E` SNC, `Exc f = ⋃ E = f⁻¹(W_sing)`, `f` an
  isomorphism over `X \ W_sing`, the strict transform `W'` a closed submanifold which is the union of the pairwise disjoint strict
  transforms of the `W⁽ᵏ⁾` (`k < n`), of dimension `k` along the strict transform of `W⁽ᵏ⁾`, with normal crossings with `E`;
* `exists_embeddedResolution_analytic_boundary_of_isCompact`, `exists_embeddedResolution_analytic_boundary`: the same relative to
  a simple normal crossings divisor `E₀` none of whose members contains a nonempty relatively open subset of `W`, with centres over
  `W_sing ∪ (W ∩ |E₀|)`.

## Tools

* `exists_separation`: principalization of `𝓘_A + 𝓘_B` relative to a boundary makes the strict transforms of `A` and `B`
  disjoint (each of `A`, `B` the closure of its part off the other);
* `isAdmissibleBlowupSequence_comp`, `isIsomorphismOver_compl_of_isAdmissibleBlowupSequence`,
  `exceptionalLocus_subset_of_isAdmissibleBlowupSequence`: admissible sequences compose, and an admissible sequence with
  centres over `F` is an isomorphism over `X \ F`, its exceptional locus lying in the members it creates, which lie over `F`.

These are restatements of theorems of `HironakaEmbeddedAnalytic`, `HironakaSeparation` and `HironakaAdmissibleCalculus`; their
proofs are one line.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence Hironaka.HironakaEmbeddedDimensionParts

noncomputable section

variable {n : ℕ}

/-! ### Embedded resolution of an arbitrary analytic set -/

section Analytic

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Embedded resolution of an arbitrary compact analytic set by one admissible sequence** (Hironaka; Bierstone--Milman 1997,
Theorem 1.6): `W ⊆ X` compact analytic with empty interior, its components of any dimensions; `W_sing = W \ ⋃ k, Reg_k W`.
One admissible sequence `f` of `(X, [])` with centres over `W_sing`, with divisor `E`: `E` has simple normal crossings,
`Exc f = ⋃ E = f⁻¹(W_sing)`, `f` is an isomorphism over `X \ W_sing`, the strict transform of `W` is a closed submanifold, the
union of the pairwise disjoint strict transforms of the dimension parts `W⁽ᵏ⁾ = closure (Reg_k W)` (`k < n`), of dimension `k`
at each point of the strict transform of `W⁽ᵏ⁾`, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_of_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hint : interior W = ∅) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ ⋃ k : ℕ, regularLocus (n := n) W k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∧
      IsIsomorphismOver n f (W \ ⋃ k : ℕ, regularLocus (n := n) W k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic_of_isCompact hWa hK hint

/-- **Embedded resolution of an arbitrary analytic set in a compact manifold by one admissible sequence** (`X` compact; the
conclusions of `exists_embeddedResolution_analytic_of_isCompact`). -/
theorem exists_embeddedResolution_analytic [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ ⋃ k : ℕ, regularLocus (n := n) W k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∧
      IsIsomorphismOver n f (W \ ⋃ k : ℕ, regularLocus (n := n) W k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic hWa hint

/-- **Embedded resolution of an arbitrary compact analytic set relative to a simple normal crossings boundary, by one admissible
sequence**: `W` compact analytic with empty interior, `E₀` a divisor with simple normal crossings with `W ⊆ closure (W \ |E₀|)`,
`F = W_sing ∪ (W ∩ |E₀|)`.  One admissible sequence `f` of `(X, E₀)` with centres over `F`, with divisor `E` (the strict
transforms of the members of `E₀`, then the new members): `E` has simple normal crossings, `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F`,
`f⁻¹(W_sing) ⊆ Exc f`, `f` is an isomorphism over `X \ F`, and the strict transform of `W` is as in
`exists_embeddedResolution_analytic_of_isCompact`, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_boundary_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic_boundary_of_isCompact hWa hK hint hE₀ hE₀W

/-- **Embedded resolution of an arbitrary analytic set in a compact manifold relative to a simple normal crossings boundary, by
one admissible sequence** (`X` compact). -/
theorem exists_embeddedResolution_analytic_boundary [CompactSpace X] {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ ⋃ k : ℕ, regularLocus (n := n) W k) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((W \ ⋃ k : ℕ, regularLocus (n := n) W k) ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic_boundary hWa hint hE₀ hE₀W

end Analytic

/-! ### Tools -/

section Tools

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Separating two analytic sets by principalization of `𝓘_A + 𝓘_B`, relative to a boundary**: `A, B ⊆ X` analytic, `A` with
empty interior, `A ∩ B` compact, `A ⊆ closure (A \ B)`, `B ⊆ closure (B \ A)`, `E₀` a divisor with simple normal crossings.
There is an admissible blowup sequence of `(X, E₀)` with centres over `A ∩ B`, with a divisor with simple normal crossings,
after which the strict transforms of `A` and `B` are disjoint. -/
theorem exists_separation {A B : Set X} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hint : interior A = ∅) (hK : IsCompact (A ∩ B))
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (A ∩ B) X' f E ∧ IsSNCDivisor n E ∧
      Disjoint (strictTransform n f A) (strictTransform n f B) :=
  HironakaSeparation.exists_separation hAa hBa hint hK hAB hBA hE₀

/-- **Admissible sequences compose**: an admissible sequence of `(Y, E)` with centres over `f⁻¹ F`, after an admissible sequence
`f` of `(X, E₀)` with centres over `F` and divisor `E`, gives an admissible sequence of `(X, E₀)` with centres over `F`. -/
theorem isAdmissibleBlowupSequence_comp {E₀ : List (Set X)} {F : Set X} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n X E₀ F Y f E) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {g : Z → Y} {E' : List (Set Z)}
    (hg : IsAdmissibleBlowupSequence n Y E (f ⁻¹' F) Z g E') :
    IsAdmissibleBlowupSequence n X E₀ F Z (f ∘ g) E' :=
  HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.comp hf hg

/-- **An admissible sequence with centres over `F` is an isomorphism over `X \ F`.** -/
theorem isIsomorphismOver_compl_of_isAdmissibleBlowupSequence {E₀ : List (Set X)} {F : Set X} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) : IsIsomorphismOver n f Fᶜ :=
  HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl h

/-- **The exceptional locus of an admissible sequence lies in the members it creates, which lie over the centres.** -/
theorem exceptionalLocus_subset_of_isAdmissibleBlowupSequence {E₀ : List (Set X)} {F : Set X} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X} {E : List (Set Y)}
    (h : IsAdmissibleBlowupSequence n X E₀ F Y f E) :
    exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧ (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' F :=
  HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop h

end Tools

end

end Hironaka
