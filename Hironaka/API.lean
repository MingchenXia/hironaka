/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The public statements of the Hironaka library, in elementary terms

This module collects the final public statements of resolution of singularities proved in this library: over an
unbundled complex manifold, without the internal machinery (no marked ideal, tower, invariant or domain condition in
any statement), and with the non-vanishing hypothesis of principalization written out:

  `∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0`

("at every point some germ of `𝔞` does not vanish identically near the point"), in place of the internal predicate
`DivisorExponentAlong.IsNonzeroAlongAt univ 𝔞 x` (equivalent: `forall_isNonzeroAlongAt_univ_iff`).

## Principalization (Hironaka; Bierstone--Milman 1997, Theorem 1.10)

For a coherent ideal `𝔞` nonzero at every point: an admissible blowup sequence `f : X' → X` (centres in normal crossings with the
divisor so far, over `Z(𝔞)`) with divisor `E` and an effective divisor `D` such that `f^*𝔞 = 𝒪(-D)`, `E` has simple normal
crossings, `supp D = ⋃ E = f⁻¹ Z(𝔞)` and `f` is an isomorphism over `X \ Z(𝔞)`:
* `exists_principalization` (`X` compact), `exists_principalization_of_isCompact` (only `Z(𝔞)` compact),
  `exists_principalization_of_subset_isCompact` (over any open set contained in a compact set), `exists_principalization_local`
  (over a relatively compact neighbourhood of a compact set), `exists_principalization_boundary` (relative to a simple normal
  crossings boundary `E₀`, `Z(𝔞)` compact).

## Embedded resolution (Hironaka; Bierstone--Milman 1997, Theorem 1.6)

An admissible blowup sequence with centres over the singular set, `E` with simple normal crossings, `Exc f = ⋃ E = f⁻¹(V_sing)`,
`f` an isomorphism off `V_sing`, and the strict transform smooth with normal crossings with `E`:
* `exists_embeddedResolution` (`X` compact, `V` irreducible; the strict transform connected of dimension `dim V`),
  `exists_embeddedResolution_of_isCompact` (`V` compact), `exists_embeddedResolution_of_subset_isCompact` (over any open set
  contained in a compact set);
* `exists_embeddedResolution_pure` (`X` compact) and `exists_embeddedResolution_pure_of_isCompact` (`W` compact): an analytic set
  `W` of pure dimension `d < n`, possibly reducible.

These are restatements of the theorems of `HironakaAdmissibleSequence`, `HironakaRelativelyCompact`,
`HironakaPrincipalizationBoundary` and `HironakaEmbeddedReducible`; their proofs are one line.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.DivisorExponentAlong Hironaka.HironakaAdmissibleSequence

noncomputable section

variable {n : ℕ}

/-- **The non-vanishing hypothesis of principalization in elementary terms**: `𝔞` is nonzero along `X` at every point iff at
every point some germ of `𝔞` does not vanish identically near the point. -/
theorem forall_isNonzeroAlongAt_univ_iff {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    {𝔞 : GermIdeal n X} :
    (∀ x, IsNonzeroAlongAt univ 𝔞 x) ↔ ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0 :=
  forall_congr' fun _ => isNonzeroAlongAt_univ_iff_exists

/-! ### Principalization -/

section Principalization

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Principalization** (Hironaka; `X` compact): a coherent ideal sheaf `𝔞` on a compact complex manifold, such that at every
point some germ of `𝔞` does not vanish identically near the point, becomes invertible with simple normal crossings support
after an admissible blowup sequence with centres over `Z(𝔞)`, which is an isomorphism over `X \ Z(𝔞)`. -/
theorem exists_principalization [CompactSpace X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] 𝔞.zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ :=
  exists_principalization_admissible h𝔞 (forall_isNonzeroAlongAt_univ_iff.mpr hne)

/-- **Principalization with a compact zero locus** (`X` any complex manifold, `Z(𝔞)` compact). -/
theorem exists_principalization_of_isCompact {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) (hZ : IsCompact 𝔞.zeroLocus) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] 𝔞.zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ :=
  HironakaAdmissibleSequence.exists_principalization_of_isCompact h𝔞 (forall_isNonzeroAlongAt_univ_iff.mpr hne) hZ

/-- **Principalization over an open set contained in a compact set** (`X` any complex manifold). -/
theorem exists_principalization_of_subset_isCompact {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) (X₀ : Opens X) {K : Set X} (hK : IsCompact K)
    (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (D : EffectiveDivisor n X₀') (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) X₀' f E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus)ᶜ :=
  HironakaRelativelyCompact.exists_principalization_of_subset_isCompact h𝔞
    (forall_isNonzeroAlongAt_univ_iff.mpr hne) X₀ hK hX₀

/-- **Local principalization** (`X` any complex manifold): over a relatively compact open neighbourhood `U` of a given compact
set `K`. -/
theorem exists_principalization_local {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (D : EffectiveDivisor n U') (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) U' f E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus)ᶜ :=
  HironakaRelativelyCompact.exists_principalization_local_admissible h𝔞 (forall_isNonzeroAlongAt_univ_iff.mpr hne) hK

/-- **Principalization relative to a simple normal crossings boundary `E₀`** (`X` any complex manifold, `Z(𝔞)` compact): the
divisor `E` of the admissible sequence of `(X, E₀)` starts with the strict transforms of the members of `E₀`, and the support of
`D` is the union of the members created by the blowups. -/
theorem exists_principalization_boundary {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) (hZ : IsCompact 𝔞.zeroLocus) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus X' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ :=
  HironakaPrincipalizationBoundary.exists_principalization_boundary h𝔞 (forall_isNonzeroAlongAt_univ_iff.mpr hne) hZ hE₀

end Principalization

/-! ### Embedded resolution -/

section EmbeddedResolution

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Embedded resolution** (Hironaka; `X` compact, `V` a closed irreducible analytic subvariety). -/
theorem exists_embeddedResolution [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularLocus V) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E :=
  exists_embeddedResolution_admissible V

/-- **Embedded resolution of a compact subvariety** (`X` any complex manifold). -/
theorem exists_embeddedResolution_of_isCompact (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hK : IsCompact V.carrier) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularLocus V) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularLocus V ∧
      IsIsomorphismOver n f (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold n (strictTransform n f V.carrier) V.dim ∧
      HasNormalCrossings n (strictTransform n f V.carrier) E :=
  HironakaAdmissibleSequence.exists_embeddedResolution_of_isCompact V hK

/-- **Embedded resolution over an open set contained in a compact set** (`X` any complex manifold). -/
theorem exists_embeddedResolution_of_subset_isCompact (V : ClosedIrreducibleAnalyticSubvariety n X)
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' singularLocus V) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' V.carrier)) E :=
  HironakaRelativelyCompact.exists_embeddedResolution_of_subset_isCompact V X₀ hK hX₀

/-- **Embedded resolution of an analytic set of pure dimension `d < n`** (possibly reducible; `X` compact). -/
theorem exists_embeddedResolution_pure [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedReducible.exists_embeddedResolution_pure hWa hd hpure

/-- **Embedded resolution of a compact analytic set of pure dimension `d < n`** (possibly reducible; `X` any complex
manifold). -/
theorem exists_embeddedResolution_pure_of_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_isCompact hWa hK hd hpure

end EmbeddedResolution

end

end Hironaka
