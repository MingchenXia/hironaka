/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.API
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Resolution.HironakaBoundaryRelativelyCompact
import Hironaka.Resolution.CanonicalResolution
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Resolution.FactorizationDomain
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The public statements of the Hironaka library, completed

`Hironaka.API` (`hir:public-statements`) collects the first eleven public statements; this module adds the remaining
ones, in the same form: over an unbundled complex manifold, without the internal machinery (no marked ideal, tower,
invariant or domain condition in any statement, except the marked-ideal form of the canonical resolution itself),
and with the non-vanishing hypothesis of principalization written out (`∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠
0`). Together, `Hironaka.API` and `Hironaka.API2` are the public surface of the library.

## Principalization (Hironaka; Bierstone--Milman 1997, Theorem 1.10; Kollár, "Principalization, III")

* `exists_principalization_of_connected` (`X` compact and connected; `𝔞` nonzero somewhere);
* `exists_principalization_boundary_of_compactSpace` (relative to a simple normal crossings boundary, `X` compact),
  `exists_principalization_boundary_of_subset_isCompact` (over an open set contained in a compact set, relative to the restriction
  of the boundary) and `exists_principalization_boundary_local` (over a relatively compact neighbourhood of a compact set).

## Embedded resolution (Hironaka; Bierstone--Milman 1997, Theorem 1.6)

* `exists_embeddedResolution_local` (`V` irreducible, over a relatively compact neighbourhood of a compact set);
* `exists_embeddedResolution_pure_of_subset_isCompact` (`W` of pure dimension, over an open set contained in a compact set);
* `exists_embeddedResolution_boundary_of_isCompact`, `exists_embeddedResolution_boundary`,
  `exists_embeddedResolution_boundary_of_subset_isCompact`, `exists_embeddedResolution_boundary_local` (relative to a simple
  normal crossings boundary `E₀`, centres over `W_sing ∪ (W ∩ |E₀|)`);
* `exists_embeddedResolution_dimensionPart_of_isCompact`, `exists_embeddedResolution_dimensionPart`,
  `exists_embeddedResolution_dimensionPart_boundary_of_isCompact` (each dimension part `closure (Reg_k W)` of an analytic set whose
  components may have different dimensions, by its own sequence), with `eq_iUnion_dimensionPart` and
  `isComplexAnalyticSubset_dimensionPart`.

## The canonical resolution of marked ideals

* `canonicalResolution` (`hir:canonical-resolution` for the canonical invariant): over a compact base, the canonical resolution of
  every marked ideal of the domain, compatible with restriction to open sets and unique up to isomorphism over biholomorphisms.

These are restatements of theorems of `HironakaPrincipalizationBoundary`, `HironakaBoundaryRelativelyCompact`,
`HironakaRelativelyCompact`, `HironakaEmbeddedReducible`,
`HironakaEmbeddedBoundary`, `HironakaEmbeddedDimensionParts`, `HironakaPrincipalization`, `FactorizationDomain` and
`CanonicalResolution`; their proofs are at most a few lines.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.DivisorExponentAlong Hironaka.HironakaAdmissibleSequence Hironaka.HironakaEmbeddedDimensionParts

noncomputable section

variable {n : ℕ}

/-! ### Principalization -/

section Principalization

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Not the zero ideal, in elementary terms**: if some germ of `𝔞` does not vanish identically near its point, `𝔞` is not
contained in the ideal of `X`. -/
theorem not_le_vanishingIdeal_univ {𝔞 : GermIdeal n X} (h : ∃ x g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) :
    ¬ 𝔞.Le (vanishingIdeal (n := n) (univ : Set X)) := by
  obtain ⟨x, g, hg, hfreq⟩ := h
  intro hle
  have h0 := (hle x g hg).2
  exact hfreq (h0.mono fun y hy => not_not.mpr (hy (mem_univ y)))

/-- **Principalization on a compact connected manifold** (Hironaka): a coherent ideal sheaf `𝔞` on a compact connected complex
manifold, some germ of which does not vanish identically near its point, becomes invertible with simple normal crossings support
after an admissible blowup sequence with centres over `Z(𝔞)`, which is an isomorphism over `X \ Z(𝔞)` (on a connected manifold a
coherent ideal which is not zero is nonzero at every point). -/
theorem exists_principalization_of_connected [CompactSpace X] [ConnectedSpace X] {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) (hne : ∃ x g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] 𝔞.zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ :=
  Hironaka.exists_principalization h𝔞 (Hironaka.forall_isNonzeroAlongAt_univ_iff.mp fun x =>
    FactorizationDomain.isNonzeroAlongAt_of_not_le FactorizationDomain.isClosedConnectedSubmanifold_univ h𝔞
      (not_le_vanishingIdeal_univ hne) x (mem_univ x))

/-- **Principalization relative to a simple normal crossings boundary on a compact manifold** (Kollár, "Principalization, III",
analytic form): the divisor `E` of the admissible sequence of `(X, E₀)` starts with the strict transforms of the members of `E₀`,
and the support of `D` is the union of the members created by the blowups. -/
theorem exists_principalization_boundary_of_compactSpace [CompactSpace X] {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X') (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus X' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f 𝔞 = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n f 𝔞.zeroLocusᶜ :=
  HironakaPrincipalizationBoundary.exists_principalization_boundary_of_compactSpace h𝔞
    (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) hE₀

/-- **Principalization relative to a simple normal crossings boundary over an open set contained in a compact set** (any `X`,
no compactness of `Z(𝔞)`; relative to the restriction of `E₀`). -/
theorem exists_principalization_boundary_of_subset_isCompact {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (D : EffectiveDivisor n X₀') (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) X₀' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : X₀ → X) 𝔞) = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' 𝔞.zeroLocus)ᶜ :=
  HironakaBoundaryRelativelyCompact.exists_principalization_boundary_of_subset_isCompact h𝔞
    (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) hE₀ X₀ hK hX₀

/-- **Local principalization relative to a simple normal crossings boundary** (any `X`): over a relatively compact open
neighbourhood `U` of a given compact set `K`. -/
theorem exists_principalization_boundary_local {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ x, ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) {K : Set X}
    (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (D : EffectiveDivisor n U') (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) U' f E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) f (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔞) = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = f ⁻¹' ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' 𝔞.zeroLocus)ᶜ :=
  HironakaBoundaryRelativelyCompact.exists_principalization_boundary_local h𝔞
    (Hironaka.forall_isNonzeroAlongAt_univ_iff.mpr hne) hE₀ hK

end Principalization

/-! ### Embedded resolution -/

section EmbeddedResolution

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Local embedded resolution** (Hironaka; `X` any complex manifold, `V` a closed irreducible analytic subvariety): over a
relatively compact open neighbourhood `U` of a given compact set `K`, an admissible blowup sequence with centres over `V_sing`,
`E` with simple normal crossings, `Exc f = ⋃ E = f⁻¹(V_sing ∩ U)`, `f` an isomorphism off `V_sing`, and the strict transform of
`V ∩ U` a closed submanifold of dimension `dim V` at each of its points, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_local (V : ClosedIrreducibleAnalyticSubvariety n X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' singularLocus V) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) E :=
  HironakaRelativelyCompact.exists_embeddedResolution_local_admissible V hK

/-- **Embedded resolution of an analytic set of pure dimension `d < n` over an open set contained in a compact set** (possibly
reducible, no compactness of `W`; `X` any complex manifold). -/
theorem exists_embeddedResolution_pure_of_subset_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E :=
  HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_subset_isCompact hWa hd hpure X₀ hK hX₀

/-- **Embedded resolution relative to a simple normal crossings boundary** (Hironaka; Bierstone--Milman 1997, Theorem 1.6 with an
initial divisor; `W` compact, `X` any complex manifold): for `W` analytic of pure dimension `d < n`, `E₀` with simple normal
crossings and no member of `E₀` containing a nonempty relatively open subset of `W`, an admissible blowup sequence of `(X, E₀)`
with centres over `F = W_sing ∪ (W ∩ |E₀|)`, `E` with simple normal crossings, `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F`,
`f⁻¹(W_sing) ⊆ Exc f`, `f` an isomorphism over `X \ F`, and the strict transform of `W` a closed submanifold of dimension `d` at
each of its points with only normal crossings with `E`. -/
theorem exists_embeddedResolution_boundary_of_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact hWa hK hd hpure hE₀ hE₀W

/-- **Embedded resolution relative to a simple normal crossings boundary in a compact manifold** (`X` compact). -/
theorem exists_embeddedResolution_boundary [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  HironakaEmbeddedBoundary.exists_embeddedResolution_boundary hWa hd hpure hE₀ hE₀W

/-- **Embedded resolution relative to a simple normal crossings boundary over an open set contained in a compact set** (any
`W`, relative to the restriction of `E₀`). -/
theorem exists_embeddedResolution_boundary_of_subset_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E :=
  HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact hWa hd hpure hE₀ hE₀W X₀ hK hX₀

/-- **Local embedded resolution relative to a simple normal crossings boundary** (any `X`, `W` of pure dimension `d < n` with
`W ⊆ closure (W \ |E₀|)`): over a relatively compact open neighbourhood `U` of a given compact set `K`. -/
theorem exists_embeddedResolution_boundary_local {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E :=
  HironakaBoundaryRelativelyCompact.exists_embeddedResolution_boundary_local hWa hd hpure hE₀ hE₀W hK

/-- **An analytic set is the union of its dimension parts** `W⁽ᵏ⁾ = closure (Reg_k W)`, `k ≤ n`. -/
theorem eq_iUnion_dimensionPart {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) :
    W = ⋃ k : Fin (n + 1), dimensionPart (n := n) W k :=
  HironakaEmbeddedDimensionParts.eq_iUnion_dimensionPart hWa

/-- **The dimension parts of an analytic set are analytic and of pure dimension.** -/
theorem isComplexAnalyticSubset_dimensionPart {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (dimensionPart (n := n) W k) ∧
      dimensionPart (n := n) W k ⊆ closure (regularLocus (n := n) (dimensionPart (n := n) W k) k) :=
  ⟨HironakaEmbeddedDimensionParts.isComplexAnalyticSubset_dimensionPart hWa k,
    subset_closure_regularLocus_dimensionPart hWa.isClosed k⟩

/-- **Embedded resolution of a dimension part of a compact analytic set** (the components of `W` may have different
dimensions; each part by its own sequence). -/
theorem exists_embeddedResolution_dimensionPart_of_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {k : ℕ} (hk : k < n) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X []
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  HironakaEmbeddedDimensionParts.exists_embeddedResolution_dimensionPart_of_isCompact hWa hK hk

/-- **Embedded resolution of a dimension part of an analytic set in a compact manifold.** -/
theorem exists_embeddedResolution_dimensionPart [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {k : ℕ} (hk : k < n) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X []
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  HironakaEmbeddedDimensionParts.exists_embeddedResolution_dimensionPart hWa hk

/-- **Embedded resolution of a dimension part relative to a simple normal crossings boundary** (`W` compact). -/
theorem exists_embeddedResolution_dimensionPart_boundary_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {k : ℕ} (hk : k < n) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ∪
          dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (dimensionPart (n := n) W k \
        regularLocus (n := n) (dimensionPart (n := n) W k) k ∪ dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ⊆
        exceptionalLocus n f ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ∪
        dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  HironakaEmbeddedDimensionParts.exists_embeddedResolution_dimensionPart_boundary_of_isCompact hWa hK hk hE₀ hE₀W

end EmbeddedResolution

/-! ### The canonical resolution of marked ideals -/

section Canonical

open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen
open Hironaka.MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (IsCanonicalSegment)
open Hironaka.ResolutionInvariantOrder (IsInvUSCOn)

/-- **The canonical resolution of marked ideals** (`hir:canonical-resolution` for the canonical invariant
`CanonicalCentres.canonicalInvariant n`): over a compact complex manifold of dimension `n`, every marked ideal of the domain has a
resolution which is a canonical segment without empty centres, the invariant is upper semicontinuous along canonical segments, the
restriction of the resolution to every open set is canonical, and every canonical resolution of the pullback along a
biholomorphism is isomorphic to it over that biholomorphism. -/
theorem canonicalResolution {X : CMfd.{u} n} [CompactSpace X] {𝔪 : MarkedIdeal n X} (h : IsInvDomain n 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsGeoResolution 𝔪 T ∧
      IsCanonicalSegment 𝔪 ((CanonicalCentres.canonicalInvariant n).inv 𝔪) T ∧
      (∀ {Y₁ : CMfd.{u} n} (T₁ : BlowupTower X Y₁), IsCanonical 𝔪 ((CanonicalCentres.canonicalInvariant n).inv 𝔪) T₁ →
        IsInvUSCOn ((CanonicalCentres.canonicalInvariant n).inv 𝔪 T₁) (geoTransformAlong 𝔪 T₁).cosupp) ∧
      (∀ U : Opens X, IsCanonical (pullback (Subtype.val : U → X) 𝔪)
        ((CanonicalCentres.canonicalInvariant n).inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' : CMfd.{u} n}
        (T' : BlowupTower X' Y'),
          IsCanonicalSegment (pullback Φ 𝔪) ((CanonicalCentres.canonicalInvariant n).inv (pullback Φ 𝔪)) T' →
          IsGeoResolution (pullback Φ 𝔪) T' →
            ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T' T χ) :=
  CanonicalResolution.canonicalResolution_canonicalInvariant h

end Canonical

end

end Hironaka
