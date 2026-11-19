import Hironaka.Resolution.FactorizationFromResolution
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Invariant.ResolutionInvariantSeq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The two Hironaka conclusions from a resolution invariant with per-sequence local finiteness

Hironaka phases H5a / H5b (TN23), blueprint `mc:hironaka-from-seq-invariant` (chapter `maximal-contact.tex`), written
after an independent review (3 October 2026) of the induction over growing sequences.  Sources: Copy-4,
`lem:relative-principalization`; Włodarczyk 2005 (`wlodarczyk05-hironaka`), embedded resolution from the canonical
resolution of `(X, X, ∅, 𝓘_V, 1)`.

The reductions of the two Hironaka statements were proved generic in the resolutions:
`FactorizationFromResolution.factorizationData_of_exists_resolution` (H5a) takes the existence of resolutions of the marked
ideals of the domain, and `EmbeddedFromResolution.exists_embeddedResolution_data_of_isCanonical` (H5b) takes a value function
with four properties and a canonical segment with empty final cosupport.  The wrappers that supply these from a resolution
invariant (`EmbeddedFromResolution.exists_embeddedResolution_data_of_resolutionInvariant(_of_isCoherent)`) are typed over the
superseded structure `ResolutionInvariantExt.ResolutionInvariant` (uniform property (8)), which the induction of
`hir:canonical-centres` cannot produce (the author's decision of 3 October 2026).  This module ADDS their forms for the
structure of that decision, `ResolutionInvariantSeq.ResolutionInvariant` (property (8) along growing sequences, resolution
by dependent choice); the earlier wrappers stay unchanged.

## Main results

* `embeddingFields_of_seq`: the four properties used by H5b, from `IsInvValue`;
* `exists_isGeoResolution_of_seq`: the existence hypothesis of H5a, from the driver `exists_isGeoResolution_isCanonical`;
* **`factorizationData_of_seq`**: from a resolution invariant in dimension `≤ j` with `n ≤ j`, the body of
  `RelativePrincipalization.FactorizationData W k 𝔞` (the conclusion of `exists_factorizationData`), under exactly that
  statement's hypotheses;
* `exists_embeddedResolution_data_of_seq`, **`exists_embeddedResolution_data_of_seq_of_isCoherent`**: from a resolution
  invariant in dimension `≤ k` with `n ≤ k` and the coherence of `𝓘_V` (Cartan's theorem), the conclusion of
  `EmbeddedResolution.exists_embeddedResolution_smoothData` with its field written out.

H4 provides such an invariant, `CanonicalCentres.canonicalInvariant n : ResolutionInvariantSeq.ResolutionInvariant n n (ValTy n)`,
and each Hironaka statement is discharged in place by one application of the results here (for H5b with the coherence of
`𝓘_V` from `CartanIrreducible.cartanCoherence`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u v

namespace Hironaka.HironakaFromSeqInvariant

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor
  Hironaka.ResolutionInvariantSeq
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ} {Λ : Type v} [LinearOrder Λ]

/-! ### The inputs of the two reductions -/

/-- **The four properties used by the embedded-resolution argument**, (1), (4), (5), (6), from a resolution invariant of the
per-sequence structure. -/
theorem embeddingFields_of_seq {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ) :
    EmbeddedFromResolution.EmbeddingFields n k R.inv :=
  ⟨R.isInvValue.admissible, R.isInvValue.emptyStep, R.isInvValue.restrictOpen, R.isInvValue.towerIso⟩

/-- **The existence hypothesis of relative principalization**: over a compact base, every marked ideal of the domain in
dimension `≤ j` has a multiple test blow-up with empty final cosupport (the driver by dependent choice,
`ResolutionInvariantSeq.exists_isGeoResolution_isCanonical`). -/
theorem exists_isGeoResolution_of_seq {j : ℕ} (R : ResolutionInvariant.{u, v} n j Λ) :
    ∀ {X : CMfd.{u} n} [CompactSpace X] (𝔪 : MarkedIdeal n X), IsInvDomain j 𝔪 →
      ∃ (Z : CMfd.{u} n) (T : BlowupTower X Z), IsGeoResolution 𝔪 T := by
  intro X _ 𝔪 h
  obtain ⟨Z, T, -, hres⟩ := exists_isGeoResolution_isCanonical R h
  exact ⟨Z, T, hres⟩

/-! ### Relative principalization (H5a) -/

/-- **Relative principalization from a resolution invariant** (`mc:hironaka-from-seq-invariant`, H5a): for a resolution
invariant in dimension `≤ j` with `n ≤ j`, under the hypotheses of `RelativePrincipalization.exists_factorizationData` (compact
connected `Y`, `W ≠ Y` a closed connected submanifold of dimension `k`, `𝔞` coherent and not contained in `𝓘_W`), the body of
`RelativePrincipalization.FactorizationData W k 𝔞` (`FactorizationFromResolution.factorizationData_of_exists_resolution`). -/
theorem factorizationData_of_seq {j : ℕ} (R : ResolutionInvariant.{u, v} n j Λ) (hnj : n ≤ j) {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
    (W : Set Y) (k : ℕ) (hW : IsClosedConnectedSubmanifold n W k) (hWY : W ≠ univ) (𝔞 : GermIdeal n Y)
    (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) W)) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y W Y' f ∧
      IsConnected (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W,
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n f W) ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal :=
  FactorizationFromResolution.factorizationData_of_exists_resolution hnj (exists_isGeoResolution_of_seq R) W k hW hWY 𝔞
    h𝔞 hres

/-! ### Embedded resolution (H5b) -/

/-- **Embedded resolution from a resolution invariant, given the domain hypothesis** (`mc:hironaka-from-seq-invariant`, H5b):
for a resolution invariant in dimension `≤ k`, a compact `X` and `V` with `(X, X, ∅, 𝓘_V, 1)` in the domain, the conclusion of
`EmbeddedResolution.exists_embeddedResolution_smoothData` (its field written out), from the canonical resolution of the driver
(`EmbeddedFromResolution.exists_embeddedResolution_data_of_isCanonical`). -/
theorem exists_embeddedResolution_data_of_seq {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  have : CompactSpace (CMfd.of (n := n) X) := ‹CompactSpace X›
  obtain ⟨Y, T, hcan, hres⟩ := exists_isGeoResolution_isCanonical R hdom
  exact EmbeddedFromResolution.exists_embeddedResolution_data_of_isCanonical (embeddingFields_of_seq R) V hdom
    ⟨Y, T, hcan, hres.2⟩

/-- **Embedded resolution from a resolution invariant and Cartan's theorem** (`mc:hironaka-from-seq-invariant`, H5b): for a
resolution invariant in dimension `≤ k` with `n ≤ k`, a compact `X` and a subvariety `V` whose ideal sheaf is coherent, the
conclusion of `EmbeddedResolution.exists_embeddedResolution_smoothData` (its field written out).  For `dim V = n` the identity
(`EmbeddedFromResolution.exists_embeddedResolution_data_of_dim_eq`); otherwise `exists_embeddedResolution_data_of_seq` with the
domain hypothesis `EmbeddedFromResolution.isInvDomain_vanishingIdeal_of_dim_lt`.  The per-sequence counterpart of
`EmbeddedFromResolution.exists_embeddedResolution_data_of_resolutionInvariant_of_isCoherent`. -/
theorem exists_embeddedResolution_data_of_seq_of_isCoherent {k : ℕ} (R : ResolutionInvariant.{u, v} n k Λ)
    (hnk : n ≤ k) {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  rcases V.dim_le.lt_or_eq with h | h
  · exact exists_embeddedResolution_data_of_seq R V
      (EmbeddedFromResolution.isInvDomain_vanishingIdeal_of_dim_lt (M := CMfd.of (n := n) X) hnk V h hcoh)
  · exact EmbeddedFromResolution.exists_embeddedResolution_data_of_dim_eq V h

end

end Hironaka.HironakaFromSeqInvariant
