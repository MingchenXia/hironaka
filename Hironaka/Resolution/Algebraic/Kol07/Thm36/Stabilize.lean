/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IndexTransport
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Stabilisation along a coordinate inclusion

The proof of [Kol07, Theorem 36] increases `n` at will through a further embedding
`𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`. This file supplies the closed-embedding data of the coordinate inclusions
between the triples `(𝔸ⁿ, I, ∅)` and `(𝔸ⁿ⁺ᵐ, I.map (coordInclFst n m), ∅)` (and the second block
likewise), the situation in which the principalization functor commutes with closed embeddings
[Kol07, Theorem 35 (5)], and derives the stabilisation identity for `BR_affine`:

* `affineSpaceTriple_closedEmbedding_coordInclFst` and its second-block counterpart
  `affineSpaceTriple_closedEmbedding_coordInclSnd`: the coordinate inclusions are closed
  embeddings of triples (`Triple.ClosedEmbedding`): over `k`, the ideal of the larger triple is
  the image of the smaller one's, and the empty boundaries correspond;
* `BR_affine_stabilize_of_BP_eq_pushforward`: stabilising along `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` does not change
  `BR_affine`, granted the identity `BP (𝔸ⁿ⁺ᵐ, …) = (BP (𝔸ⁿ, …)).pushforward` of Theorem 35 (5),
  which `Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly` supplies.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme.BlowUpSequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
/-- The coordinate inclusion `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` is a closed embedding of triples
`(𝔸ⁿ, I, ∅) ↪ (𝔸ⁿ⁺ᵐ, I.map (coordInclFst n m), ∅)` in the sense of `Triple.ClosedEmbedding`, the
situation of [Kol07, Theorem 35 (5)]. -/
theorem affineSpaceTriple_closedEmbedding_coordInclFst {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) (hI' : IsNonzeroEverywhere (I.map (coordInclFst n m))) :
    (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI').ClosedEmbedding
      (affineSpaceTriple k n I hI) (coordInclFst n m) :=
  ⟨coordInclFst_comp_affineSpaceToSpec n m, rfl, (empty_comap (coordInclFst n m)).symm⟩

/-- The coordinate inclusion, typed as a morphism between the ambients of the two affine-space
triples (which are the affine spaces by definition), is a closed immersion: the instance
`isClosedImmersion_coordInclFst` read at those types, so that the pushforward of sequences and
[Kol07, Theorem 35 (5)] elaborate on the triples. -/
instance isClosedImmersion_coordInclFst_affineSpaceTriple {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) (hI' : IsNonzeroEverywhere (I.map (coordInclFst n m))) :
    IsClosedImmersion (X := (affineSpaceTriple k n I hI).X.left)
      (Y := (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI').X.left)
      (coordInclFst n m) :=
  isClosedImmersion_coordInclFst n m

/-- The same instance with the target read as the affine space itself. -/
instance isClosedImmersion_coordInclFst_affineSpaceTriple' {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) :
    IsClosedImmersion (X := (affineSpaceTriple k n I hI).X.left) (coordInclFst n m) :=
  isClosedImmersion_coordInclFst n m

/-- Stabilisation along `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` does not change `BR_affine` [Kol07, Theorem 36, proof],
granted the identity of [Kol07, Theorem 35 (5)] for the two principalization sequences. -/
theorem BR_affine_stabilize_of_BP_eq_pushforward {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) (hI' : IsNonzeroEverywhere (I.map (coordInclFst n m)))
    (hBP : Hironaka.Sequence.BP (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI') =
      (Hironaka.Sequence.BP (affineSpaceTriple k n I hI)).pushforward
        (coordInclFst n m : (affineSpaceTriple k n I hI).X.left ⟶
          (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI').X.left))
    {X : Scheme.{u}} (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k))) :
    BR_affine (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI')
        (emb ≫ coordInclFst n m) =
      BR_affine (affineSpaceTriple k n I hI) emb :=
  BR_affine_comp_eq_of_BP_eq_pushforward (affineSpaceTriple k n I hI)
    (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hI') (coordInclFst n m) hBP rfl emb

/-- The second coordinate inclusion, typed at the triples' ambients, is a closed immersion. -/
instance isClosedImmersion_coordInclSnd_affineSpaceTriple {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin m) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) (hI' : IsNonzeroEverywhere (I.map (coordInclSnd n m))) :
    IsClosedImmersion (X := (affineSpaceTriple k m I hI).X.left)
      (Y := (affineSpaceTriple k (n + m) (I.map (coordInclSnd n m)) hI').X.left)
      (coordInclSnd n m) :=
  isClosedImmersion_coordInclSnd n m

/-- The same instance with the target read as the affine space itself. -/
instance isClosedImmersion_coordInclSnd_affineSpaceTriple' {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin m) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) :
    IsClosedImmersion (X := (affineSpaceTriple k m I hI).X.left) (coordInclSnd n m) :=
  isClosedImmersion_coordInclSnd n m

omit [CharZero k] in
/-- The second coordinate inclusion `𝔸ᵐ ↪ 𝔸ⁿ⁺ᵐ` is a closed embedding of triples
`(𝔸ᵐ, I, ∅) ↪ (𝔸ⁿ⁺ᵐ, I.map (coordInclSnd n m), ∅)`, the situation of [Kol07, Theorem 35 (5)]. -/
theorem affineSpaceTriple_closedEmbedding_coordInclSnd {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin m) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) (hI' : IsNonzeroEverywhere (I.map (coordInclSnd n m))) :
    (affineSpaceTriple k (n + m) (I.map (coordInclSnd n m)) hI').ClosedEmbedding
      (affineSpaceTriple k m I hI) (coordInclSnd n m) :=
  ⟨coordInclSnd_comp_affineSpaceToSpec n m, rfl, (empty_comap (coordInclSnd n m)).symm⟩

end Hironaka.Resolution
