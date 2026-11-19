import Hironaka.Coherence.CartanComponentIdeal
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false

/-!
# Cartan's coherence theorem (formerly a named input; PROVED)

Source: H. Cartan, *Idéaux et modules de fonctions analytiques de variables complexes*,
Bull. SMF 78 (1950); Grauert--Remmert, *Coherent analytic sheaves*, Ch. 4 §2; Demailly,
*Complex analytic and differential geometry*, II.5; Gunning--Rossi, IV.C.  Used by Copy-4,
`sec:fixed-data` (`references/transcendental-nakamaye-copy4-20260911/source/
main-Nulllocus.tex:1503-1515`): "`𝔧 := 𝓘_{Z'}`, a coherent ideal sheaf".

Human decision I-0739 item 5 (answering I-0735 (A)): `ct22Copy4_exists_stepOneData` is proved from
two named inputs in their own modules; this is input (i), stated for EVERY analytic subset (the
clean classical statement; the consumer needs it for `Z' = closure (E_nK(α) \ V)` only).  Item 6
of the same decision makes discharging it a TN-CLASSICAL programme: Oka's coherence theorem
(`OkaPolynomialRelations`, run 0119, in progress), then Cartan's argument via the local
parametrization already in the tree.

`IsComplexAnalyticSubset` asks for a finite holomorphic presentation at EVERY point of the
manifold, so the sets are closed; at a point off `A` the ideal is the unit ideal.  Dimension `0`
is included (points are open, `𝓘_A` is `0` at points of `A`).  No compactness, Kähler or
Hausdorff hypothesis: coherence is local.

**Status (TN-CLASSICAL run 0122):** proved, statement unchanged.  The proof is
`CartanIrreducible.cartanCoherence`: Oka's theorem (`OkaCoherence.okaProperty_euclidean`), the
reductions to irreducible germs at the origin (`CartanLocalReduction`, `CartanIrreducibleReduction`)
and Demailly II.4.29 for an irreducible germ with finitely many primitive elements on the moment
curve (`CartanPrescribedPrimitive`, `CartanLocalAlgebra`, `CartanKeyLemma`, `CartanLocalInclusion`,
`CartanIrreducible`).
-/

universe u

namespace Hironaka.CartanCoherenceInterface

open Hironaka.HolomorphicIdealSheaves CartanComponentIdeal

/-- **Cartan's coherence theorem** (H. Cartan 1950): on a complex manifold the ideal sheaf `𝓘_A`
of every analytic subset `A` is coherent, i.e. near every point it is generated, at every point of
a neighbourhood, by finitely many holomorphic functions.  Proved in
`CartanIrreducible.cartanCoherence`. -/
theorem cartanCoherence {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] : CartanCoherence n X :=
  CartanIrreducible.cartanCoherence

end Hironaka.CartanCoherenceInterface
