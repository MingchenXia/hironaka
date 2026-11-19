import Hironaka.Analytic.AnalyticDescendingChain

set_option autoImplicit false

/-!
# The Noether property of analytic subsets of a compact complex manifold

Source: Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5, §6 and Ch. 9, §1
(every decreasing sequence of analytic sets is stationary on compact subsets);
Boucksom, *Divisorial Zariski decompositions*, proof of Theorem 3.17 ("by the
strong Noetherian property of analytic sets"); blueprint `ana:locus-properties`.

On a compact complex manifold the closed analytic subsets satisfy the descending
chain condition; equivalently every nonempty family of analytic subsets has a
minimal member.

PROVED in `Hironaka.AnalyticDescendingChain`: germs of a descending chain stabilize at
each point (Noetherianity of the ring of holomorphic germs), the stabilization spreads to a
fixed neighbourhood by the identity theorem along the connected regular parts of the local
decomposition, and compactness makes the chain stationary.
`Hironaka.LocusProperties.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus` uses it.
-/

open Set

namespace Hironaka.AnalyticNoetherProperty



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Noether property of analytic sets.**  A nonempty family of analytic subsets of a
compact complex manifold has a minimal member. -/
theorem exists_minimal_of_isComplexAnalyticSubset [CompactSpace M]
    (𝒜 : Set (Set M)) (h𝒜 : ∀ A ∈ 𝒜, IsComplexAnalyticSubset (n := n) A)
    (hne : 𝒜.Nonempty) :
    ∃ A ∈ 𝒜, ∀ B ∈ 𝒜, B ⊆ A → B = A :=
  AnalyticDescendingChain.exists_minimal_of_isComplexAnalyticSubset 𝒜 h𝒜 hne

end

end Hironaka.AnalyticNoetherProperty
