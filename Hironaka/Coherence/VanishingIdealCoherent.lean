import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Analytic.CoherentIdealWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The vanishing ideal of a closed submanifold is coherent

Source: Copy-4, Step 5 of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), where `ψ_{𝓘_V}` and `ψ_{𝓘_W}` appear
in `eq:IV-H` and in "`ψ_{𝓘_W}` is bounded on `Λ`".

Both of those need a *weight* for a vanishing ideal, and
`Pending/CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent`
produces one from coherence alone.  This module supplies the missing coherence.

Nothing new is needed analytically: `Pending/BlowupFlatCoordinates` already proves
Hadamard's lemma in flattening coordinates
(`exists_eq_sum_flatCoord`: every germ of `𝓘_C` on `flatDomain Φ` is
`∑_{i ≥ k} bᵢ · flatCoord Φ i`) and that the coordinates with `i ≥ k` lie in `𝓘_C`.
Coherence is the conjunction of those two, with the family

  `gᵢ = flatCoord Φ i` for `i ≥ k`,  `gᵢ = 0` for `i < k`,

together with the trivial chart off `C`, where `𝓘_C` is the unit ideal.  The one
step not already on disk is that `𝓘_C` absorbs holomorphic combinations of its
own members — `GermIdeal` is a bare `mem` predicate and carries no closure axiom,
so this has to be checked for `vanishingIdeal` by hand.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.VanishingIdealCoherent

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  Hironaka.BlowupSequences BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `𝓘_A` absorbs holomorphic combinations of its own members. -/
theorem mem_vanishingIdeal_of_isInSpanAt {A : Set M} {N : ℕ} {g : Fin N → M → ℂ} {y : M}
    (hg : ∀ i, (vanishingIdeal (n := n) A).mem y (g i)) {f : M → ℂ}
    (hf : IsInSpanAt (n := n) (· ∈ range g) y f) :
    (vanishingIdeal (n := n) A).mem y f := by
  obtain ⟨hfhol, K, s, a, hs, -, hsum⟩ := hf
  refine ⟨hfhol, ?_⟩
  have hzero : ∀ᶠ y' in 𝓝 y, ∀ i, y' ∈ A → g i y' = 0 :=
    eventually_all.mpr fun i => (hg i).2
  filter_upwards [hsum, hzero] with y' h1 h2 hy'A
  rw [h1]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i, hi⟩ := hs j
  rw [← hi, h2 i hy'A, mul_zero]

/-- **The vanishing ideal of a closed complex submanifold is coherent.** -/
theorem isCoherent_vanishingIdeal {C : Set M} (hC : IsClosedSubmanifold n C) :
    (vanishingIdeal (n := n) C).IsCoherent := by
  classical
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨k, -, -, Φ, hΦsrc, -, hflat⟩ := hC.2 x hx
    refine ⟨flatDomain Φ, isOpen_flatDomain Φ, mem_flatDomain_self Φ, n,
      fun i => if k ≤ i.1 then flatCoord Φ i else 0, fun i => ?_, fun y hy f => ?_⟩
    · by_cases hik : k ≤ i.1
      · simp only [hik, if_true]
        exact fun z hz => (holomorphicAt_flatCoord Φ i hz).mdifferentiableAt.mdifferentiableWithinAt
      · simp only [hik, if_false]
        exact mdifferentiableOn_const
    · constructor
      · intro hf
        obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy hf
        refine ⟨hf.1, n, fun i => if k ≤ i.1 then flatCoord Φ i else 0, b,
          fun i => ⟨i, rfl⟩, hbhol, ?_⟩
        filter_upwards [hbeq] with y' h1
        rw [h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hik : k ≤ i.1
        · simp [hik]
        · rw [hb0 i (Nat.lt_of_not_le hik)]
          simp
      · refine mem_vanishingIdeal_of_isInSpanAt fun i => ?_
        by_cases hik : k ≤ i.1
        · simpa only [hik, if_true] using flatCoord_mem_vanishingIdeal Φ hflat hik hy
        · simp only [hik, if_false]
          exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩
  · refine ⟨Cᶜ, hC.1.isOpen_compl, hx, 1, fun _ => fun _ => (1 : ℂ),
      fun i => mdifferentiableOn_const, fun y hy f => ?_⟩
    constructor
    · intro hf
      exact isInSpanAt_of_eq_mul ⟨0, rfl⟩ hf.1 hf.1 (Eventually.of_forall fun _ => by simp)
    · intro hf
      refine ⟨hf.1, ?_⟩
      filter_upwards [hC.1.isOpen_compl.mem_nhds hy] with y' h1 h2
      exact absurd h2 h1

/-- **The weight `ψ_{𝓘_C}` of a closed submanifold** (Copy-4, `sec:qpsh`). -/
theorem exists_hasAnalyticSingularitiesOfType_vanishingIdeal [CompactSpace M]
    {C : Set M} (hC : IsClosedSubmanifold n C) :
    ∃ φ : M → EReal,
      HasAnalyticSingularitiesOfType φ 1 (vanishingIdeal (n := n) C) :=
  CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent
    (isCoherent_vanishingIdeal hC)

end

end Hironaka.VanishingIdealCoherent
