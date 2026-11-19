import Hironaka.Manifold.ChartDifferentiable
import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.KahlerCurrentRegularization
import Hironaka.Analytic.AnalyticNoetherProperty
import Hironaka.Analytic.KahlerCurrentMax

set_option autoImplicit false

/-!
# A Kähler current whose polar set is the non-Kähler locus

Source: Boucksom, *Divisorial Zariski decompositions*, Theorem 3.17; Copy-4,
`sec:nK`; blueprint `ana:locus-properties`.

Among the polar sets of Kähler currents in a big class `α` with analytic
singularities (a nonempty family, by regularizing any Kähler current) pick a
minimal one, `P(S)` (Noether property).  It contains `E_nK(α)`, since a positive
Lelong number forces a pole.  Conversely, for any Kähler current `T`, the
maximum `R` of `S` and `T` has Lelong numbers below both; its regularization `S'`
has `P(S') ⊆ {ν(R) > 0} ⊆ {ν(S) > 0} ⊆ P(S)`, so `P(S') = P(S)` by minimality,
and every point of `P(S)` has `ν(T) ≥ ν(R) > 0`.  Hence `P(S) = E_nK(α)`, and
`E_nK(α)` is an analytic subset.

This module holds the proof so that modules below `Hironaka.LocusProperties` in the
import order can use analyticity of non-Kähler loci; the statements there are
thin wrappers.  Inputs: `KahlerCurrentRegularization` (an explicit classical
interface) and `AnalyticNoetherProperty`, `KahlerCurrentMax` (proved).  The
regularized current supplied here has bounded-remainder analytic singularities
and is smooth off its pole set, so the elementary pole-set analyticity theorem
applies directly.
-/

open Set

namespace Hironaka.NonKahlerLocusPoleSet

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold Hironaka.GlobalAnalyticSingularities

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- **Boucksom, Theorem 3.17.**  A big class contains a Kähler current with
bounded-remainder analytic singularities, smooth off its polar set, whose polar
set is exactly `E_nK(α)`. -/
theorem exists_kahlerCurrent_poleSet_eq_nonKahlerLocus (hn : 0 < n)
    (alpha : RealBottChern n X) (hbig : IsBigClass alpha) :
    ∃ T : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) T.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) T.potential ∧
        poleSet T.potential = nonKahlerLocus alpha := by
  classical
  set 𝒜 : Set (Set X) := {A | ∃ S : KahlerCurrent alpha,
    HasAnalyticSingularities (n := n) S.potential ∧
      HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
      poleSet S.potential = A} with h𝒜def
  have h𝒜 : ∀ A ∈ 𝒜, IsComplexAnalyticSubset (n := n) A := by
    rintro A ⟨S, hS, -, rfl⟩
    exact isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities hS
  obtain ⟨T₀⟩ := hbig
  obtain ⟨S₀, hS₀a, hS₀s, -⟩ :=
    KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos T₀
  obtain ⟨A, ⟨S, hSa, hSs, rfl⟩, hmin⟩ :=
    AnalyticNoetherProperty.exists_minimal_of_isComplexAnalyticSubset 𝒜 h𝒜
      ⟨_, S₀, hS₀a, hS₀s, rfl⟩
  refine ⟨S, hSa, hSs, subset_antisymm ?_ ?_⟩
  · intro x hx T
    obtain ⟨R, hR⟩ := KahlerCurrentMax.exists_kahlerCurrent_lelongNumber_le_both S T
    obtain ⟨S', hS'a, hS's, hsub⟩ :=
      KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos R
    have hS'S : poleSet S'.potential ⊆ poleSet S.potential := fun y hy =>
      eq_bot_of_lelongNumber_pos hn S.strictlyPsh.1 ((hsub hy).trans_le (hR y).1)
    have heq := hmin _ ⟨S', hS'a, hS's, rfl⟩ hS'S
    rw [← heq] at hx
    exact (hsub hx).trans_le (hR x).2
  · intro x hx
    exact eq_bot_of_lelongNumber_pos hn S.strictlyPsh.1 (hx S)

/-- The non-Kähler locus of a big class is an analytic subset.  The preceding
Boucksom theorem supplies a Kähler current with analytic singularities whose
polar set is the locus, and `AnalyticPoleSet` makes that polar set analytic. -/
theorem isComplexAnalyticSubset_nonKahlerLocus (hn : 0 < n)
    (alpha : RealBottChern n X) (hbig : IsBigClass alpha) :
    IsComplexAnalyticSubset (n := n) (nonKahlerLocus alpha) := by
  obtain ⟨T, hsing, -, hpole⟩ :=
    exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn alpha hbig
  rw [← hpole]
  exact isComplexAnalyticSubset_poleSet_of_hasAnalyticSingularities hsing

end

end Hironaka.NonKahlerLocusPoleSet
