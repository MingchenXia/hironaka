/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false

/-!
# The singular locus of `V` and its local generators (TN.4 #4, Stokes against `[V]`)

Blueprint `ana:stokes-singular-locus-analytic` (Demailly, CADG II.4.31): for an irreducible
analytic subvariety `V` of dimension `k`, `V_sing` is cut out near every point by Cartan
generators `g` of `𝓘_V` and the `(n - k)`-minors of their Jacobian.  This file starts that
programme with the first ingredient, `exists_cartanGenerators`: Cartan's coherence theorem
(`CartanIrreducible.cartanCoherence`, `demailly-cadg:II.4.29`) gives, near every point, finitely
many holomorphic functions generating `𝓘_A` at every point of an open set `U`, and on `U` a
CLOSED analytic set `A` is exactly their common zero set (a generator lies in `𝓘_A`, so it
vanishes on `A`; off the closed `A` the constant `1` lies in `𝓘_A`, so some generator does not
vanish).

The two directions of the Jacobian criterion and the resulting presentation of `V_sing` are in
`Hironaka.StokesSingularLocusAnalytic` (`isComplexAnalyticSubset_singularLocus`).
-/


open Set Filter
open scoped Topology Manifold

namespace Hironaka.StokesSingularLocus

open Hironaka.HolomorphicIdealSheaves

open Hironaka
noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cartan generators of a closed analytic set.**  Near every point, finitely many holomorphic
functions generate the ideal `𝓘_A` at every point of an open neighbourhood `U`
(`demailly-cadg:II.4.29`), and on `U` the set `A` is exactly their common zero set. -/
theorem exists_cartanGenerators {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAc : IsClosed A) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (s : Fin N → M → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U) ∧
      (∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) A).mem y g ↔
        IsInSpanAt (n := n) (· ∈ range s) y g) ∧
      ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0) := by
  obtain ⟨U, hU, hxU, N, s, hs, hspan⟩ := CartanIrreducible.cartanCoherence A hA x
  refine ⟨U, hU, hxU, N, s, hs, hspan, fun y hy => ⟨fun hyA i => ?_, fun hzero => ?_⟩⟩
  · -- each generator lies in `𝓘_A` at `y`, hence vanishes at the point `y ∈ A`
    have hhol : HolomorphicAt n (s i) y :=
      Filter.mem_of_superset (hU.mem_nhds hy) fun z hz =>
        (hs i z hz).mdifferentiableAt (hU.mem_nhds hz)
    have hmem : (vanishingIdeal (n := n) A).mem y (s i) := by
      rw [hspan y hy]
      refine ⟨hhol, 1, fun _ => s i, fun _ _ => 1, fun _ => ⟨i, rfl⟩,
        fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const, ?_⟩
      exact Eventually.of_forall fun z => by simp
    exact hmem.2.self_of_nhds hyA
  · -- off the closed set `A`, the constant `1` lies in `𝓘_A`
    by_contra hyA
    have hev : ∀ᶠ z in 𝓝 y, z ∉ A := hAc.isOpen_compl.mem_nhds hyA
    have hmem : (vanishingIdeal (n := n) A).mem y (fun _ => (1 : ℂ)) :=
      ⟨Eventually.of_forall fun _ => mdifferentiableAt_const,
        hev.mono fun z hz hzA => absurd hzA hz⟩
    rw [hspan y hy] at hmem
    obtain ⟨-, K, t, a, ht, -, hrep⟩ := hmem
    have h1 := hrep.self_of_nhds
    have : ∀ j, t j y = 0 := fun j => by
      obtain ⟨i, hi⟩ := ht j
      rw [← hi]; exact hzero i
    simp [this] at h1

end

end Hironaka.StokesSingularLocus
