/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama

/-!
# The branch of a node through a point of a smooth curve

The local algebra of the pole computation at the points over the nodes
(blueprint `sm-omega-base-change-fibre.tex`, `lem:sm-omega-bcf-pole-chart`, the step "`ū v̄ = 0` in
the domain `L`, say `v̄ = 0`; then `dū` is a basis and `ū` a uniformizer"). Let `L` be a discrete
valuation ring which is a `K`-algebra with `Ω_{L/K}` finitely generated and nonzero (for instance
the local ring at a closed point of a smooth curve over `K`, or of an étale neighbourhood of one),
and let `ū, v̄ ∈ 𝔪_L` with `ū v̄ = 0` such that `Ω_{L/K}` is spanned by `dū` and `dv̄` (the images
of the coordinates of an étale node chart, when the map from the node is unramified). Then one of
`ū, v̄` vanishes and the other is a uniformizer whose differential spans `Ω_{L/K}`
(`branch_of_node`).

The key step is `not_mem_sq_of_span_D`: an element of `𝔪` whose differential spans `Ω_{L/K}` is not
in `𝔪²`, since `d(𝔪²) ⊆ 𝔪 Ω` and Nakayama's lemma.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2 (b)
(`semi-stable.tex`, T:1702–1704: the two branches of a node and the residues of `du/u = −dv/v`).
-/

open IsLocalRing

namespace DeJongAlterations.StableModification.Omega.RosenlichtComponent

variable {K L : Type*} [Field K] [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
  [Algebra K L]

/-- `d(𝔪²) ⊆ 𝔪 Ω`. -/
theorem D_mem_smul_of_mem_sq {a : L} (ha : a ∈ maximalIdeal L ^ 2) :
    KaehlerDifferential.D K L a ∈ (maximalIdeal L) • (⊤ : Submodule L Ω[L⁄K]) := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hx trivial)
      (Submodule.smul_mem_smul hy trivial)
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **An element whose differential spans `Ω` is not in `𝔪²`** (Nakayama). -/
theorem not_mem_sq_of_span_D [Module.Finite L Ω[L⁄K]] [Nontrivial Ω[L⁄K]] {a : L}
    (ha : Submodule.span L {KaehlerDifferential.D K L a} = ⊤) : a ∉ maximalIdeal L ^ 2 := by
  intro h2
  have h1 := D_mem_smul_of_mem_sq (K := K) h2
  have hle : (⊤ : Submodule L Ω[L⁄K]) ≤ (maximalIdeal L) • (⊤ : Submodule L Ω[L⁄K]) :=
    ha.symm.le.trans (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h1))
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal L) ⊤
    (Module.Finite.fg_top) hle (maximalIdeal_le_jacobson _)
  exact top_ne_bot hbot

/-- In a discrete valuation ring an element of `𝔪 ∖ 𝔪²` is a uniformizer. -/
theorem irreducible_of_mem_of_not_mem_sq {a : L} (ha : a ∈ maximalIdeal L)
    (ha2 : a ∉ maximalIdeal L ^ 2) : Irreducible a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha2 (Submodule.zero_mem _)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hϖm : ϖ ∈ maximalIdeal L := hϖ.not_isUnit
  rcases n with _ | _ | n
  · rw [pow_zero, mul_one] at ha
    exact absurd u.isUnit ((mem_maximalIdeal _).mp ha)
  · rw [zero_add, pow_one]
    exact (irreducible_isUnit_mul u.isUnit).mpr hϖ
  · exfalso
    apply ha2
    have : (u : L) * ϖ ^ (n + 1 + 1) = ((u : L) * ϖ ^ n * ϖ) * ϖ := by ring
    rw [this, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖm) hϖm

/-- **The branch of a node through a point of a smooth curve** (blueprint
`lem:sm-omega-bcf-pole-chart`, local step): if `ū, v̄ ∈ 𝔪_L`, `ū v̄ = 0` and `Ω_{L/K}` (finite and
nonzero) is spanned by `dū, dv̄`, then either `v̄ = 0`, `ū` is a uniformizer and `dū` spans
`Ω_{L/K}`, or symmetrically. -/
theorem branch_of_node [Module.Finite L Ω[L⁄K]] [Nontrivial Ω[L⁄K]] {u v : L}
    (hu : u ∈ maximalIdeal L) (hv : v ∈ maximalIdeal L) (huv : u * v = 0)
    (hΩ : Submodule.span L {KaehlerDifferential.D K L u, KaehlerDifferential.D K L v} = ⊤) :
    (v = 0 ∧ Irreducible u ∧ Submodule.span L {KaehlerDifferential.D K L u} = ⊤) ∨
      (u = 0 ∧ Irreducible v ∧ Submodule.span L {KaehlerDifferential.D K L v} = ⊤) := by
  rcases mul_eq_zero.mp huv with h0 | h0
  · subst h0
    have hspan : Submodule.span L {KaehlerDifferential.D K L v} = ⊤ := by
      rw [← hΩ, map_zero, Submodule.span_insert_zero]
    exact Or.inr ⟨rfl, irreducible_of_mem_of_not_mem_sq hv (not_mem_sq_of_span_D hspan), hspan⟩
  · subst h0
    have hspan : Submodule.span L {KaehlerDifferential.D K L u} = ⊤ := by
      rw [← hΩ, map_zero, Set.pair_comm, Submodule.span_insert_zero]
    exact Or.inl ⟨rfl, irreducible_of_mem_of_not_mem_sq hu (not_mem_sq_of_span_D hspan), hspan⟩

end DeJongAlterations.StableModification.Omega.RosenlichtComponent
