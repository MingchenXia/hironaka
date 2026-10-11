/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualPrimeHypersurfacePureNeighbourhood


set_option autoImplicit false

/-!
# Simultaneously regular and finitely avoiding original prime zeros

Complete natural statement and ENTIRE proof precede the import baseline.
Density is produced from the original equation, not an input certificate.
-/

open Hironaka

noncomputable section
open Set Filter
open scoped Topology

namespace Hironaka.ActualPrimeRegularFiniteAvoidance



/-- Original finite nondivisible tests are simultaneously avoided at actual
regular zeros of the original prime equation in every origin neighbourhood. -/
theorem frequently_regular_zero_avoiding_finite_family {m : ℕ} {ι : Type*} [Fintype ι]
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x)
    (hQ : Prime (HolGerm.mk q hq))
    (a : ι → ComplexModel (m + 1) → ℂ)
    (ha : ∀ i, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (a i) x)
    (hnot : ∀ i, ¬HolGerm.mk q hq ∣ HolGerm.mk (a i) (ha i)) :
    ∃ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), q x = 0 ∧
      RegularAtDim (n := m + 1) {y | q y = 0} x m ∧ ∀ i, a i x ≠ 0 := by
  obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ :=
    ActualPrimeHypersurfacePureNeighbourhood.exists_pure_hypersurface_neighbourhood q hq hQ
  have hf := ActualPrimeGermGenericAvoidance.frequently_zero_avoiding_finite_family q hq hQ a ha hnot
  have hA : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), ∀ i, DifferentiableAt ℂ (a i) x :=
    Filter.eventually_all.mpr ha
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨W, hWsub, hWo, hW0⟩ := mem_nhds_iff.mp (inter_mem hS (hΩo.mem_nhds hΩ0))
  have hWΩ : W ⊆ Ω := fun y hy => (hWsub hy).2
  obtain ⟨y, hyW, ⟨hqy, hay⟩, hAy⟩ :=
    Filter.frequently_iff.mp (hf.and_eventually hA) (hWo.mem_nhds hW0)
  have hne : ∀ᶠ z in 𝓝 y, ∀ i, a i z ≠ 0 :=
    Filter.eventually_all.mpr (fun i => (hAy i).continuousAt.eventually_ne (hay i))
  obtain ⟨O, hOsub, hOo, hyO⟩ := mem_nhds_iff.mp (inter_mem (hWo.mem_nhds hyW) hne)
  have hycl : y ∈ closure (regularLocus (n := m + 1) ({z | q z = 0} ∩ W) m) :=
    (hΩ W hWo hWΩ).2 ⟨hqy, hyW⟩
  obtain ⟨x, hxO, hxreg⟩ := mem_closure_iff.mp hycl O hOo hyO
  have hxW : x ∈ W := (hOsub hxO).1
  have heq : ({z | q z = 0} ∩ W) ∩ W = {z | q z = 0} ∩ W := by
    ext z
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz.2⟩⟩
  have hxregB : RegularAtDim (n := m + 1) {z | q z = 0} x m :=
    RegularPointDimension.regularAtDim_of_inter_eq hWo hxW heq hxreg
  exact ⟨x, (hWsub hxW).1, hxregB.2.1, hxregB, (hOsub hxO).2⟩

end Hironaka.ActualPrimeRegularFiniteAvoidance
