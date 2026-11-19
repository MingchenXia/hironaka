import Hironaka.Resolution.HironakaG34ToricCharts

/-!
# Transporting partial character sections through monomial coordinates

The inverse character change is explicit. It transports an existing section
realizing the coordinates outside a carrier mask through one monomial chart,
provided its pivot is outside that mask, and through a coordinate permutation.
This constructs the new section; no future-chart or protection package is
assumed. The actual geometric pivot and the starting Gamma action still have
to be produced in the native history.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG4ToricCharacterSections

open HironakaG34ToricCharts

noncomputable section

variable {n : ℕ}

/-- Inverse to the monomial change of characters near the identity. -/
def inverseChartVec (b : Fin n → ℂ) (k : ℕ) (j : Fin n) : Fin n → ℂ :=
  fun i => if k ≤ i.val ∧ i ≠ j then b i * b j else b i

theorem inverseChartVec_one (k : ℕ) (j : Fin n) :
    inverseChartVec (1 : Fin n → ℂ) k j = 1 := by
  funext i
  simp only [inverseChartVec, Pi.one_apply, mul_one, ite_self]

theorem continuous_inverseChartVec (k : ℕ) (j : Fin n) :
    Continuous (fun b : Fin n → ℂ => inverseChartVec b k j) := by
  refine continuous_pi fun i => ?_
  by_cases h : k ≤ i.val ∧ i ≠ j
  · simpa only [inverseChartVec, if_pos h, Pi.mul_def] using
      (continuous_apply i).mul (continuous_apply j)
  · simpa only [inverseChartVec, if_neg h] using (continuous_apply i : Continuous fun b : Fin n → ℂ => b i)

theorem chartVec_inverseChartVec (k : ℕ) (j : Fin n) (b : Fin n → ℂ)
    (hb : b j ≠ 0) : chartVec (inverseChartVec b k j) k j = b := by
  funext i
  by_cases h : k ≤ i.val ∧ i ≠ j
  · simp [chartVec, inverseChartVec, h, hb]
  · simp [chartVec, inverseChartVec, h]

/-- An actual section realizing the free coordinates gives an explicit
section for the transformed characters. Only the free pivot must be realized. -/
theorem partial_realization_after_chartVec
    {A : Type*} {F : Filter A} {μ : A → Fin n → ℂ}
    (S : Finset (Fin n)) (k : ℕ) (j : Fin n) (hj : j ∉ S)
    (s : (Fin n → ℂ) → A) (hs : Tendsto s (𝓝 1) F)
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (s b) i = b i) :
    Tendsto (fun b => s (inverseChartVec b k j)) (𝓝 1) F ∧
      ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S,
        chartVec (μ (s (inverseChartVec b k j))) k j i = b i := by
  have hInv : Tendsto (fun b : Fin n → ℂ => inverseChartVec b k j) (𝓝 1) (𝓝 1) := by
    simpa only [inverseChartVec_one] using (continuous_inverseChartVec k j).tendsto 1
  refine ⟨hs.comp hInv, ?_⟩
  have hne : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), b j ≠ 0 :=
    (isOpen_ne_fun (continuous_apply j) continuous_const).mem_nhds (by simp)
  filter_upwards [hInv.eventually hrealize, hne] with b hb hbj i hi
  have hbi := hb i hi
  have hbj' := hb j hj
  by_cases h : k ≤ i.val ∧ i ≠ j
  · simp only [chartVec, if_pos h]
    rw [hbi, hbj']
    simp [inverseChartVec, h, hbj]
  · simp only [chartVec, if_neg h]
    rw [hbi]
    simp only [inverseChartVec, if_neg h]

/-- The same primitive section survives the actual coordinate permutation:
reindex the requested characters by the forward permutation. -/
theorem partial_realization_after_permutation
    {A : Type*} {F : Filter A} {μ : A → Fin n → ℂ}
    (S : Finset (Fin n)) (σ : Fin n ≃ Fin n)
    (s : (Fin n → ℂ) → A) (hs : Tendsto s (𝓝 1) F)
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (s b) i = b i) :
    Tendsto (fun b : Fin n → ℂ => s (fun i => b (σ i))) (𝓝 (1 : Fin n → ℂ)) F ∧
      ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S.image σ,
        μ (s (fun j => b (σ j))) (σ.symm i) = b i := by
  have hperm : Tendsto (fun b : Fin n → ℂ => fun i => b (σ i)) (𝓝 1) (𝓝 1) :=
    (continuous_pi fun i => continuous_apply (σ i)).tendsto 1
  refine ⟨hs.comp hperm, ?_⟩
  filter_upwards [hperm.eventually hrealize] with b hb i hi
  have hpre : σ.symm i ∉ S := by
    intro hmem
    exact hi (Finset.mem_image.mpr ⟨σ.symm i, hmem, σ.apply_symm_apply i⟩)
  simpa only [σ.apply_symm_apply] using hb (σ.symm i) hpre

end

end Hironaka.HironakaG4ToricCharacterSections
