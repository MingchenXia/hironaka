/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sums of finitely many marked ideals and the coefficient ideal

Source: Włodarczyk 2005, §2.9 (the sum `(𝓘₁, μ₁) + … + (𝓘ₘ, μₘ) = (∑ᵢ 𝓘ᵢ^{∏_{j≠i} μⱼ}, ∏ⱼ μⱼ)`, Lemma
`le:operations` (1)) and §2.11 (the coefficient ideal `𝓒(𝓘, μ) = (𝓘, μ) + (𝓓𝓘, μ - 1) + … + (𝓓^{μ-1}𝓘, 1)` and Lemma
`le:coeff` `𝓒(𝓘, μ) ≃ (𝓘, μ)`), for `N = M` and transform with centre-relative strict transforms
(`geoTransformAlong`, `IsGeoTestTower`).

* `finSumIdeal_one`, `finSumIdeal_congr`, `isCoherent_finSumIdeal_of_lt`, `mem_cosupport_finSumIdeal` (`cosupp(∑ᵢ
  𝔍ᵢ, μ) = ⋂ᵢ cosupp(𝔍ᵢ, μ)`).
* `msum 𝔪 m`: Włodarczyk's sum of `𝔪 0, …, 𝔪 (m - 1)`.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.CoefficientIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupControlledTransform BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueing DerivativeIdealTower RestrictedIdealExtension

noncomputable section

/-! ### Finite sums of ideals -/

section FinSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `finSumIdeal J 1 = J 0` for a coherent `J 0`. -/
theorem finSumIdeal_one {J : ℕ → GermIdeal n M} (hJ : (J 0).IsCoherent) : finSumIdeal J 1 = J 0 := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine HomogenizedIdeal.mem_of_isInSpanAt hJ (IsInSpanAt.mono ?_
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < 1 ∧ (J i).mem y s) y g from hg))
    rintro s ⟨i, hi, hs⟩
    obtain rfl : i = 0 := by omega
    exact hs
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < 1 ∧ (J i).mem y s) y g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨0, Nat.one_pos, hg⟩ (holomorphicAt_of_mem hJ hg)

/-- Only the members `J i`, `i < m`, matter. -/
theorem finSumIdeal_congr {J J' : ℕ → GermIdeal n M} {m : ℕ} (h : ∀ i < m, J i = J' i) :
    finSumIdeal J m = finSumIdeal J' m := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem y s) y g
    exact IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => ⟨i, hi, h i hi ▸ hs⟩)
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g from hg)
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g
    exact IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => ⟨i, hi, (h i hi).symm ▸ hs⟩)
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem y s) y g from hg)

/-- **A finite sum of coherent ideals is coherent** (only the members `i < m` are assumed coherent). -/
theorem isCoherent_finSumIdeal_of_lt {J : ℕ → GermIdeal n M} :
    ∀ {m : ℕ}, (∀ i < m, (J i).IsCoherent) → (finSumIdeal J m).IsCoherent
  | 0, _ => by
    rw [finSumIdeal_congr (J' := fun _ => unitIdeal n M) (fun i hi => absurd hi (Nat.not_lt_zero i))]
    exact isCoherent_finSumIdeal (fun _ => isCoherent_unitIdeal) 0
  | m + 1, hJ => by
    rw [finSumIdeal_succ fun i hi => hJ i (Nat.lt_succ_of_le hi)]
    exact isCoherent_sumIdeal (isCoherent_finSumIdeal_of_lt fun i hi => hJ i (Nat.lt_succ_of_lt hi))
      (hJ m (Nat.lt_succ_self m))

/-- **The cosupport of a finite sum** (equal marks): `cosupp(∑_{i<m} 𝔍ᵢ, μ) = ⋂_{i<m} cosupp(𝔍ᵢ, μ)`. -/
theorem mem_cosupport_finSumIdeal {N : Set M} {J : ℕ → GermIdeal n M} {m μ : ℕ}
    (hJ : ∀ i < m, ∀ x g, (J i).mem x g → HolomorphicAt n g x) {x : M} :
    x ∈ cosupport n N (finSumIdeal J m) μ ↔ x ∈ N ∧ ∀ i < m, x ∈ cosupport n N (J i) μ := by
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun i hi => ⟨hxN, fun g hg => hx g ?_⟩⟩
    exact (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ i, i < m ∧ (J i).mem x s)
      ⟨i, hi, hg⟩ (hJ i hi x g hg) : IsInSpanAt (n := n) _ x g)
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun g hg => IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g from hg) ?_⟩
    rintro s ⟨i, hi, hs⟩
    exact (hx i hi).2 s hs

end FinSum

/-! ### Włodarczyk's sum of finitely many marked ideals -/

section MSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The exponent of the `i`-th summand: `∏_{j < m, j ≠ i} dⱼ`. -/
def sumExp (d : ℕ → ℕ) (m i : ℕ) : ℕ := ((Finset.range m).erase i).prod d

theorem mul_sumExp (d : ℕ → ℕ) {m i : ℕ} (hi : i < m) :
    d i * sumExp d m i = (Finset.range m).prod d := by
  rw [sumExp, Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)]

theorem one_le_sumExp {d : ℕ → ℕ} {m : ℕ} (hd : ∀ j < m, 1 ≤ d j) (i : ℕ) : 1 ≤ sumExp d m i := by
  have h : 0 < ((Finset.range m).erase i).prod d := Finset.prod_pos fun j hj => by
    have := hd j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
    omega
  unfold sumExp
  omega

/-- **Włodarczyk's sum of marked ideals** (§2.9):
`(𝓘₀, μ₀) + … + (𝓘_{m-1}, μ_{m-1}) = (∑ᵢ 𝓘ᵢ^{∏_{j≠i} μⱼ}, ∏ⱼ μⱼ)`, on the `N` and `E` of `𝔪 0`. -/
def msum (𝔪 : ℕ → MarkedIdeal n M) (m : ℕ) : MarkedIdeal n M where
  N := (𝔪 0).N
  E := (𝔪 0).E
  ideal := finSumIdeal (fun i => idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)) m
  d := (Finset.range m).prod fun j => (𝔪 j).d

end MSum

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

end Tower

end

end Hironaka.CoefficientIdeal
