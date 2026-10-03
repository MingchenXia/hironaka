/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.OrderMultiplicativity
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient ideal along a submanifold, restricted to a subset (one stage)

Sources: Włodarczyk 2005, Lemma `le:S` (first statement), GGT 2008 Proposition 5.6.4 (1), on the submanifold `N` of
`(M, N, E, 𝔞, d)` with the coefficient ideal `𝓒_N` of `HomogenizedIdealAlong`.

* `cosupport_inter_subset_of_subset`: `cosupp(𝔟|_N, d) ∩ S ⊆ cosupp(𝔟|_S, d)` for `S ⊆ N` (orders do not drop under restriction).
* `cosupport_coeffMarkedAlong_subset`: `cosupp(𝓒_N(𝔪)|_A, μ_𝓒) ⊆ cosupp 𝔪` for every `A ⊆ N` (the last summand of `𝓒_N` contains
  `g^{μ_𝓒}` for `g ∈ 𝓓_N^{d-1} 𝔞`, and `cosupp(𝔞|_N, d) = N ∩ V(𝓓_N^{d-1} 𝔞)`).
* **`cosupp_coeffMarkedAlong_withN`: `cosupp(𝓒_N(𝔪)|_S) = cosupp 𝔪 ∩ S`** for every `S ⊆ N` (`le:S`, first statement, along `N`).

Not here: the statements along multiple test blow-ups with centres in the strict transforms of `S` (they need the transforms along
`N`, item (2) of `hir:along-calculus`).
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.CoefficientIdealAlongRestriction

open Hironaka.HolomorphicIdealSheaves
open Hironaka.GermIdealOrder Hironaka.DerivativeIdealAlong Hironaka.GiraudAlong Hironaka.TangentDirectionAlong Hironaka.IdealWeightPowers Hironaka.MarkedIdeals Hironaka.CoefficientIdeal Hironaka.CoefficientIdealRestriction Hironaka.HomogenizedIdealAlong

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Orders along `N` do not drop under restriction to `S ⊆ N`**: `cosupp(𝔟|_N, d) ∩ S ⊆ cosupp(𝔟|_S, d)`. -/
theorem cosupport_inter_subset_of_subset {N S : Set M} (hS : S ⊆ N) (𝔟 : GermIdeal n M) (d : ℕ) :
    cosupport n N 𝔟 d ∩ S ⊆ cosupport n S 𝔟 d :=
  fun _ hx => ⟨hx.2, fun g hg => (hx.1.2 g hg).mono_set hS⟩

/-- **The cosupport of the restricted coefficient ideal lies in the cosupport**: for `A ⊆ N`,
`cosupp(𝓒_N(𝔪)|_A, μ_𝓒) ⊆ cosupp 𝔪` (`N` regular at its points, `d ≥ 1`). -/
theorem cosupport_coeffMarkedAlong_subset {𝔪 : MarkedIdeal n M}
    (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (hd : 1 ≤ 𝔪.d) {A : Set M} (hA : A ⊆ 𝔪.N) :
    cosupport n A (coeffMarkedAlong 𝔪).ideal (coeffMarkedAlong 𝔪).d ⊆ 𝔪.cosupp := by
  intro x hx
  have hxN : x ∈ 𝔪.N := hA hx.1
  set e := sumExp (fun j => 𝔪.d - j) 𝔪.d (𝔪.d - 1) with he
  have he1 : 1 ≤ e := one_le_sumExp (d := fun j => 𝔪.d - j) (m := 𝔪.d) (fun j hj => by omega) _
  -- `x ∈ N ∩ V(𝓓_N^{d-1} 𝔞) = cosupp(𝔞|_N, d)`
  have hcos := cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong h𝔞 hN (𝔪.d - 1)
  rw [Nat.sub_add_cancel hd] at hcos
  show x ∈ cosupport n 𝔪.N 𝔪.ideal 𝔪.d
  rw [hcos]
  refine ⟨hxN, fun g hg => ?_⟩
  have hghol : HolomorphicAt n g x := holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (𝔪.d - 1) x g hg
  -- `g^e` is a germ of the last summand, so it vanishes to order `μ_𝓒 = e ≥ 1` on `A` at `x`
  have hpow : (idealPow (derivMarkedAlong 𝔪 (𝔪.d - 1)).ideal e).mem x (fun p => g p ^ e) :=
    OrderMultiplicativity.pow_mem_idealPow hg hghol e
  have hmem : (coeffMarkedAlong 𝔪).ideal.mem x (fun p => g p ^ e) :=
    (InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ i, i < 𝔪.d ∧ (idealPow (derivMarkedAlong 𝔪 i).ideal
        (sumExp (fun j => (derivMarkedAlong 𝔪 j).d) 𝔪.d i)).mem x s)
      ⟨𝔪.d - 1, by omega, hpow⟩ (holomorphicAt_of_mem_idealPow hpow) : IsInSpanAt (n := n) _ x _)
  have hv := hx.2 _ hmem
  rw [coeffMarkedAlong_d hd, ← he] at hv
  have h0 := (vanishesToOrderOn_one_iff hx.1 (BlowupDerivativeIdeal.holomorphicAt_pow hghol e)).mp (hv.mono he1)
  exact pow_eq_zero_iff (by omega) |>.mp h0

/-- **Włodarczyk `le:S` (first statement) along `N`**: for every `S ⊆ N`, the restriction of the coefficient ideal along `N`
to `S` has cosupport `cosupp 𝔪 ∩ S` (`N` regular at its points, `d ≥ 1`). -/
theorem cosupp_coeffMarkedAlong_withN {𝔪 : MarkedIdeal n M}
    (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (hd : 1 ≤ 𝔪.d) {S : Set M} (hS : S ⊆ 𝔪.N) :
    (withN (coeffMarkedAlong 𝔪) S).cosupp = 𝔪.cosupp ∩ S := by
  refine Subset.antisymm (fun x hx => ⟨cosupport_coeffMarkedAlong_subset hN h𝔞 hd hS hx, hx.1⟩) ?_
  rw [← cosupp_coeffMarkedAlong hN h𝔞 hd]
  exact cosupport_inter_subset_of_subset hS _ _

end

end Hironaka.CoefficientIdealAlongRestriction
