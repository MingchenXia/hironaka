/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.OrderTaylorCosupport
import Hironaka.Support.CoefficientIdealTowerOperationsOriginalExact
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientIdealRestriction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal
  HomogenizedGlueing HomogenizedGlueingTower MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal RestrictedIdealWeight BlowupStrictSubmanifold

noncomputable section

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable [IsComplexManifold n M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M']

/-- **The support of the coefficient ideal restricted to any set lies in the support** (`N = M`, `𝔞` coherent,
`d ≥ 1`): `supp(𝓒(𝔪)|_A) ⊆ supp(𝔪)`.  Only the last summand `(𝓓^{d-1}𝔞, 1)` is used: on its support `𝓓^{d-1}𝔞`
vanishes at the point, and `supp(𝔞, d) = V(𝓓^{d-1}𝔞)` (Giraud--Villamayor). -/
theorem cosupport_coeff_subset {𝔪 : MarkedIdeal n M} (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) (A : Set M) :
    cosupport n A (coeffMarked 𝔪).ideal (coeffMarked 𝔪).d ⊆ 𝔪.cosupp := by
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x :=
    hol_of_isCoherent h𝔞
  set D : ℕ → ℕ := fun j => (derivMarked 𝔪 j).d with hD
  have hD1 : ∀ j < 𝔪.d, 1 ≤ D j := fun j hj => by simp only [hD, derivMarked_d]; omega
  set e := sumExp D 𝔪.d (𝔪.d - 1) with he
  have he1 : 1 ≤ e := one_le_sumExp hD1 _
  have hmark : (coeffMarked 𝔪).d = e := by
    have := mul_sumExp D (show 𝔪.d - 1 < 𝔪.d by omega)
    simp only [hD, derivMarked_d, show 𝔪.d - (𝔪.d - 1) = 1 by omega, one_mul] at this
    exact this.symm
  intro x hx
  have hJ : ∀ i < 𝔪.d, ∀ y g, (idealPow (derivMarked 𝔪 i).ideal (sumExp D 𝔪.d i)).mem y g →
      HolomorphicAt n g y := fun _ _ _ _ hg => holomorphicAt_of_mem_idealPow hg
  have hx' := (mem_cosupport_finSumIdeal hJ).mp hx
  have hlast := hx'.2 (𝔪.d - 1) (by omega)
  have hzero : x ∈ (iterDerivIdeal 𝔪.ideal (𝔪.d - 1)).zeroLocus := by
    intro g hg
    have hghol : HolomorphicAt n g x := holomorphicAt_of_mem_iterDerivIdeal hhol (𝔪.d - 1) x g hg
    have hpow : (idealPow (derivMarked 𝔪 (𝔪.d - 1)).ideal e).mem x (fun p => g p ^ e) :=
      OrderMultiplicativity.pow_mem_idealPow hg hghol e
    have hv := (hlast.2 _ hpow).mono (show 1 ≤ (coeffMarked 𝔪).d by rw [hmark]; exact he1)
    have h0 := (vanishesToOrderOn_one_iff hx'.1 (holomorphicAt_of_mem_idealPow hpow)).mp hv
    exact (pow_eq_zero_iff (by omega)).mp h0
  rw [← OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol, Nat.sub_add_cancel hd] at hzero
  rw [MarkedIdeal.cosupp, hN]
  exact hzero

end OneSpace

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **A multiple test blow-up of a restriction `𝔟|_S` has its centres in the strict transforms of `S`.** -/
theorem centresIn_of_isGeoTestTower_withN (𝔟 : MarkedIdeal n X) (S : Set X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (withN 𝔟 S) T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      refine ⟨centresIn_of_isGeoTestTower_withN 𝔟 S T hT0, fun x hx => ?_⟩
      rw [← N_geoTransformAlong_withN 𝔟 S T]
      exact hC.subset_N hx

theorem isCoherent_coeffMarked {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    (coeffMarked 𝔪).ideal.IsCoherent :=
  (isAmbientFamily_derivMarked hN h𝔞).isCoherent_msum

/-- **Włodarczyk `le:S`, the support** (GGT Proposition 5.6.4, first statement): for `𝔪 = (X, X, E, 𝔞, μ)` with
`𝔞` coherent and `μ ≥ 1`, and ANY set `S`, `supp(𝔪) ∩ S = supp(𝓒(𝔪)|_S)`. -/
theorem cosupp_coeff_withN (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (S : Set X) : (withN (coeffMarked 𝔪) S).cosupp = 𝔪.cosupp ∩ S := by
  refine Subset.antisymm (fun x hx => ⟨cosupport_coeff_subset hN h𝔞 hd S hx, hx.1⟩) ?_
  have h0 := (coeff_tower 𝔪 hN h𝔞 hd (BlowupTower.refl : BlowupTower X X)).2 trivial
  rw [geoTransformAlong_refl, geoTransformAlong_refl] at h0
  rw [← h0]
  exact cosupp_inter_subset_cosupp_withN (𝔟 := coeffMarked 𝔪) hN S

/-- **Włodarczyk `le:S` (1) and the inclusion `⊆` of (2)** (GGT Proposition 5.6.4 (1)--(2)): let
`𝔪 = (X, X, E, 𝔞, μ)` with `𝔞` coherent and `μ ≥ 1`, `S` a closed submanifold, and `T` a multiple test blow-up of
`𝔪` whose centres lie in the strict transforms of `S`.  Then `T` is a multiple test blow-up of `𝓒(𝔪)|_S`, along it
`[𝓒(𝔪)|_S]_T ≃ 𝓒(𝔪)_T|_{S_T}`, and `supp(𝔪_T) ∩ S_T ⊆ supp[𝓒(𝔪)|_S]_T`. -/
theorem coeff_restrict_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (hTS : CentresIn S T) :
    IsGeoTestTower (withN (coeffMarked 𝔪) S) T ∧
      RestrictEquiv (geoTransformAlong (withN (coeffMarked 𝔪) S) T)
        (withN (geoTransformAlong (coeffMarked 𝔪) T) (strictAlong T S)) ∧
      (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S ⊆
        (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp := by
  obtain ⟨hiff, hcos⟩ := coeff_tower 𝔪 hN h𝔞 hd T
  have hTc : IsGeoTestTower (coeffMarked 𝔪) T := hiff.mpr hT
  obtain ⟨hsT, hNT, -, -, -, hRE⟩ :=
    restrict_tower (coeffMarked 𝔪) hN (isCoherent_coeffMarked hN h𝔞) hS T hTc hTS
  refine ⟨hsT, hRE, ?_⟩
  rw [hRE.cosupp_eq, ← hcos hT]
  exact cosupp_inter_subset_cosupp_withN hNT _

end Tower

end

end Hironaka.CoefficientIdealRestriction
