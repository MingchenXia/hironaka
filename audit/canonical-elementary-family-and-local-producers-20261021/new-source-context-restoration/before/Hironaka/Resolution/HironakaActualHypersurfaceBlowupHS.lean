/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualInvertibleIntrinsicHS
import Hironaka.Resolution.HironakaHypersurfaceMultiplicityDescent
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS

/-! Genuine all-order HS nonincrease for original maximal-order hypersurface blowups. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHypersurfaceBlowupHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaHolomorphicJetChartInvariance HironakaActualInvertibleIntrinsicHS
  HironakaHypersurfaceStrictIdeal HironakaHypersurfaceMultiplicityDescent
  HironakaActualBlowupOffCentreIntrinsicHS BlowupTowers MarkedIdeals GermIdealOrder IdealWeightPowers

/-- The computed principal jet dimension is monotone in the genuine original order. -/
theorem actual_principal_binomial_hs_mono (n μ ν ℓ : ℕ) (hμν : μ ≤ ν) :
    Nat.choose (n+ℓ) n - (if μ ≤ ℓ then Nat.choose (n+(ℓ-μ)) n else 0) ≤
      Nat.choose (n+ℓ) n - (if ν ≤ ℓ then Nat.choose (n+(ℓ-ν)) n else 0) := by
  by_cases hν : ν ≤ ℓ
  · rw [if_pos (hμν.trans hν),if_pos hν]
    have hc := Nat.choose_le_choose n (show n+(ℓ-ν) ≤ n+(ℓ-μ) by omega)
    omega
  · rw [if_neg hν]
    split_ifs <;> omega

section OriginalIdeals
variable {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- ONLY original invertibility and the EXISTING original order comparison give EVERY intrinsic HS inequality. -/
theorem actual_invertible_intrinsic_hs_le_of_original_order_le
    (A : GermIdeal n Y) (B : GermIdeal n X) (hA : A.IsInvertible) (hB : B.IsInvertible)
    (y : Y) (x : X) (hle : order n univ A y ≤ order n univ B x) (ℓ : ℕ) :
    hilbertSamuelAt A y ℓ ≤ hilbertSamuelAt B x ℓ := by
  obtain ⟨μ,hμ,hprofileA⟩ := exists_actual_original_order_intrinsic_hs A hA y
  obtain ⟨ν,hν,hprofileB⟩ := exists_actual_original_order_intrinsic_hs B hB x
  rw [hμ,hν] at hle
  have hμν : μ ≤ ν := by exact_mod_cast hle
  rw [hprofileA ℓ,hprofileB ℓ]
  exact actual_principal_binomial_hs_mono n μ ν ℓ hμν
end OriginalIdeals

/-- True maximal-order hypersurface geometry gives ALL-point ALL-order intrinsic HS nonincrease,
including SINGULAR exceptional strict-transform points, without any HS comparison certificate. -/
theorem actual_hypersurface_blowup_intrinsic_hs_nonincreasing {m : ℕ}
    {X Y : CMfd.{u} (m+1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m+1) W)
    (hI : (vanishingIdeal (n := m+1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m+1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m+1) E) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m+1) univ (vanishingIdeal (n := m+1) W) x ≤ (μ : ℕ∞))
    {C : Set X} (hCadm : (⟨univ,E,vanishingIdeal (n := m+1) W,μ⟩ : MarkedIdeal (m+1) X).IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong (m+1) C π) (y : Y) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := m+1) (strictTransform (m+1) π W)) y ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := m+1) W) (π y) ℓ := by
  by_cases hyC : π y ∈ C
  · have hcoh := CartanIrreducible.cartanCoherence W hWa
    have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hCadm.1 hCadm.2.1
    have hstrict := controlledTransform_vanishingIdeal_eq_strictTransform hWa hI hpure hE hμ hbound hCadm hπ
    have hnewinv : (vanishingIdeal (n := m+1) (strictTransform (m+1) π W)).IsInvertible := by
      rw [← hstrict]
      exact isInvertible_controlledTransform hπ hI μ hle
    have hmax := isMaximalOrder_vanishingIdeal_of_order_le hWa μ hbound
    have hnewmax := hmax.controlledTransform hπ hcoh hle
    rw [hstrict] at hnewmax
    apply actual_invertible_intrinsic_hs_le_of_original_order_le _ _ hnewinv hI y (π y) _ ℓ
    exact (order_le_of_isMaximalOrder hnewmax y).trans
      ((le_order_iff (𝔞 := vanishingIdeal (n := m+1) W) (fun _ hg => hg.1)).mpr (hCadm.2.1 hyC).2)
  · exact (hilbertSamuelAt_actual_strict_blowup_off_centre hπ hWa y hyC ℓ).le
end
end Hironaka.HironakaActualHypersurfaceBlowupHS
