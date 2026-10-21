/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact
import Hironaka.Support.MarkedIdealOperationsMonotoneControlledOriginalExact
import Hironaka.Support.OrderMultiplicativityCosupportOriginalExact
import Hironaka.Support.DerivativeIdealTowerOriginalExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.CoefficientIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupControlledTransform BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueing DerivativeIdealTower RestrictedIdealExtension

noncomputable section

section FinSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A finite sum of ideals contained in a coherent ideal `𝔅` is contained in `𝔅`. -/
theorem finSumIdeal_le {J : ℕ → GermIdeal n M} {m : ℕ} {𝔅 : GermIdeal n M} (h𝔅 : 𝔅.IsCoherent)
    (h : ∀ i < m, (J i).Le 𝔅) : (finSumIdeal J m).Le 𝔅 := fun y g hg =>
  HomogenizedIdeal.mem_of_isInSpanAt h𝔅 (IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => h i hi y s hs)
    (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g from hg))

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {C : Set M} {π : M' → M}

/-- **Controlled transforms of finite sums** (equal marks, `m ≥ 1`): for coherent `𝔍ᵢ ⊆ 𝓘_C^μ`,
`σ^c(∑_{i<m} 𝔍ᵢ, μ) = ∑_{i<m} σ^c(𝔍ᵢ, μ)`. -/
theorem controlledTransform_finSumIdeal (hπ : IsBlowupAlong n C π) {J : ℕ → GermIdeal n M} {μ : ℕ} :
    ∀ {m : ℕ}, 1 ≤ m → (∀ i < m, (J i).IsCoherent) →
      (∀ i < m, (J i).Le (idealPow (vanishingIdeal (n := n) C) μ)) →
      controlledTransform hπ (finSumIdeal J m) μ =
        finSumIdeal (fun i => controlledTransform hπ (J i) μ) m
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, hJ, hle => by
    rw [finSumIdeal_one (hJ 0 Nat.one_pos),
      finSumIdeal_one (J := fun i => controlledTransform hπ (J i) μ)
        (isCoherent_controlledTransform hπ (hJ 0 Nat.one_pos) (hle 0 Nat.one_pos))]
  | m + 2, _, hJ, hle => by
    have hJ' : ∀ i < m + 1, (J i).IsCoherent := fun i hi => hJ i (by omega)
    have hle' : ∀ i < m + 1, (J i).Le (idealPow (vanishingIdeal (n := n) C) μ) :=
      fun i hi => hle i (by omega)
    have hB := GermIdealPullbackCalculus.isCoherent_idealPow
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) μ
    rw [finSumIdeal_succ fun i hi => hJ i (by omega),
      MarkedIdealOperationsTransform.controlledTransform_sumIdeal hπ (isCoherent_finSumIdeal_of_lt hJ')
        (hJ (m + 1) (by omega)) (finSumIdeal_le hB hle') (hle (m + 1) (by omega)),
      controlledTransform_finSumIdeal hπ (by omega) hJ' hle']
    exact (finSumIdeal_succ (J := fun i => controlledTransform hπ (J i) μ) (μ := m + 1) fun i hi =>
      isCoherent_controlledTransform hπ (hJ i (by omega)) (hle i (by omega))).symm

end FinSum

section MSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable [IsComplexManifold n M]

variable {𝔪 : ℕ → MarkedIdeal n M} {m : ℕ}

/-- **The cosupport of a sum** is the intersection of the cosupports (`N = M`, marks `≥ 1`). -/
theorem cosupp_msum (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) :
    (msum 𝔪 m).cosupp = {x | ∀ i < m, x ∈ (𝔪 i).cosupp} := by
  ext x
  have hhol : ∀ i < m, ∀ y g,
      (idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)).mem y g → HolomorphicAt n g y :=
    fun i _ y g hg => holomorphicAt_of_mem_idealPow hg
  show x ∈ cosupport n (𝔪 0).N
    (finSumIdeal (fun i => idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)) m)
    ((Finset.range m).prod fun j => (𝔪 j).d) ↔ _
  rw [h.N 0 hm, mem_cosupport_finSumIdeal hhol]
  simp only [mem_univ, true_and, Set.mem_ofPred_eq]
  refine forall₂_congr fun i hi => ?_
  have hpow := OrderMultiplicativity.cosupport_idealPow_mul_eq
    (fun y g hg => holomorphicAt_of_mem (h.coh i hi) hg)
    (one_le_sumExp h.d i) (𝔪 i).d
  rw [mul_sumExp (fun j => (𝔪 j).d) hi] at hpow
  rw [hpow, MarkedIdeal.cosupp, h.N i hi]

/-- **A centre is admissible for a sum iff it is admissible for every summand.** -/
theorem isAdmissibleCentre_msum_iff (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) {C : Set M} :
    (msum 𝔪 m).IsAdmissibleCentre C ↔ ∀ i < m, (𝔪 i).IsAdmissibleCentre C := by
  rw [IsAdmissibleCentre, cosupp_msum h hm]
  constructor
  · rintro ⟨hC, hsub, hnc⟩ i hi
    exact ⟨hC, fun x hx => hsub hx i hi, by rw [h.E i hi]; exact hnc⟩
  · intro hall
    exact ⟨(hall 0 hm).1, fun x hx i hi => (hall i hi).2.1 hx, (hall 0 hm).2.2⟩

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {C : Set M} {π : M' → M}

/-- **One step of `le:operations` (1)**: the transform of a sum is the sum of the transforms. -/
theorem geoTransform_msum (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) (hπ : IsBlowupAlong n C π)
    (hC : ∀ i < m, (𝔪 i).IsAdmissibleCentre C) :
    (msum 𝔪 m).geoTransform C π = msum (fun i => (𝔪 i).geoTransform C π) m := by
  have hle : ∀ i < m, (𝔪 i).ideal.Le (idealPow (vanishingIdeal (n := n) C) (𝔪 i).d) := fun i hi =>
    HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (h.N i hi) (h.coh i hi) (hC i hi)
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hlepow : ∀ i < m, (idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)).Le
      (idealPow (vanishingIdeal (n := n) C) ((Finset.range m).prod fun j => (𝔪 j).d)) :=
      fun i hi => by
    have := MarkedIdealOperationsTransform.idealPow_mono (hle i hi) (sumExp (fun j => (𝔪 j).d) m i)
    rwa [MarkedIdealOperationsTransform.idealPow_idealPow hIC, mul_sumExp (fun j => (𝔪 j).d) hi]
      at this
  have hideal : ((msum 𝔪 m).geoTransform C π).ideal =
      (msum (fun i => (𝔪 i).geoTransform C π) m).ideal := by
    have hN : (msum 𝔪 m).N = univ := h.N 0 hm
    rw [geoTransform_ideal_eq_controlledTransform hN h.isCoherent_msum hπ]
    show controlledTransform hπ (finSumIdeal (fun i => idealPow (𝔪 i).ideal
        (sumExp (fun j => (𝔪 j).d) m i)) m) ((Finset.range m).prod fun j => (𝔪 j).d) = _
    rw [controlledTransform_finSumIdeal hπ hm
      (fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.coh i hi) _) hlepow]
    refine finSumIdeal_congr fun i hi => ?_
    rw [geoTransform_ideal_eq_controlledTransform (h.N i hi) (h.coh i hi) hπ,
      ← MarkedIdealOperationsTransform.controlledTransform_idealPow hπ (h.coh i hi) (hle i hi),
      ← mul_sumExp (fun j => (𝔪 j).d) hi]
    rfl
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hideal rfl

/-- One admissible step keeps an ambient family ambient. -/
theorem IsAmbientFamily.geoTransform (h : IsAmbientFamily 𝔪 m) (hπ : IsBlowupAlong n C π)
    (hC : ∀ i < m, (𝔪 i).IsAdmissibleCentre C) :
    IsAmbientFamily (fun i => (𝔪 i).geoTransform C π) m where
  N i hi := geoTransform_N_eq_univ (h.N i hi) hπ
  E i hi := by simp only [geoTransform_E, h.E i hi]
  coh i hi := by
    rw [geoTransform_ideal_eq_controlledTransform (h.N i hi) (h.coh i hi) hπ]
    exact isCoherent_controlledTransform hπ (h.coh i hi)
      (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (h.N i hi) (h.coh i hi) (hC i hi))
  d i hi := h.d i hi

end MSum

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk `le:operations` (1)** for `m ≥ 1` summands (`N = M`, common `E`, coherent ideals,
marks `≥ 1`): the multiple test blow-ups of `𝔪 0 + … + 𝔪 (m - 1)` are exactly the simultaneous
multiple test blow-ups of the `𝔪 i`, and along them the transform of the sum is the sum of the
transforms. -/
theorem geoTransformAlong_msum (𝔪 : ℕ → MarkedIdeal n X) {m : ℕ} (hm : 1 ≤ m)
    (h : IsAmbientFamily 𝔪 m) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (msum 𝔪 m) T ↔ ∀ i < m, IsGeoTestTower (𝔪 i) T) ∧
      ((∀ i < m, IsGeoTestTower (𝔪 i) T) →
        geoTransformAlong (msum 𝔪 m) T = msum (fun i => geoTransformAlong (𝔪 i) T) m ∧
        IsAmbientFamily (fun i => geoTransformAlong (𝔪 i) T) m)
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ => ⟨rfl, h⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_msum 𝔪 hm h T
      refine ⟨?_, fun hall => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          have hTi := ihT.mp hT
          obtain ⟨heq, hfam⟩ := ihE hTi
          rw [heq, isAdmissibleCentre_msum_iff hfam hm] at hC
          exact fun i hi => ⟨hTi i hi, hC i hi⟩
        · intro hall
          have hTi : ∀ i < m, IsGeoTestTower (𝔪 i) T := fun i hi => (hall i hi).1
          obtain ⟨heq, hfam⟩ := ihE hTi
          refine ⟨ihT.mpr hTi, ?_⟩
          rw [heq, isAdmissibleCentre_msum_iff hfam hm]
          exact fun i hi => (hall i hi).2
      · have hTi : ∀ i < m, IsGeoTestTower (𝔪 i) T := fun i hi =>
          ((isGeoTestTower_step_iff (𝔪 i) T C π hπ).mp (hall i hi)).1
        have hCi : ∀ i < m, (geoTransformAlong (𝔪 i) T).IsAdmissibleCentre C := fun i hi =>
          ((isGeoTestTower_step_iff (𝔪 i) T C π hπ).mp (hall i hi)).2
        obtain ⟨heq, hfam⟩ := ihE hTi
        refine ⟨?_, hfam.geoTransform hπ hCi⟩
        rw [geoTransformAlong_step, heq, geoTransform_msum hfam hm hπ hCi]
        rfl

/-- `𝓓^0(𝔪) = 𝔪`. -/
theorem derivMarked_zero {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : derivMarked 𝔪 0 = 𝔪 := by
  cases 𝔪; rfl

/-- **Włodarczyk, Lemma `le:coeff`: `𝓒(𝔪) ≃ 𝔪`** (`N = M`, `𝔞` coherent, `d ≥ 1`): a tower is a
multiple test blow-up of `𝓒(𝔪)` iff it is one of `𝔪`, and along it the cosupports of the transforms
agree. -/
theorem coeff_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower (coeffMarked 𝔪) T ↔ IsGeoTestTower 𝔪 T) ∧
      (IsGeoTestTower 𝔪 T →
        (geoTransformAlong (coeffMarked 𝔪) T).cosupp = (geoTransformAlong 𝔪 T).cosupp) := by
  have hfam := isAmbientFamily_derivMarked hN h𝔞
  obtain ⟨hiff, heq⟩ := geoTransformAlong_msum (fun i => derivMarked 𝔪 i) hd hfam T
  have hall : IsGeoTestTower 𝔪 T → ∀ i < 𝔪.d, IsGeoTestTower (derivMarked 𝔪 i) T :=
    fun hT i hi => (inclusions_tower 𝔪 hN h𝔞 (le_of_lt hi) T hT).1
  refine ⟨⟨fun hC => ?_, fun hT => (show IsGeoTestTower (msum _ _) T from hiff.mpr (hall hT))⟩,
    fun hT => ?_⟩
  · have := hiff.mp hC 0 hd
    rwa [derivMarked_zero] at this
  · obtain ⟨he, hfamT⟩ := heq (hall hT)
    rw [show coeffMarked 𝔪 = msum (fun i => derivMarked 𝔪 i) 𝔪.d from rfl, he,
      cosupp_msum hfamT hd]
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      have := hx 0 hd
      rwa [derivMarked_zero] at this
    · intro hx i hi
      obtain ⟨-, hNT, hNDT, -, -, -, hle⟩ := inclusions_tower 𝔪 hN h𝔞 (le_of_lt hi) T hT
      have hdT : i ≤ (geoTransformAlong 𝔪 T).d := by
        rw [d_geoTransformAlong]; exact le_of_lt hi
      have h1 := cosupp_subset_cosupp_derivMarked hNT hdT hx
      show x ∈ cosupport n (geoTransformAlong (derivMarked 𝔪 i) T).N
        (geoTransformAlong (derivMarked 𝔪 i) T).ideal (geoTransformAlong (derivMarked 𝔪 i) T).d
      rw [hNDT, d_geoTransformAlong, derivMarked_d]
      have h1' : x ∈ cosupport n univ (iterDerivIdeal (geoTransformAlong 𝔪 T).ideal i)
          ((geoTransformAlong 𝔪 T).d - i) := by
        have := h1
        rwa [MarkedIdeal.cosupp, derivMarked_N, hNT] at this
      rw [d_geoTransformAlong] at h1'
      exact cosupport_subset_of_le hle _ h1'

end Tower

end

end Hironaka.CoefficientIdeal
