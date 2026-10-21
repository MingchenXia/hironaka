import Hironaka.MarkedIdeal.DerivativeAmbientMarkedDataExact
import Hironaka.Blowup.BlowupDerivativeMaximalOrder
import Hironaka.MarkedIdeal.HadamardBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.DerivativeIdealTower

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupControlledTransform BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal

noncomputable section

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable [IsComplexManifold n M]

/-- **Giraud** (`N = M`): `cosupp(𝔪) ⊆ cosupp(𝓓^j 𝔪)` for `j ≤ d`. -/
theorem cosupp_subset_cosupp_derivMarked {𝔪 : MarkedIdeal n M} (hN : 𝔪.N = univ) {j : ℕ}
    (hj : j ≤ 𝔪.d) : 𝔪.cosupp ⊆ (derivMarked 𝔪 j).cosupp := by
  intro y hy
  have h1 : y ∈ cosupport n univ 𝔪.ideal ((𝔪.d - j) + j) := by
    rw [Nat.sub_add_cancel hj, ← hN]; exact hy
  have h2 := MaximalContact.cosupport_add_subset_cosupport_iterDerivIdeal 𝔪.ideal (𝔪.d - j) j h1
  show y ∈ cosupport n 𝔪.N (iterDerivIdeal 𝔪.ideal j) (𝔪.d - j)
  rw [hN]; exact h2

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {C : Set M} {π : M' → M}

/-- **Controlled transforms are monotone in the ideal.** -/
theorem controlledTransform_le_of_le (hπ : IsBlowupAlong n C π) {𝔟 𝔠 : GermIdeal n M}
    (h : 𝔟.Le 𝔠) (μ : ℕ) : (controlledTransform hπ 𝔟 μ).Le (controlledTransform hπ 𝔠 μ) :=
  fun y _ hf => ⟨hf.1, fun g hg => GermIdealPullbackCalculus.pullback_le_pullback h y _ (hf.2 g hg)⟩

end OneSpace

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk, Lemma `le:inclusions2`** (`N = M`, transform with centre-relative strict
transforms): let `𝔪 = (X, X, E, 𝔞, d)` with `𝔞` coherent and `j ≤ d`.  Every multiple test blow-up
`T` of `𝔪` is a multiple test blow-up of `𝓓^j(𝔪)`, and `[𝓓^j(𝔪)]_T ⊆ 𝓓^j(𝔪_T)`.  Along `T` both
transforms keep `N` the whole space and the same `E`, and their ideals stay coherent. -/
theorem inclusions_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    {j : ℕ} (hj : j ≤ 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (derivMarked 𝔪 j) T ∧
      (geoTransformAlong 𝔪 T).N = univ ∧ (geoTransformAlong (derivMarked 𝔪 j) T).N = univ ∧
      (geoTransformAlong (derivMarked 𝔪 j) T).E = (geoTransformAlong 𝔪 T).E ∧
      (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      (geoTransformAlong (derivMarked 𝔪 j) T).ideal.IsCoherent ∧
      (geoTransformAlong (derivMarked 𝔪 j) T).ideal.Le
        (iterDerivIdeal (geoTransformAlong 𝔪 T).ideal j)
  | _, .refl => fun _ =>
      ⟨trivial, hN, hN, rfl, h𝔞, isCoherent_iterDerivIdeal h𝔞 j, fun _ _ h => h⟩
  | _, .step T C π hπ => fun hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hD, hNT, hNDT, hE, hcoh, hcohD, hle⟩ := inclusions_tower 𝔪 hN h𝔞 hj T hT0
      have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
      have hdD : (geoTransformAlong (derivMarked 𝔪 j) T).d = 𝔪.d - j :=
        d_geoTransformAlong (derivMarked 𝔪 j) T
      -- the centre is admissible for the transform of `𝓓^j(𝔪)`
      have hCD : (geoTransformAlong (derivMarked 𝔪 j) T).IsAdmissibleCentre C := by
        refine ⟨hC.1, fun y hy => ?_, by rw [hE]; exact hC.2.2⟩
        have h1 : y ∈ cosupport n univ (geoTransformAlong 𝔪 T).ideal ((𝔪.d - j) + j) := by
          have := hC.2.1 hy
          rwa [MarkedIdeal.cosupp, hNT, hd, ← Nat.sub_add_cancel hj] at this
        have h2 := MaximalContact.cosupport_add_subset_cosupport_iterDerivIdeal
          (geoTransformAlong 𝔪 T).ideal (𝔪.d - j) j h1
        show y ∈ cosupport n (geoTransformAlong (derivMarked 𝔪 j) T).N
          (geoTransformAlong (derivMarked 𝔪 j) T).ideal (geoTransformAlong (derivMarked 𝔪 j) T).d
        rw [hNDT, hdD]
        exact cosupport_subset_of_le hle (𝔪.d - j) h2
      have hleC : (geoTransformAlong 𝔪 T).ideal.Le
          (idealPow (vanishingIdeal (n := n) C) (𝔪.d - j + j)) := by
        rw [Nat.sub_add_cancel hj, ← hd]
        exact HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcoh hC
      have hleCD : (geoTransformAlong (derivMarked 𝔪 j) T).ideal.Le
          (idealPow (vanishingIdeal (n := n) C) (geoTransformAlong (derivMarked 𝔪 j) T).d) :=
        HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNDT hcohD hCD
      have hT' : (geoTransformAlong 𝔪 (.step T C π hπ)).ideal =
          controlledTransform hπ (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).d := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcoh hπ]
      have hTD' : (geoTransformAlong (derivMarked 𝔪 j) (.step T C π hπ)).ideal =
          controlledTransform hπ (geoTransformAlong (derivMarked 𝔪 j) T).ideal
            (geoTransformAlong (derivMarked 𝔪 j) T).d := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNDT hcohD hπ]
      refine ⟨(isGeoTestTower_step_iff (derivMarked 𝔪 j) T C π hπ).mpr ⟨hD, hCD⟩,
        geoTransform_N_eq_univ hNT hπ, geoTransform_N_eq_univ hNDT hπ, ?_, ?_, ?_, ?_⟩
      · simp only [geoTransformAlong_step, geoTransform_E, hE]
      · rw [hT']
        exact isCoherent_controlledTransform hπ hcoh
          (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcoh hC)
      · rw [hTD']
        exact isCoherent_controlledTransform hπ hcohD hleCD
      · rw [hTD', hT', hdD, hd]
        have hinc := BlowupDerivativeIdeal.controlledTransform_iterDerivIdeal_le hπ hcoh j (𝔪.d - j)
          hleC
        rw [Nat.sub_add_cancel hj] at hinc
        exact fun y g hg => hinc y g (controlledTransform_le_of_le hπ hle (𝔪.d - j) y g hg)

end Tower

end

end Hironaka.DerivativeIdealTower
