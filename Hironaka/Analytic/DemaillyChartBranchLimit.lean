import Hironaka.Analytic.BergmanWeightConvergence
import Hironaka.Analytic.QuantitativeRegularizationChartBranch
import Hironaka.Analytic.QuantitativeRegularizationBergmanInstanceTransport

set_option autoImplicit false

/-!
# Demailly's doubling and convergence for the chart Bergman branches

Copy-4's `lem:regularization` (Step 1) glues the chart Bergman branches
`QuantitativeRegularizationChartBranch.chartBergmanBranch e B ρ φ m = m⁻¹ log K_{B, e^{-mΨ}} ∘ e - ρ ∘ e`
with `Ψ = φ ∘ e⁻¹ + ρ` the corrected weight.  Demailly 1992 (`bou02-volume:2.6`, clause (ii))
needs two more facts about the SAME branches as `m` varies, both proved in
`Hironaka.BergmanWeightConvergence` for the Bergman weight `m⁻¹ log K_{mP}` of a psh `P` on a
bounded convex domain of `ℂ^d`:

* `exists_chartBergmanBranch_two_mul_le` (doubling, from `bergmanWeight_two_mul_le`, i.e.
  Demailly's subadditivity `K_{2m} ≤ C K_m²`): on the patch of a coordinate ball `ball c β`,
  `b_{2m} ≤ b_m + D/m` with `D` depending only on `d`, `c` and `β` — not on the form, the
  potential, the weight `φ`, the chart or `m`;
* `tendsto_chartBergmanBranch` (convergence, from `tendsto_bergmanWeight`): `b_m(x) → φ(x)` at
  every point of the patch, poles included.

These are exactly the branch hypotheses of `DemaillySymmetricGluingLimit.glued_two_mul_le` and
`DemaillySymmetricGluingLimit.tendsto_glued` (programme `TN.3.3.DEMPROVE`, transport of A7/A8 to
the chart branches).

The Bergman objects of `chartBergmanBranch` are elaborated with the canonical Borel structure of
`ComplexModel d`, those of `BergmanWeightConvergence` with `borel _`;
`QuantitativeRegularizationBergmanInstanceTransport.bergmanLog_congr_instance` identifies them.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.DemaillyChartBranchLimit

open BergmanSupWeight BergmanWeightConvergence
  QuantitativeRegularizationChartBranch QuantitativeRegularizationBergmanInstanceTransport

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- Points of a ball have norm below `‖c‖ + β`. -/
theorem norm_lt_of_mem_ball {c z : ComplexModel d} {β : ℝ} (hz : z ∈ ball c β) :
    ‖z‖ < ‖c‖ + β := by
  have h := norm_le_norm_add_norm_sub' z c
  rw [mem_ball, dist_eq_norm] at hz
  linarith

/-- `(a + r) - r = a` in `EReal` for a real `r`. -/
theorem add_coe_sub_coe (a : EReal) (r : ℝ) : a + (r : EReal) - (r : EReal) = a := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add, EReal.bot_sub]
  | top => rw [EReal.top_add_coe, EReal.top_sub_coe]
  | coe s => rw [← EReal.coe_add, ← EReal.coe_sub, add_sub_cancel_right]

/-- **Doubling for the chart branches** (Demailly's subadditivity in a chart): on the patch of
`ball c β`, `b_{2m} ≤ b_m + D/m`, with `D` depending only on `d`, `c`, `β`. -/
theorem exists_chartBergmanBranch_two_mul_le (c : ComplexModel d) {β : ℝ} (hβ : 0 < β) :
    ∃ D : ℝ, ∀ (ζ : SmoothRealForm d Z 2) (φ : Z → EReal), ThetaPlurisubharmonic ζ φ →
      ∀ (e : ComplexChart d Z) (Ω : Set (ComplexModel d)) (ρ : ComplexModel d → ℝ),
      IsSmoothLocalPotential ζ e Ω ρ → ball c β ⊆ Ω →
      ∀ m : ℕ, 1 ≤ m → ∀ x ∈ chartPatch e (ball c β),
        chartBergmanBranch e (ball c β) ρ φ (2 * m) x ≤
          chartBergmanBranch e (ball c β) ρ φ m x + ((D / (m : ℝ) : ℝ) : EReal) := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  have hR : 0 < ‖c‖ + β := by positivity
  obtain ⟨C, _hC, hdouble⟩ := bergmanWeight_two_mul_le d (‖c‖ + β) hR
  refine ⟨Real.log C / 2, fun ζ φ hφ e Ω ρ hρ hβΩ m hm x hx => ?_⟩
  have hpsh : PlurisubharmonicOn (correctedWeight e ρ φ) (ball c β) :=
    (plurisubharmonicOn_correctedWeight hφ hρ).mono hβΩ
  have h := hdouble (ball c β) isOpen_ball (convex_ball c β) (fun z hz => norm_lt_of_mem_ball hz)
    (correctedWeight e ρ φ) hpsh m hm (e.val x) hx.2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hbr : ∀ k : ℕ, chartBergmanBranch e (ball c β) ρ φ k x =
      bergmanWeight (ball c β) (correctedWeight e ρ φ) k (e.val x) - (ρ (e.val x) : EReal) := by
    intro k
    rw [chartBergmanBranch_of_mem hx, bergmanWeight,
      bergmanLog_congr_instance _ _ (borel (ComplexModel d)) ⟨rfl⟩]
  rw [hbr, hbr]
  have hD : (((2 * (m : ℝ))⁻¹ * Real.log C : ℝ) : EReal) = ((Real.log C / 2 / (m : ℝ) : ℝ) : EReal) := by
    congr 1
    field_simp
  rw [hD] at h
  calc bergmanWeight (ball c β) (correctedWeight e ρ φ) (2 * m) (e.val x) - (ρ (e.val x) : EReal)
      ≤ (((Real.log C / 2 / (m : ℝ) : ℝ) : EReal) +
          bergmanWeight (ball c β) (correctedWeight e ρ φ) m (e.val x)) -
          (ρ (e.val x) : EReal) := EReal.sub_le_sub h le_rfl
    _ = bergmanWeight (ball c β) (correctedWeight e ρ φ) m (e.val x) - (ρ (e.val x) : EReal) +
          ((Real.log C / 2 / (m : ℝ) : ℝ) : EReal) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, add_comm (((Real.log C / 2 / (m : ℝ) : ℝ) : EReal)),
          add_assoc, add_assoc, add_comm (((Real.log C / 2 / (m : ℝ) : ℝ) : EReal))]

/-- **Convergence of the chart branches** (Demailly's convergence in a chart): at every point of
the patch of `ball c β`, `b_m(x) → φ(x)` in `EReal`, poles included. -/
theorem tendsto_chartBergmanBranch {ζ : SmoothRealForm d Z 2} {φ : Z → EReal}
    (hφ : ThetaPlurisubharmonic ζ φ) {e : ComplexChart d Z} {Ω : Set (ComplexModel d)}
    {ρ : ComplexModel d → ℝ} (hρ : IsSmoothLocalPotential ζ e Ω ρ) {c : ComplexModel d}
    {β : ℝ} (hβΩ : ball c β ⊆ Ω) {x : Z} (hx : x ∈ chartPatch e (ball c β)) :
    Tendsto (fun m : ℕ => chartBergmanBranch e (ball c β) ρ φ m x) atTop (𝓝 (φ x)) := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  have hβ : 0 < β := by
    have hmem : e.val x ∈ ball c β := hx.2
    rw [mem_ball] at hmem
    exact dist_nonneg.trans_lt hmem
  have hR : 0 < ‖c‖ + β := by positivity
  have hpsh : PlurisubharmonicOn (correctedWeight e ρ φ) (ball c β) :=
    (plurisubharmonicOn_correctedWeight hφ hρ).mono hβΩ
  have hlim := tendsto_bergmanWeight d (‖c‖ + β) hR (ball c β) isOpen_ball (convex_ball c β)
    (fun z hz => norm_lt_of_mem_ball hz) (correctedWeight e ρ φ) hpsh (e.val x) hx.2
  have hval : correctedWeight e ρ φ (e.val x) = φ x + (ρ (e.val x) : EReal) := by
    simp only [correctedWeight, chartFunction, e.val.left_inv hx.1]
  rw [hval] at hlim
  have hbr : ∀ k : ℕ, chartBergmanBranch e (ball c β) ρ φ k x =
      bergmanWeight (ball c β) (correctedWeight e ρ φ) k (e.val x) +
        ((-ρ (e.val x) : ℝ) : EReal) := by
    intro k
    rw [chartBergmanBranch_of_mem hx, bergmanWeight,
      bergmanLog_congr_instance _ _ (borel (ComplexModel d)) ⟨rfl⟩, sub_eq_add_neg,
      EReal.coe_neg]
  simp_rw [hbr]
  have hadd := (EReal.continuousAt_add
    (p := (φ x + (ρ (e.val x) : EReal), ((-ρ (e.val x) : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
      (hlim.prodMk_nhds tendsto_const_nhds)
  have h0 : φ x + (ρ (e.val x) : EReal) + ((-ρ (e.val x) : ℝ) : EReal) = φ x := by
    rw [EReal.coe_neg, ← sub_eq_add_neg, add_coe_sub_coe]
  rw [h0] at hadd
  exact hadd

end

end Hironaka.DemaillyChartBranchLimit
