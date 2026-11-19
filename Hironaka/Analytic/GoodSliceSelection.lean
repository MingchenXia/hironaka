import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

/-!
# Choosing a good slice

The Fubini step of Hiep's Lemma 2.1 (`hiep14-weighted-lct:lem-2.1`).  Let `g ≥ 0` have finite
integral over `B × D(a, ρ)` for the product of a measure on `X` with Lebesgue measure on
`ℂ`, and let `Φ(u) = ∫_B g(·, u)`.  Then for every `ε > 0` some height `t` with
`0 < |t| < min(ε, ρ)` satisfies `|t|² Φ(a + t) ≤ ε²`.

Proof.  Otherwise `Φ ≥ ε²/η²` almost everywhere on `D(a, η)` for `η ≤ min(ε, ρ)`, so
`∫_{D(a,η)} Φ ≥ π ε²`.  But `∫_{D(a,η)} Φ → 0` as `η → 0`, because `Φ` is integrable on
`D(a, ρ)` and the discs shrink to a null set.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

theorem exists_good_slice {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {B : Set X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : X × ℂ → ℝ≥0∞} (hg : AEMeasurable g ((μ.restrict B).prod (volume.restrict (ball a ρ))))
    (hfin : ∫⁻ p, g p ∂((μ.restrict B).prod (volume.restrict (ball a ρ))) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℂ, t ≠ 0 ∧ ‖t‖ < ε ∧ ‖t‖ < ρ ∧
      ENNReal.ofReal (‖t‖ ^ 2) * ∫⁻ w in B, g (w, a + t) ∂μ ≤ ENNReal.ofReal (ε ^ 2) := by
  set Φ : ℂ → ℝ≥0∞ := fun u => ∫⁻ w in B, g (w, u) ∂μ with hΦ
  have hΦint : ∫⁻ u in ball a ρ, Φ u ≠ ⊤ := by
    rwa [lintegral_prod_symm _ hg] at hfin
  by_contra hbad
  push Not at hbad
  set κ : Measure ℂ := (volume.restrict (ball a ρ)).withDensity Φ with hκ
  have hκball : ∀ η : ℝ, η ≤ ρ → κ (ball a η) = ∫⁻ u in ball a η, Φ u := by
    intro η hη
    rw [hκ, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball hη)]
  set η : ℕ → ℝ := fun k => min (min ε ρ) (1 / ((k : ℝ) + 1)) with hη
  have hηpos : ∀ k, 0 < η k := fun k => lt_min (lt_min hε hρ) Nat.one_div_pos_of_nat
  have hηε : ∀ k, η k ≤ ε := fun k => (min_le_left _ _).trans (min_le_left _ _)
  have hηρ : ∀ k, η k ≤ ρ := fun k => (min_le_left _ _).trans (min_le_right _ _)
  -- Lower bound on every shrinking disc.
  have hlow : ∀ k, ENNReal.ofReal (ε ^ 2) ≤ κ (ball a (η k)) := by
    intro k
    rw [hκball _ (hηρ k)]
    have hpt : ∀ᵐ u ∂(volume.restrict (ball a (η k))),
        ENNReal.ofReal (ε ^ 2 / η k ^ 2) ≤ Φ u := by
      have hnull : (volume : Measure ℂ) {a} = 0 := measure_singleton a
      filter_upwards [ae_restrict_mem measurableSet_ball,
        (ae_restrict_iff' measurableSet_ball).mpr (measure_eq_zero_iff_ae_notMem.mp hnull |>.mono
          fun u hu _ => hu)] with u hu hua
      have hne : u - a ≠ 0 := sub_ne_zero.mpr (by simpa using hua)
      have hlt : ‖u - a‖ < η k := by simpa [dist_eq_norm] using hu
      have hb := hbad (u - a) hne (hlt.trans_le (hηε k)) (hlt.trans_le (hηρ k))
      rw [add_sub_cancel] at hb
      have hsq : ‖u - a‖ ^ 2 ≤ η k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
      have hb' : ENNReal.ofReal (ε ^ 2) < ENNReal.ofReal (η k ^ 2) * Φ u :=
        hb.trans_le (by gcongr)
      have hη2 : 0 < η k ^ 2 := by have := hηpos k; positivity
      rw [ENNReal.ofReal_div_of_pos hη2]
      refine ENNReal.div_le_of_le_mul ?_
      rw [mul_comm]
      exact hb'.le
    calc ENNReal.ofReal (ε ^ 2)
        ≤ ENNReal.ofReal (ε ^ 2 / η k ^ 2) * volume (ball a (η k)) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (hηpos k).le, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (by have := hηpos k; positivity)]
          have hpi : (1 : ℝ≥0∞) ≤ (NNReal.pi : ℝ≥0∞) := by
            have h1 : (1 : NNReal) ≤ NNReal.pi := by
              rw [← NNReal.coe_le_coe, NNReal.coe_real_pi, NNReal.coe_one]
              linarith [Real.two_le_pi]
            exact_mod_cast h1
          calc ENNReal.ofReal (ε ^ 2) = ENNReal.ofReal (ε ^ 2) * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr
      _ = ∫⁻ u in ball a (η k), ENNReal.ofReal (ε ^ 2 / η k ^ 2) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ u in ball a (η k), Φ u := lintegral_mono_ae hpt
  -- The discs shrink to a `κ`-null set.
  have hanti : Antitone fun k => ball a (η k) := by
    intro i j hij
    refine ball_subset_ball (min_le_min_left _ ?_)
    gcongr
  have h0 : κ (ball a (η 0)) ≠ ⊤ := by
    rw [hκball _ (hηρ 0)]
    exact ne_top_of_le_ne_top hΦint (lintegral_mono_set (ball_subset_ball (hηρ 0)))
  have hlim := tendsto_measure_iInter_atTop (μ := κ)
    (fun k => measurableSet_ball.nullMeasurableSet) hanti ⟨0, h0⟩
  have hinter : κ (⋂ k, ball a (η k)) = 0 := by
    refine measure_mono_null (t := {a}) ?_ ?_
    · intro u hu
      rw [mem_iInter] at hu
      by_contra hua
      have hd : 0 < dist u a := dist_pos.mpr hua
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
      have := hu k
      rw [mem_ball] at this
      exact lt_irrefl _ (this.trans_le (min_le_right _ _) |>.trans hk)
    · refine withDensity_absolutelyContinuous _ _ ?_
      rw [Measure.restrict_apply (measurableSet_singleton a)]
      exact measure_mono_null inter_subset_left (measure_singleton a)
  rw [hinter] at hlim
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨k, hk⟩ := (hlim.eventually (Iio_mem_nhds hpos)).exists
  exact absurd (hlow k) (not_le.mpr hk)

end Hironaka
