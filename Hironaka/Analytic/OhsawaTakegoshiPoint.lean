import Hironaka.Analytic.StrongOpennessRegularRoute
import Hironaka.Analytic.HiepSliceLemma
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicPullback

set_option autoImplicit false

/-!
# L² extension from a point

`exists_extension_from_point`: on a bounded open convex domain `Ω ⊆ ℂⁿ` with a
plurisubharmonic weight `φ`, every point `y ∈ Ω` carries a holomorphic function `F` with
`F y = 1` and `∫_Ω |F|² e^{-cφ} ≤ C e^{-cφ(y)}`, where `C` depends only on `n` and the bound
`R` on `‖z‖`.  It follows from the Ohsawa--Takegoshi hyperplane theorem
(`ohsawaTakegoshiHyperplane_of_regular`) by induction on `n` through the coordinate
hyperplanes, first at `y = 0` and then at an arbitrary point by translation.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.OhsawaTakegoshiPoint

noncomputable section



/-- The extension from the origin, by induction on the dimension. -/
theorem exists_extension_from_zero (n : ℕ) : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
      ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
      (0 : ComplexModel n) ∈ Ω → ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧ F 0 = 1 ∧
        (∫⁻ z in Ω, multiplierDensity φ c F z) ≤ ENNReal.ofReal C * multiplierWeight c (φ 0) := by
  induction n with
  | zero =>
    let _ : MeasurableSpace (ComplexModel 0) := borel _
    have _ : BorelSpace (ComplexModel 0) := ⟨rfl⟩
    intro R hR
    refine ⟨(volume (univ : Set (ComplexModel 0))).toReal + 1, by positivity,
      fun Ω hΩ hconv hbd φ hφ c hc h0 => ⟨fun _ => 1, differentiableOn_const _, rfl, ?_⟩⟩
    have hfin : volume (univ : Set (ComplexModel 0)) ≠ ⊤ :=
      (isCompact_univ (X := ComplexModel 0)).measure_lt_top.ne
    have hconst : ∀ z : ComplexModel 0,
        multiplierDensity φ c (fun _ => 1) z = multiplierWeight c (φ 0) := fun z => by
      rw [Subsingleton.elim z (0 : ComplexModel 0)]
      simp [multiplierDensity]
    simp only [hconst]
    rw [setLIntegral_const, mul_comm]
    gcongr
    calc volume Ω ≤ volume (univ : Set (ComplexModel 0)) := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (volume (univ : Set (ComplexModel 0))).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  | succ n ih =>
    let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    let _ : MeasurableSpace (ComplexModel (n + 1)) := borel _
    have _ : BorelSpace (ComplexModel (n + 1)) := ⟨rfl⟩
    intro R hR
    obtain ⟨Cn, hCn, hn⟩ := ih R hR
    obtain ⟨CT, hCT, hOT⟩ :=
      ohsawaTakegoshiHyperplane_of_regular ohsawaTakegoshiHyperplaneRegular n R hR
    refine ⟨CT * Cn, mul_pos hCT hCn, fun Ω hΩ hconv hbd φ hφ c hc h0 => ?_⟩
    have hemb0 : hyperplaneEmbedding n 0 = 0 := map_zero (hyperplaneCLM n)
    set Ω' : Set (ComplexModel n) := hyperplaneEmbedding n ⁻¹' Ω with hΩ'
    have hΩ'open : IsOpen Ω' := hΩ.preimage (continuous_hyperplaneEmbedding n)
    have hΩ'conv : Convex ℝ Ω' :=
      hconv.linear_preimage ((hyperplaneCLM n).toLinearMap.restrictScalars ℝ)
    have hbd' : ∀ w ∈ Ω', ‖w‖ < R := fun w hw => by
      simpa [norm_hyperplaneEmbedding] using hbd _ hw
    have hφ' : PlurisubharmonicOn (fun w => φ (hyperplaneEmbedding n w)) Ω' :=
      hφ.comp_continuousLinearMap (hyperplaneCLM n)
    have h0' : (0 : ComplexModel n) ∈ Ω' := by
      show hyperplaneEmbedding n 0 ∈ Ω
      rw [hemb0]; exact h0
    obtain ⟨f, hfhol, hf0, hfint⟩ := hn Ω' hΩ'open hΩ'conv hbd' _ hφ' c hc h0'
    have hbdlast : ∀ z ∈ Ω, ‖z (Fin.last n)‖ < R := fun z hz =>
      lt_of_le_of_lt (PiLp.norm_apply_le z _) (hbd z hz)
    obtain ⟨F, hFhol, hFext, hFint⟩ := hOT Ω hΩ hconv hbdlast φ hφ c hc f hfhol
    refine ⟨F, hFhol, ?_, ?_⟩
    · have := hFext 0 h0'
      rwa [hemb0, hf0] at this
    · calc (∫⁻ z in Ω, multiplierDensity φ c F z)
          ≤ ENNReal.ofReal CT * ∫⁻ w in Ω',
              multiplierDensity (fun w => φ (hyperplaneEmbedding n w)) c f w := hFint
        _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal Cn * multiplierWeight c (φ 0)) := by
          gcongr
          simpa [hemb0] using hfint
        _ = ENNReal.ofReal (CT * Cn) * multiplierWeight c (φ 0) := by
          rw [ENNReal.ofReal_mul hCT.le, mul_assoc]

/-- **L² extension from a point.** On an open convex domain `Ω ⊆ ℂⁿ` contained in the ball of
radius `R`, with a plurisubharmonic weight `φ` and an exponent `c > 0`, every point `y ∈ Ω`
carries a holomorphic `F` with `F y = 1` and `∫_Ω |F|² e^{-cφ} ≤ C e^{-cφ(y)}`, where `C`
depends only on `n` and `R`. -/
theorem exists_extension_from_point (n : ℕ) : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel n), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
      ∀ φ : ComplexModel n → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
      ∀ y ∈ Ω, ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F Ω ∧ F y = 1 ∧
        (∫⁻ z in Ω, multiplierDensity φ c F z) ≤ ENNReal.ofReal C * multiplierWeight c (φ y) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, h0⟩ := exists_extension_from_zero n (2 * R) (by linarith)
  refine ⟨C, hC, fun Ω hΩ hconv hbd φ hφ c hc y hy => ?_⟩
  set Ω' : Set (ComplexModel n) := (fun x => x + y) ⁻¹' Ω with hΩ'
  have hΩ'open : IsOpen Ω' := hΩ.preimage (continuous_id.add continuous_const)
  have hΩ'conv : Convex ℝ Ω' := by
    have := hconv.translate_preimage_right y
    simpa [hΩ', add_comm] using this
  have hbd' : ∀ x ∈ Ω', ‖x‖ < 2 * R := fun x hx => by
    have h1 := hbd _ hx
    have h2 := hbd y hy
    calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
      _ < 2 * R := by linarith
  have hφ' : PlurisubharmonicOn (fun x => φ (x + y)) Ω' :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hΩ'open
      ((differentiable_id.add_const y).differentiableOn) (fun x hx => hx) hφ
  have hy' : (0 : ComplexModel n) ∈ Ω' := by simpa [hΩ'] using hy
  obtain ⟨F', hF'hol, hF'0, hF'int⟩ := h0 Ω' hΩ'open hΩ'conv hbd' _ hφ' c hc hy'
  refine ⟨fun x => F' (x - y), ?_, by simpa using hF'0, ?_⟩
  · refine hF'hol.comp (differentiable_id.sub_const y).differentiableOn fun x hx => ?_
    simpa [hΩ'] using hx
  · have hmp : MeasurePreserving (fun x : ComplexModel n => x + y) volume volume :=
      measurePreserving_add_right volume y
    have htrans : (∫⁻ z in Ω, multiplierDensity φ c (fun x => F' (x - y)) z) =
        ∫⁻ x in Ω', multiplierDensity (fun x => φ (x + y)) c F' x := by
      rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight y)]
      simp only [multiplierDensity, add_sub_cancel_right]
      rfl
    rw [htrans]
    simpa using hF'int

end

end Hironaka.OhsawaTakegoshiPoint
