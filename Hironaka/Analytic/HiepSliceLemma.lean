import Hironaka.Analytic.StrongOpennessSliceInduction
import Hironaka.Analytic.PotentialTheory.Distributional.DiscRecovery
import Hironaka.Analytic.HolomorphicPullback

set_option autoImplicit false

/-!
# Hiep's Lemma 2.1 for increasing sequences: analytic ingredients

Ingredients of `SliceExtensionProperty` (`Hironaka.StrongOpennessSliceInduction`), the
analytic half of the strong-openness induction (I-0114):

* `sliceMap m u : ℂ^m → ℂ^{m+1}`, `w ↦ (w, u)`, and its linear part `hyperplaneCLM`;
* `ohsawaTakegoshi_at_height`: the Ohsawa--Takegoshi interface moved from `z_last = 0` to
  the slice `z_last = u`, by translation;
* `lintegral_ball_normSq_ge`: the mean-value inequality
  `vol(B(ζ, δ)) |F(ζ)|² ≤ ∫_{B(ζ,δ)} |F|²` for holomorphic `F`, from the plurisubharmonicity
  of `|F|²`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

variable {m : ℕ}

/-! ### The slice map -/

/-- The linear embedding `w ↦ (w, 0)` of `ℂ^m` into `ℂ^{m+1}`. -/
def hyperplaneCLM (m : ℕ) : ComplexModel m →L[ℂ] ComplexModel (m + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := hyperplaneEmbedding m
      map_add' := fun w w' => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hyperplaneEmbedding]
      map_smul' := fun a w => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hyperplaneEmbedding] }

@[simp] theorem hyperplaneCLM_apply (w : ComplexModel m) :
    hyperplaneCLM m w = hyperplaneEmbedding m w := rfl

/-- The affine slice `w ↦ (w, u)` of `ℂ^{m+1}`. -/
def sliceMap (m : ℕ) (u : ℂ) (w : ComplexModel m) : ComplexModel (m + 1) :=
  hyperplaneEmbedding m w + EuclideanSpace.single (Fin.last m) u

@[simp] theorem sliceMap_last (u : ℂ) (w : ComplexModel m) :
    sliceMap m u w (Fin.last m) = u := by
  simp [sliceMap]

@[simp] theorem sliceMap_castSucc (u : ℂ) (w : ComplexModel m) (i : Fin m) :
    sliceMap m u w i.castSucc = w i := by
  simp [sliceMap, Fin.castSucc_ne_last]

theorem analyticAt_sliceMap (u : ℂ) (w : ComplexModel m) : AnalyticAt ℂ (sliceMap m u) w :=
  ((hyperplaneCLM m).analyticAt w).add analyticAt_const

theorem differentiable_sliceMap (u : ℂ) : Differentiable ℂ (sliceMap m u) :=
  fun w => (analyticAt_sliceMap u w).differentiableAt

theorem continuous_sliceMap (u : ℂ) : Continuous (sliceMap m u) :=
  (differentiable_sliceMap u).continuous

/-! ### Ohsawa--Takegoshi at an arbitrary height -/

/-- The Ohsawa--Takegoshi interface for the slice `z_last = u` instead of `z_last = 0`.
The constant depends only on the bound `R` for `|z_last - u|` on the domain. -/
theorem ohsawaTakegoshi_at_height (hOT : OhsawaTakegoshiHyperplane) (m : ℕ) {R : ℝ}
    (hR : 0 < R) : by
      letI : MeasurableSpace (ComplexModel m) := borel _
      letI : BorelSpace (ComplexModel m) := ⟨rfl⟩
      letI : MeasurableSpace (ComplexModel (m + 1)) := borel _
      letI : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
      exact ∃ C : ℝ, 0 < C ∧
        ∀ Ω : Set (ComplexModel (m + 1)), IsOpen Ω → Convex ℝ Ω → ∀ u : ℂ,
          (∀ z ∈ Ω, ‖z (Fin.last m) - u‖ < R) →
          ∀ φ : ComplexModel (m + 1) → EReal, PlurisubharmonicOn φ Ω →
            ∀ c : ℝ, 0 < c → ∀ f : ComplexModel m → ℂ,
              DifferentiableOn ℂ f (sliceMap m u ⁻¹' Ω) →
              ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F Ω ∧
                (∀ w ∈ sliceMap m u ⁻¹' Ω, F (sliceMap m u w) = f w) ∧
                (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
                  ENNReal.ofReal C *
                    ∫⁻ w in sliceMap m u ⁻¹' Ω,
                      multiplierDensity (fun w => φ (sliceMap m u w)) c f w := by
  let _ : MeasurableSpace (ComplexModel m) := borel _
  have _ : BorelSpace (ComplexModel m) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  obtain ⟨C, hC, hOTm⟩ := hOT m R hR
  refine ⟨C, hC, fun Ω hΩ hconv u hbd φ hφ c hc f hf => ?_⟩
  set a : ComplexModel (m + 1) := EuclideanSpace.single (Fin.last m) u with ha
  set Ω' : Set (ComplexModel (m + 1)) := (fun x => x + a) ⁻¹' Ω with hΩ'
  have hΩ'open : IsOpen Ω' := hΩ.preimage (continuous_id.add continuous_const)
  have hΩ'conv : Convex ℝ Ω' := by
    have := hconv.translate_preimage_right a
    simpa [hΩ', add_comm] using this
  have hbd' : ∀ z ∈ Ω', ‖z (Fin.last m)‖ < R := by
    intro z hz
    simpa [ha] using hbd _ hz
  have hφ' : PlurisubharmonicOn (fun x => φ (x + a)) Ω' :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hΩ'open
      ((differentiable_id.add_const a).differentiableOn) (fun x hx => hx) hφ
  have hpre : hyperplaneEmbedding m ⁻¹' Ω' = sliceMap m u ⁻¹' Ω := rfl
  obtain ⟨F', hF'hol, hF'ext, hF'int⟩ :=
    hOTm Ω' hΩ'open hΩ'conv hbd' (fun x => φ (x + a)) hφ' c hc f (by rwa [hpre])
  refine ⟨fun x => F' (x - a), ?_, ?_, ?_⟩
  · refine hF'hol.comp (differentiable_id.sub_const a).differentiableOn fun x hx => ?_
    simpa [hΩ'] using hx
  · intro w hw
    have := hF'ext w (by rwa [hpre])
    show F' (sliceMap m u w - a) = f w
    rw [sliceMap, add_sub_cancel_right]
    exact this
  · have hmp : MeasurePreserving (fun x : ComplexModel (m + 1) => x + a) volume volume :=
      measurePreserving_add_right volume a
    have htrans : (∫⁻ z in Ω, multiplierDensity φ c (fun x => F' (x - a)) z) =
        ∫⁻ x in Ω', multiplierDensity (fun x => φ (x + a)) c F' x := by
      rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight a)]
      simp only [multiplierDensity, add_sub_cancel_right]
      rfl
    rw [htrans]
    exact hF'int

/-! ### The mean-value inequality for `|F|²` -/

/-- For `F` holomorphic near the closed ball `B̄(ζ, δ)`,
`vol(B(ζ, δ)) |F(ζ)|² ≤ ∫_{B(ζ,δ)} |F|²`. -/
theorem lintegral_ball_normSq_ge {n : ℕ}
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    {U : Set (ComplexModel n)} (hU : IsOpen U) {F : ComplexModel n → ℂ}
    (hF : DifferentiableOn ℂ F U) {ζ : ComplexModel n} {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall ζ δ ⊆ U) :
    volume (ball ζ δ) * ENNReal.ofReal (‖F ζ‖ ^ 2) ≤
      ∫⁻ x in ball ζ δ, ENNReal.ofReal (‖F x‖ ^ 2) := by
  have hpsh : PlurisubharmonicOn (fun x => ((‖F x‖ ^ 2 : ℝ) : EReal)) U := by
    let G : ComplexModel n → ComplexModel 1 := fun x => WithLp.toLp 2 (fun _ => F x)
    have hG : DifferentiableOn ℂ G U := by
      have hL : Differentiable ℂ (fun a : Fin 1 → ℂ => (WithLp.toLp 2 a : ComplexModel 1)) :=
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 1 => ℂ)).symm.differentiable
      exact hL.comp_differentiableOn (differentiableOn_pi.mpr fun _ => hF)
    have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU hG (mapsTo_univ _ _)
      ((discPshOn_norm_sq (univ : Set (ComplexModel 1))).plurisubharmonicOn isOpen_univ)
    have hnorm : ∀ x, ‖G x‖ = ‖F x‖ := by
      intro x
      simp [G, EuclideanSpace.norm_eq]
    simpa [hnorm] using h
  have hsub := PSHD.real_ball_submean (u := fun x => ‖F x‖ ^ 2) hpsh.discPshOn volume ζ hδ hB
  have hcont : ContinuousOn (fun x => ‖F x‖ ^ 2) (closedBall ζ δ) :=
    ((hF.continuousOn.mono hB).norm).pow 2
  have hint : IntegrableOn (fun x => ‖F x‖ ^ 2) (ball ζ δ) volume :=
    (hcont.integrableOn_compact (isCompact_closedBall ζ δ)).mono_set ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)]
  have hfin : volume (ball ζ δ) ≠ ⊤ := measure_ball_lt_top.ne
  calc volume (ball ζ δ) * ENNReal.ofReal (‖F ζ‖ ^ 2)
      = ENNReal.ofReal ((volume (ball ζ δ)).toReal * ‖F ζ‖ ^ 2) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsub

end

end Hironaka
