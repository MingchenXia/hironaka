import Hironaka.MarkedIdeal.GermIdealSliceClosure
import Hironaka.Analytic.OhsawaTakegoshiInterface
import Hironaka.Analytic.PotentialTheory.MultiplierIdeals

set_option autoImplicit false

/-!
# The dimension induction for strong openness of increasing sequences

This module proves `IncreasingStrongOpenness (m + 1)` from three inputs: the
Ohsawa--Takegoshi interface `OhsawaTakegoshiHyperplane`, the Krull interface
`GermKrullIntersection m`, and `IncreasingStrongOpenness m`.  It is the analytic half of
the route recorded in I-0114.

Fix `z`, `c` and an increasing family `v_j`.  The union over `j` of the multiplier germ
ideals `I(c v_j)_z` is an ideal of holomorphic germs, because the `v_j` increase
(`isHolomorphicGermIdeal_multiplierUnion`).  Hiep's Lemma 2.1 (`hiep14-weighted-lct:lem-2.1`)
produces, for every `ε > 0`, a slice `z_last = z_last + t` with `0 < |t| < ε` and an element
`F` of that ideal extending `f` from the slice with `|t| |F| ≤ K ε` on a fixed torus.
`germIdeal_mem_of_slice_extensions` then puts `f` in the ideal.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



variable {m : ℕ}

/-- A germ complex differentiable near `x` is bounded on a smaller neighbourhood, so its
product with a weighted-L² holomorphic germ is again weighted L².  This is
`multiplierIntegrableAt_holomorphic_mul` with differentiability near `x` in place of
analyticity at `x`, and without the quasi-plurisubharmonicity of the weight. -/
theorem multiplierIntegrableAt_differentiable_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
    {φ : E → EReal} {c : ℝ} {f g : E → ℂ} {x : E}
    (hf : MultiplierIntegrableAt φ c f x μ) (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y) :
    MultiplierIntegrableAt φ c (fun y => g y * f y) x μ := by
  obtain ⟨hc, U, hU, hxU, hfhol, hfint⟩ := hf
  have hgbound : ∀ᶠ y in 𝓝 x, ‖g y‖ ≤ ‖g x‖ + 1 := by
    have hnorm : Tendsto (fun y => ‖g y‖) (𝓝 x) (𝓝 ‖g x‖) :=
      hg.self_of_nhds.continuousAt.norm
    exact (hnorm.eventually_lt tendsto_const_nhds (by linarith)).mono fun _ hy => hy.le
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (hg.and hgbound)
  set W := U ∩ V with hWdef
  have hW : IsOpen W := hU.inter hV
  have hgW : DifferentiableOn ℂ g W := fun y hy => (hVsub hy.2).1.differentiableWithinAt
  have hhol : DifferentiableOn ℂ (fun y => g y * f y) W :=
    hgW.mul (hfhol.mono inter_subset_left)
  have hfW := hfint.mono (inter_subset_left : W ⊆ U)
  have hdens : ∀ y, multiplierDensity φ c (fun z => g z * f z) y =
      ENNReal.ofReal (‖g y‖ ^ 2) * multiplierDensity φ c f y := by
    intro y
    unfold multiplierDensity
    rw [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
  refine ⟨hc, W, hW, ⟨hxU, hxV⟩, hhol, ?_, ?_⟩
  · have hgm : AEMeasurable (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) (μ.restrict W) :=
      (ENNReal.continuous_ofReal.comp_continuousOn
        ((hgW.continuousOn.norm).pow 2)).aemeasurable hW.measurableSet
    have hfun : multiplierDensity φ c (fun z => g z * f z) =
        fun y => ENNReal.ofReal (‖g y‖ ^ 2) * multiplierDensity φ c f y := funext hdens
    rw [hfun]
    exact hgm.mul hfW.1
  · set K : ℝ≥0∞ := ENNReal.ofReal ((‖g x‖ + 1) ^ 2) with hK
    calc
      (∫⁻ y in W, multiplierDensity φ c (fun z => g z * f z) y ∂μ) ≤
          ∫⁻ y in W, K * multiplierDensity φ c f y ∂μ := by
        refine setLIntegral_mono_ae' hW.measurableSet
          (Filter.Eventually.of_forall fun y hy => ?_)
        rw [hdens]
        gcongr
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hVsub hy.2).2 2)
      _ = K * ∫⁻ y in W, multiplierDensity φ c f y ∂μ := by
        rw [lintegral_const_mul' K _ (by simp [K])]
      _ < ⊤ := ENNReal.mul_lt_top (by simp [K]) hfW.2

/-- The union of the multiplier germ ideals of an increasing family of plurisubharmonic
functions is an ideal of holomorphic germs. -/
theorem isHolomorphicGermIdeal_multiplierUnion
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    (μ : Measure (ComplexModel (m + 1)))
    {W : Set (ComplexModel (m + 1))} (hW : IsOpen W) {v : ℕ → ComplexModel (m + 1) → EReal}
    (hpsh : ∀ j, PlurisubharmonicOn (v j) W) (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    {z : ComplexModel (m + 1)} (hz : z ∈ W) {c : ℝ} (hc : 0 < c) :
    IsHolomorphicGermIdeal z (fun h => ∃ j, MultiplierIntegrableAt (v j) c h z μ) := by
  have hqpsh : ∀ j, QuasiPlurisubharmonicAt (v j) z := fun j =>
    (hpsh j z hz).quasiPlurisubharmonicAt
  have hlift : ∀ {j j' : ℕ} {h : ComplexModel (m + 1) → ℂ}, j ≤ j' →
      MultiplierIntegrableAt (v j) c h z μ → MultiplierIntegrableAt (v j') c h z μ := by
    intro j j' h hjj' hh
    refine multiplierIntegrableAt_of_moreSingularAt (hqpsh j') ⟨0, ?_⟩ hh
    filter_upwards [hW.mem_nhds hz] with y hy
    simpa using hmono y hy hjj'
  refine ⟨⟨0, multiplierIntegrableAt_zero (v 0) hc z μ⟩, ?_, ?_, ?_, ?_⟩
  · rintro h₁ h₂ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩
    exact ⟨max j₁ j₂, multiplierIntegrableAt_add (hqpsh _) (hlift (le_max_left _ _) hj₁)
      (hlift (le_max_right _ _) hj₂)⟩
  · rintro a h ha ⟨j, hj⟩
    exact ⟨j, multiplierIntegrableAt_differentiable_mul hj ha⟩
  · rintro h ⟨j, _, U, hU, hzU, hhol, _⟩
    exact ⟨U, hU, hzU, hhol⟩
  · rintro h h' ⟨j, hj⟩ hh'
    exact ⟨j, hj.congr EventuallyEq.rfl hh'.symm⟩

/-- **Hiep's Lemma 2.1 for increasing sequences**, in the form the algebraic half consumes.
There is a polydisc `Δ(z, s')` on which `f` is holomorphic, a torus radius `s < s'` and a
constant `K` with the following property.  For every `ε > 0` there is a slice height `t`
with `0 < |t| < min(ε, s/2)` and some `F` in `⋃_j I(c v_j)_z`, holomorphic on `Δ(z, s')`, which
agrees with `f` on `z_last = z_last + t` and satisfies `|t| |F| ≤ K ε` on the torus. -/
def SliceExtensionProperty (m : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel (m + 1)) := borel _
  letI : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  exact ∀ (W : Set (ComplexModel (m + 1))) (v : ℕ → ComplexModel (m + 1) → EReal),
    IsOpen W → (∀ j, PlurisubharmonicOn (v j) W) →
    (∀ y ∈ W, Monotone fun j => v j y) →
    LocallyUniformlyBoundedAbove (range v) W →
    ∀ z ∈ W, ∀ c : ℝ, 0 < c → ∀ f : ComplexModel (m + 1) → ℂ, AnalyticAt ℂ f z →
      MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c f z volume →
      ∃ s s' K : ℝ, 0 < s ∧ s < s' ∧ DifferentiableOn ℂ f (openPolydisc z s') ∧
        ∀ ε : ℝ, 0 < ε → ∃ t : ℂ, t ≠ 0 ∧ ‖t‖ < ε ∧ ‖t‖ < s / 2 ∧
          ∃ F : ComplexModel (m + 1) → ℂ,
            (∃ j, MultiplierIntegrableAt (v j) c F z volume) ∧
            DifferentiableOn ℂ F (openPolydisc z s') ∧
            (∀ x ∈ openPolydisc z s', x (Fin.last m) = z (Fin.last m) + t → F x = f x) ∧
            ∀ θ, ‖t‖ * ‖F (torusPoint z s θ)‖ ≤ K * ε

/-- **The induction step.**  Slice extensions and Krull's intersection theorem in dimension
`m + 1` give strong openness for increasing sequences in dimension `m + 1`. -/
theorem increasingStrongOpenness_succ_of_sliceExtensions (hK : GermKrullIntersection m)
    (hS : SliceExtensionProperty m) : IncreasingStrongOpenness (m + 1) := by
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  intro W v hW hpsh hmono hbdd z hz c hc f hf hmem
  obtain ⟨s, s', K, hs, hss', hfhol, hdata⟩ := hS W v hW hpsh hmono hbdd z hz c hc f hf hmem
  choose t ht0 htε hts F hFJ hFhol hslice hbound using
    fun k : ℕ => hdata (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htlim : Tendsto t atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) (fun k => (htε k).le) hinv)
  exact germIdeal_mem_of_slice_extensions hK
    (isHolomorphicGermIdeal_multiplierUnion volume hW hpsh hmono hz hc) hs hss' hfhol
    t ht0 hts htlim F hFJ hFhol hslice (fun k => K * (1 / ((k : ℝ) + 1)))
    (by simpa using hinv.const_mul K) hbound

/-- **Strong openness for increasing sequences in every dimension**, from slice extensions
and Krull's intersection theorem in every dimension.  The base case `n = 0` is
`hiepLocalUniformBound_zero`. -/
theorem increasingStrongOpenness_of_sliceExtensions (hK : ∀ m, GermKrullIntersection m)
    (hS : ∀ m, IncreasingStrongOpenness m → SliceExtensionProperty m) :
    ∀ n, IncreasingStrongOpenness n := by
  intro n
  induction n with
  | zero => exact increasingStrongOpenness_of_hiepLocalUniformBound 0 hiepLocalUniformBound_zero
  | succ m ih => exact increasingStrongOpenness_succ_of_sliceExtensions (hK m) (hS m ih)

end

end Hironaka
