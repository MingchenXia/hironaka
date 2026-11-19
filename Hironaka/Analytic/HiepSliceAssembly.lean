import Hironaka.Analytic.HiepSliceBounds
import Hironaka.Analytic.HiepSliceGeometry

set_option autoImplicit false

/-!
# Hiep's Lemma 2.1 for increasing sequences: assembly

`sliceExtensionProperty_of_ohsawaTakegoshi` proves `SliceExtensionProperty m` from two
hypotheses: the Ohsawa--Takegoshi interface and `IncreasingStrongOpenness m`.  Together
with `increasingStrongOpenness_of_sliceExtensions` this gives strong openness for increasing
sequences in every dimension.  The only remaining inputs are Ohsawa--Takegoshi and Krull's
intersection theorem for germ ideals.

Fix a ball `B(z, r)` on which the family is bounded by `C`, `f` is analytic and the weighted
mass is finite, and a polydisc `Δ(z, ρ)` inside it.  For `ε > 0`:

1. choose a slice height `t`, `0 < |t| < ε`, with `|t|² ∫_{slice} |f|² e^{-cV} ≤ ε²`
   (`exists_good_slice` in slice coordinates, `aemeasurable_lintegral_sliceMap_prod`);
2. choose `j₀` with `∫_{Δ'(ρ/2)} |f|² e^{-c v_{j₀}} < 2ε²/|t|²` on the slice
   (`exists_index_lintegral_lt`);
3. extend by Ohsawa--Takegoshi to `F` on `Δ(z, ρ/2)` with
   `∫ |F|² e^{-c v_{j₀}} ≤ C_OT · 2ε²/|t|²`;
4. on the torus of radius `ρ/8`, the mean-value inequality over balls of radius `ρ/8` gives
   `|t| |F| ≤ K ε` with `K² = 2 e^{cC} C_OT / vol(B(0, ρ/8))`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

/-- The core of Lemma 2.1: from localized data to slice extensions. -/
theorem sliceExtensions_of_local_data (hOT : OhsawaTakegoshiHyperplane) {m : ℕ}
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    (hIH : IncreasingStrongOpenness m)
    {W : Set (ComplexModel (m + 1))} {v : ℕ → ComplexModel (m + 1) → EReal}
    (hpsh : ∀ j, PlurisubharmonicOn (v j) W) (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    {z : ComplexModel (m + 1)} {c : ℝ} (hc : 0 < c) {f : ComplexModel (m + 1) → ℂ}
    {ρ C : ℝ} (hρ : 0 < ρ) (hρW : polydiscN z ρ ⊆ W)
    (hC : ∀ j, ∀ y ∈ polydiscN z ρ, v j y ≤ (C : EReal))
    (han : ∀ y ∈ polydiscN z ρ, AnalyticAt ℂ f y)
    (hmeas : AEMeasurable (multiplierDensity (fun y => ⨆ j, v j y) c f)
      (volume.restrict (polydiscN z ρ)))
    (hmass : ∫⁻ x in polydiscN z ρ, multiplierDensity (fun y => ⨆ j, v j y) c f x ≠ ⊤) :
    ∃ s s' K : ℝ, 0 < s ∧ s < s' ∧ DifferentiableOn ℂ f (openPolydisc z s') ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : ℂ, t ≠ 0 ∧ ‖t‖ < ε ∧ ‖t‖ < s / 2 ∧
        ∃ F : ComplexModel (m + 1) → ℂ,
          (∃ j, MultiplierIntegrableAt (v j) c F z volume) ∧
          DifferentiableOn ℂ F (openPolydisc z s') ∧
          (∀ x ∈ openPolydisc z s', x (Fin.last m) = z (Fin.last m) + t → F x = f x) ∧
          ∀ θ, ‖t‖ * ‖F (torusPoint z s θ)‖ ≤ K * ε := by
  obtain ⟨hinst₁⟩ := ‹BorelSpace (ComplexModel (m + 1))›
  obtain ⟨hinst₀⟩ := ‹BorelSpace (ComplexModel m)›
  subst hinst₁ hinst₀
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel m) := borel _
  have _ : BorelSpace (ComplexModel m) := ⟨rfl⟩
  set ρ' : ℝ := ρ / 2 with hρ'
  set s : ℝ := ρ' / 4 with hs
  set δ : ℝ := ρ' / 4 with hδ
  have hρ'pos : 0 < ρ' := by positivity
  have hspos : 0 < s := by positivity
  have hδpos : 0 < δ := by positivity
  obtain ⟨COT, hCOT, hOTh⟩ := ohsawaTakegoshi_at_height hOT m (R := 2 * ρ') (by positivity)
  set V0 : ℝ≥0∞ := volume (ball (0 : ComplexModel (m + 1)) δ) with hV0
  have hV0pos : V0 ≠ 0 := (measure_ball_pos volume _ hδpos).ne'
  have hV0top : V0 ≠ ⊤ := measure_ball_lt_top.ne
  set K : ℝ := Real.sqrt (2 * Real.exp (c * C) * COT / V0.toReal) with hK
  have hfdiff : DifferentiableOn ℂ f (polydiscN z ρ) := fun y hy =>
    (han y hy).differentiableAt.differentiableWithinAt
  refine ⟨s, ρ' / 2, K, hspos, by rw [hs]; linarith,
    hfdiff.mono fun x hx i => (hx i).trans (by linarith), fun ε hε => ?_⟩
  -- Step 1: the slice.
  set ε' : ℝ := min ε (s / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  set zl : ℂ := z (Fin.last m) with hzl
  set z' : ComplexModel m := initCoords z with hz'
  set G : ComplexModel (m + 1) → ℝ≥0∞ := multiplierDensity (fun y => ⨆ j, v j y) c f with hG
  obtain ⟨hgmeas, hgfin⟩ := aemeasurable_lintegral_sliceMap_prod z ρ hmeas hmass
  obtain ⟨t, ht0, htε', htρ, hslice⟩ := exists_good_slice (μ := volume) (B := polydiscN z' ρ)
    (a := zl) hρ hgmeas hgfin hε'pos
  set u : ℂ := zl + t with hu
  have htε : ‖t‖ < ε := htε'.trans_le (min_le_left _ _)
  have hts : ‖t‖ < s / 2 := htε'.trans_le (min_le_right _ _)
  have htρ' : ‖t‖ < ρ' := hts.trans (by rw [hs]; linarith)
  have hut : u - zl = t := by rw [hu]; ring
  have huρ : ‖u - zl‖ < ρ := by rw [hut]; exact htρ
  have huρ' : ‖u - zl‖ < ρ' := by rw [hut]; exact htρ'
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  -- Step 2: the slice bound.
  set Ws : Set (ComplexModel m) := polydiscN z' ρ with hWs
  have hpreρ : sliceMap m u ⁻¹' polydiscN z ρ = Ws := sliceMap_preimage_polydiscN z huρ
  have hmaps : MapsTo (sliceMap m u) Ws (polydiscN z ρ) := fun w hw => by
    rw [← hpreρ] at hw; exact hw
  have hpshs : ∀ j, PlurisubharmonicOn (fun w => v j (sliceMap m u w)) Ws := fun j =>
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (isOpen_polydiscN _ _)
      (differentiable_sliceMap u).differentiableOn (hmaps.mono_right hρW) (hpsh j)
  have hmonos : ∀ w ∈ Ws, Monotone fun j => v j (sliceMap m u w) := fun w hw =>
    hmono _ (hρW (hmaps hw))
  have hCs : ∀ j, ∀ w ∈ Ws, v j (sliceMap m u w) ≤ (C : EReal) := fun j w hw =>
    hC j _ (hmaps hw)
  have hans : ∀ w ∈ Ws, AnalyticAt ℂ (fun w => f (sliceMap m u w)) w := fun w hw =>
    (han _ (hmaps hw)).comp (analyticAt_sliceMap u w)
  set Φ : ℝ≥0∞ := ∫⁻ w in Ws, G (sliceMap m u w) with hΦ
  have hΦle : Φ ≤ ENNReal.ofReal (ε' ^ 2 / ‖t‖ ^ 2) := by
    have ht2 : 0 < ‖t‖ ^ 2 := by positivity
    rw [ENNReal.ofReal_div_of_pos ht2, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr ht2).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hslice
  have hmass_s : (∫⁻ w in Ws, multiplierDensity (fun w => ⨆ j, v j (sliceMap m u w)) c
      (fun w => f (sliceMap m u w)) w) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΦle
  set B' : Set (ComplexModel m) := polydiscN z' ρ' with hB'
  have hB'cl : closure B' ⊆ closedPolydiscN z' ρ' := closure_polydiscN_subset _ _
  have hB'c : IsCompact (closure B') :=
    (isCompact_closedPolydiscN z' hρ'pos.le).of_isClosed_subset isClosed_closure hB'cl
  have hB'W : closure B' ⊆ Ws :=
    hB'cl.trans (closedPolydiscN_subset_polydiscN z' (by rw [hρ']; linarith))
  set M : ℝ≥0∞ := ENNReal.ofReal (2 * ε' ^ 2 / ‖t‖ ^ 2) with hM
  have hMlt : (∫⁻ w in B', multiplierDensity (fun w => ⨆ j, v j (sliceMap m u w)) c
      (fun w => f (sliceMap m u w)) w) < M := by
    refine lt_of_le_of_lt ((lintegral_mono_set (subset_closure.trans hB'W)).trans hΦle) ?_
    rw [hM, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have : 0 < ε' ^ 2 / ‖t‖ ^ 2 := by positivity
    linarith [show 2 * ε' ^ 2 / ‖t‖ ^ 2 = 2 * (ε' ^ 2 / ‖t‖ ^ 2) by ring]
  obtain ⟨j₀, hj₀⟩ := exists_index_lintegral_lt hIH (isOpen_polydiscN _ _) hpshs hmonos hCs hc
    hans hmass_s (isOpen_polydiscN _ _).measurableSet hB'c hB'W hMlt
  -- Step 3: Ohsawa--Takegoshi.
  set Ω : Set (ComplexModel (m + 1)) := polydiscN z ρ' with hΩ
  have hΩρ : Ω ⊆ polydiscN z ρ := fun x hx i => (hx i).trans (by rw [hρ']; linarith)
  have hpreΩ : sliceMap m u ⁻¹' Ω = B' := sliceMap_preimage_polydiscN z huρ'
  have hbdΩ : ∀ x ∈ Ω, ‖x (Fin.last m) - u‖ < 2 * ρ' := by
    intro x hx
    have h1 := hx (Fin.last m)
    calc ‖x (Fin.last m) - u‖ = ‖(x (Fin.last m) - zl) - t‖ := by rw [hu]; ring_nf
      _ ≤ ‖x (Fin.last m) - zl‖ + ‖t‖ := norm_sub_le _ _
      _ < ρ' + ρ' := add_lt_add h1 htρ'
      _ = 2 * ρ' := by ring
  obtain ⟨F, hFdiff, hFext, hFint⟩ := hOTh Ω (isOpen_polydiscN _ _) (convex_polydiscN _ _) u
    hbdΩ (v j₀) ((hpsh j₀).mono (hΩρ.trans hρW)) c hc (fun w => f (sliceMap m u w))
    (by rw [hpreΩ]; exact fun w hw =>
      (hans w (subset_closure.trans hB'W hw)).differentiableAt.differentiableWithinAt)
  rw [hpreΩ] at hFext hFint
  have hFint' : (∫⁻ x in Ω, multiplierDensity (v j₀) c F x) ≤ ENNReal.ofReal COT * M :=
    hFint.trans (by gcongr)
  have hFfin : (∫⁻ x in Ω, multiplierDensity (v j₀) c F x) < ⊤ :=
    hFint'.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hzΩ : z ∈ Ω := fun i => by simpa using hρ'pos
  refine ⟨t, ht0, htε, hts, F, ⟨j₀, hc, Ω, isOpen_polydiscN _ _, hzΩ, hFdiff, ?_, hFfin⟩,
    hFdiff.mono fun x hx i => (hx i).trans (by linarith), ?_, ?_⟩
  · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      (isOpen_polydiscN _ _)
      (fun x hx => ((hpsh j₀) x (hρW (hΩρ hx))).quasiPlurisubharmonicAt) hc.ne'
      hFdiff.continuousOn
  · -- Agreement on the slice.
    intro x hx hxl
    have hxΩ : x ∈ Ω := fun i => (hx i).trans (by linarith)
    have hxu : x (Fin.last m) = u := hxl
    have hx' : sliceMap m u (initCoords x) = x := by
      rw [← hxu]; exact sliceMap_initCoords x
    have hw : initCoords x ∈ B' := by
      rw [← hpreΩ, mem_preimage, hx']; exact hxΩ
    have := hFext (initCoords x) hw
    rwa [hx'] at this
  · -- The torus bound.
    intro θ
    set ζ := torusPoint z s θ with hζ
    have hζcl : ζ ∈ closedPolydiscN z s := fun i => (norm_torusPoint_sub z hspos.le θ i).le
    have hBΩ : closedBall ζ δ ⊆ Ω :=
      (closedBall_subset_closedPolydiscN hζcl).trans
        (closedPolydiscN_subset_polydiscN z (by rw [hs, hδ]; linarith))
    have hmv := lintegral_ball_normSq_ge (isOpen_polydiscN z ρ') hFdiff hδpos hBΩ
    have hpt : ∀ x ∈ Ω, ENNReal.ofReal (‖F x‖ ^ 2) ≤
        ENNReal.ofReal (Real.exp (c * C)) * multiplierDensity (v j₀) c F x := fun x hx =>
      le_ofReal_exp_mul_multiplierWeight hc.le (hC j₀ x (hΩρ hx)) _
    have hchain : V0 * ENNReal.ofReal (‖F ζ‖ ^ 2) ≤
        ENNReal.ofReal (Real.exp (c * C) * COT * (2 * ε' ^ 2 / ‖t‖ ^ 2)) := by
      calc V0 * ENNReal.ofReal (‖F ζ‖ ^ 2)
          = volume (ball ζ δ) * ENNReal.ofReal (‖F ζ‖ ^ 2) := by
            rw [hV0, Measure.addHaar_ball_center volume ζ δ]
        _ ≤ ∫⁻ x in ball ζ δ, ENNReal.ofReal (‖F x‖ ^ 2) := hmv
        _ ≤ ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (c * C)) *
              multiplierDensity (v j₀) c F x := by
            refine (lintegral_mono_set (ball_subset_closedBall.trans hBΩ)).trans ?_
            exact setLIntegral_mono' (isOpen_polydiscN _ _).measurableSet hpt
        _ = ENNReal.ofReal (Real.exp (c * C)) *
              ∫⁻ x in Ω, multiplierDensity (v j₀) c F x :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (Real.exp (c * C)) * (ENNReal.ofReal COT * M) := by gcongr
        _ = _ := by
            rw [hM, ← ENNReal.ofReal_mul hCOT.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              mul_assoc]
    have hV0r : 0 < V0.toReal := ENNReal.toReal_pos hV0pos hV0top
    have hreal : V0.toReal * ‖F ζ‖ ^ 2 ≤
        Real.exp (c * C) * COT * (2 * ε' ^ 2 / ‖t‖ ^ 2) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)] at h
    have hsq : (‖t‖ * ‖F ζ‖) ^ 2 ≤ (K * ε') ^ 2 := by
      have hK2 : K ^ 2 = 2 * Real.exp (c * C) * COT / V0.toReal := by
        rw [hK, Real.sq_sqrt (by positivity)]
      rw [mul_pow, mul_pow, hK2]
      have ht2 : 0 < ‖t‖ ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hV0r]
      calc ‖t‖ ^ 2 * ‖F ζ‖ ^ 2 * V0.toReal = ‖t‖ ^ 2 * (V0.toReal * ‖F ζ‖ ^ 2) := by ring
        _ ≤ ‖t‖ ^ 2 * (Real.exp (c * C) * COT * (2 * ε' ^ 2 / ‖t‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hreal ht2.le
        _ = 2 * Real.exp (c * C) * COT * ε' ^ 2 := by field_simp
    have hKnn : 0 ≤ K := Real.sqrt_nonneg _
    have hle : ‖t‖ * ‖F ζ‖ ≤ K * ε' :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    exact hle.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hKnn)

/-- **Hiep's Lemma 2.1 for increasing sequences.**  The Ohsawa--Takegoshi interface and
strong openness in dimension `m` give slice extensions in dimension `m + 1`. -/
theorem sliceExtensionProperty_of_ohsawaTakegoshi (hOT : OhsawaTakegoshiHyperplane) {m : ℕ}
    (hIH : IncreasingStrongOpenness m) : SliceExtensionProperty m := by
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel m) := borel _
  have _ : BorelSpace (ComplexModel m) := ⟨rfl⟩
  intro W v hW hpsh hmono hbdd z hz c hc f hf hmem
  obtain ⟨_, U, hU, hzU, _, hL2⟩ := hmem
  obtain ⟨U₀, hU₀, C, hC⟩ := hbdd z hz
  rw [hW.nhdsWithin_eq hz] at hU₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem (inter_mem (hU.mem_nhds hzU) hU₀) (hW.mem_nhds hz))
      hf.eventually_analyticAt)
  have hballW : ball z r ⊆ W := fun y hy => (hball hy).1.2
  have hballU : ball z r ⊆ U := fun y hy => (hball hy).1.1.1
  have hCb : ∀ j, ∀ y ∈ ball z r, v j y ≤ (C : EReal) := fun j y hy =>
    hC (v j) ⟨j, rfl⟩ y ⟨(hball hy).1.1.2, (hball hy).1.2⟩
  -- A polydisc inside the half ball.
  set ρ : ℝ := r / (2 * (Real.sqrt ((m + 1 : ℕ) : ℝ) + 1)) with hρ
  have hsq : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hρpos : 0 < ρ := by positivity
  have hpoly : polydiscN z ρ ⊆ ball z (r / 2) := by
    refine polydiscN_subset_ball z hρpos.le ?_
    rw [hρ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpolyr : polydiscN z ρ ⊆ ball z r := hpoly.trans (ball_subset_ball (by linarith))
  -- The pointwise limit agrees with its regularization a.e. on the half ball.
  have hae := ae_uscRegularization_iSup_eq_on_ball
    (fun j => ((hpsh j).mono hballW).discPshOn) (fun y hy => hmono y (hballW hy)) volume z hr
    subset_rfl hCb
  have hsupfun : (fun y => ⨆ j, v j y) = ⨆ j, v j := funext fun y => (iSup_apply ..).symm
  have hweight : multiplierDensity (uscRegularization (⨆ j, v j)) c f
      =ᵐ[volume.restrict (polydiscN z ρ)] multiplierDensity (fun y => ⨆ j, v j y) c f := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (isOpen_polydiscN z ρ).measurableSet]
      with x hx hxm
    simp only [multiplierDensity]
    rw [← hsupfun, hx (hpoly hxm)]
  obtain ⟨hmeasU, hintU⟩ := hL2.mono (hpolyr.trans hballU)
  refine sliceExtensions_of_local_data hOT hIH hpsh hmono hc hρpos (hpolyr.trans hballW)
    (fun j y hy => hCb j y (hpolyr hy)) (fun y hy => (hball (hpolyr hy)).2)
    (hmeasU.congr hweight) ?_
  rw [← lintegral_congr_ae hweight]
  exact hintU.ne

/-- **Strong openness for increasing sequences, in every dimension, from the
Ohsawa--Takegoshi extension theorem and Krull's intersection theorem for germ ideals.**
The first is a stated interface (`OhsawaTakegoshiHyperplane`); the second is proved as
`germKrullIntersection` (`Hironaka.StrongOpennessFromOhsawaTakegoshi`). -/
theorem increasingStrongOpenness_of_ohsawaTakegoshi_krull (hOT : OhsawaTakegoshiHyperplane)
    (hK : ∀ m, GermKrullIntersection m) : ∀ n, IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_sliceExtensions hK
    fun _ hIH => sliceExtensionProperty_of_ohsawaTakegoshi hOT hIH

end

end Hironaka
