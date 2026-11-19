import Hironaka.Analytic.HiepSliceLemma
import Hironaka.Analytic.GoodSliceSelection

set_option autoImplicit false

/-!
# Hiep's Lemma 2.1 for increasing sequences: the slice bound and the assembly

* `exists_index_lintegral_lt`: on a slice, strong openness in the lower dimension,
  compactness and monotone convergence give one index `j` whose weighted mass on a
  relatively compact set is below any bound exceeding the mass of the pointwise limit.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



/-- **The slice bound.**  Let `v_j` be an increasing, uniformly bounded above family of
plurisubharmonic functions on an open `W ⊆ ℂ^n`, and `h` analytic on `W` with finite
weighted mass for the pointwise limit.  If strong openness for increasing sequences holds
in dimension `n`, then for every relatively compact `B` with `B̄ ⊆ W` and every `M` above
the limit's weighted mass on `B`, some `v_j` already has weighted mass below `M` on `B`. -/
theorem exists_index_lintegral_lt {n : ℕ}
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (hIH : IncreasingStrongOpenness n)
    {W : Set (ComplexModel n)} (hW : IsOpen W) {v : ℕ → ComplexModel n → EReal}
    (hpsh : ∀ j, PlurisubharmonicOn (v j) W) (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    {C : ℝ} (hC : ∀ j, ∀ y ∈ W, v j y ≤ (C : EReal)) {c : ℝ} (hc : 0 < c)
    {h : ComplexModel n → ℂ} (han : ∀ y ∈ W, AnalyticAt ℂ h y)
    (hmass : (∫⁻ y in W, multiplierDensity (fun y => ⨆ j, v j y) c h y) ≠ ⊤)
    {B : Set (ComplexModel n)} (hBm : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBW : closure B ⊆ W) {M : ℝ≥0∞}
    (hM : (∫⁻ y in B, multiplierDensity (fun y => ⨆ j, v j y) c h y) < M) :
    ∃ j, (∫⁻ y in B, multiplierDensity (v j) c h y) < M := by
  obtain ⟨hinst⟩ := ‹BorelSpace (ComplexModel n)›
  subst hinst
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hdiff : DifferentiableOn ℂ h W := fun y hy =>
    (han y hy).differentiableAt.differentiableWithinAt
  have hqpsh : ∀ j, QuasiPlurisubharmonicOn (v j) W := fun j y hy =>
    (hpsh j y hy).quasiPlurisubharmonicAt
  have hdmeas : ∀ j, AEMeasurable (multiplierDensity (v j) c h) (volume.restrict W) := fun j =>
    aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW (hqpsh j) hc.ne'
      hdiff.continuousOn
  -- Densities decrease in `j` on `W`.
  have hanti : ∀ {i j : ℕ}, i ≤ j → ∀ y ∈ W,
      multiplierDensity (v j) c h y ≤ multiplierDensity (v i) c h y := by
    intro i j hij y hy
    unfold multiplierDensity
    gcongr
    exact multiplierWeight_antitone hc.le (hmono y hy hij)
  -- The regularized limit.
  have hbdd : LocallyUniformlyBoundedAbove (range v) W := fun x _ =>
    ⟨univ, univ_mem, C, by rintro _ ⟨j, rfl⟩ y ⟨_, hy⟩; exact hC j y hy⟩
  have hPpsh : PlurisubharmonicOn (uscRegularization (⨆ j, v j)) W := by
    have := plurisubharmonicOn_uscRegularization_sSup hW (range_nonempty v)
      (by rintro _ ⟨j, rfl⟩; exact hpsh j) hbdd
    rwa [sSup_range] at this
  have hsupfun : (fun y => ⨆ j, v j y) = ⨆ j, v j := funext fun y => (iSup_apply ..).symm
  -- Strong openness in dimension `n` at every point of `W`.
  have hloc : ∀ y ∈ W, ∃ j, MultiplierIntegrableAt (v j) c h y volume := by
    intro y hy
    refine hIH W v hW hpsh hmono hbdd y hy c hc h (han y hy) ⟨hc, W, hW, hy, hdiff, ?_, ?_⟩
    · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
        (fun x hx => (hPpsh x hx).quasiPlurisubharmonicAt) hc.ne' hdiff.continuousOn
    · refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hmass.lt_top
      unfold multiplierDensity
      gcongr
      refine multiplierWeight_antitone hc.le ?_
      rw [hsupfun]
      exact le_uscRegularization _ x
  choose! jy hjy using hloc
  have hopen : ∀ y ∈ closure B, ∃ U : Set (ComplexModel n), IsOpen U ∧ y ∈ U ∧ U ⊆ W ∧
      (∫⁻ x in U, multiplierDensity (v (jy y)) c h x) < ⊤ := by
    intro y hy
    obtain ⟨_, U, hU, hyU, _, _, hint⟩ := hjy y (hBW hy)
    exact ⟨U ∩ W, hU.inter hW, ⟨hyU, hBW hy⟩, inter_subset_right,
      (lintegral_mono_set inter_subset_left).trans_lt hint⟩
  choose! U hUopen hyU hUW hUint using hopen
  obtain ⟨t, ht, hcover⟩ := hBc.elim_nhds_subcover U
    (fun y hy => (hUopen y hy).mem_nhds (hyU y hy))
  set jstar := t.sup jy with hjstar
  have hfinite : (∫⁻ x in B, multiplierDensity (v jstar) c h x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ ((lintegral_mono_set (subset_closure.trans hcover)).trans
      (lintegral_biUnion_finset_le _ t U))
    refine ENNReal.sum_ne_top.mpr fun y hy => ne_top_of_le_ne_top (hUint y (ht y hy)).ne ?_
    refine setLIntegral_mono' (hUopen y (ht y hy)).measurableSet fun x hx => ?_
    exact hanti (Finset.le_sup hy) x (hUW y (ht y hy) hx)
  -- Monotone convergence along the tail.
  have hBsubW : B ⊆ W := subset_closure.trans hBW
  have hlim : Tendsto (fun k => ∫⁻ x in B, multiplierDensity (v (k + jstar)) c h x) atTop
      (𝓝 (∫⁻ x in B, multiplierDensity (fun y => ⨆ j, v j y) c h x)) := by
    refine tendsto_lintegral_of_dominated_convergence' (multiplierDensity (v jstar) c h)
      (fun k => (hdmeas _).mono_measure (Measure.restrict_mono hBsubW le_rfl)) ?_ hfinite ?_
    · intro k
      filter_upwards [ae_restrict_mem hBm] with x hx
      exact hanti (Nat.le_add_left _ _) x (hBsubW hx)
    · filter_upwards [ae_restrict_mem hBm] with x hx
      have hmx : Monotone fun k => v (k + jstar) x :=
        fun i j hij => hmono x (hBsubW hx) (Nat.add_le_add_right hij _)
      have hsup : (⨆ k, v (k + jstar) x) = ⨆ j, v j x :=
        (hmono x (hBsubW hx)).iSup_nat_add jstar
      have hconv : Tendsto (fun k => v (k + jstar) x) atTop (𝓝 (⨆ j, v j x)) :=
        hsup ▸ tendsto_atTop_iSup hmx
      unfold multiplierDensity
      exact ENNReal.Tendsto.const_mul
        ((continuous_multiplierWeight hc).tendsto _ |>.comp hconv) (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hM)).exists
  exact ⟨k + jstar, hk⟩

end

end Hironaka
