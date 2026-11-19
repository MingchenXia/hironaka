import Hironaka.Analytic.StrongOpennessLocalization
import Hironaka.Analytic.QuasiEquisingularBasics
import Hironaka.Analytic.SubgeodesicChord

set_option autoImplicit false

/-!
# Strong openness for increasing sequences from Hiep's strong effective openness

`IncreasingStrongOpenness n` (Xia, Theorem 1.4.4, `xia-sgpt:page-0043`) is cited
there to Guan--Zhou and to Hiep.  Neither source states the increasing-sequence
form.  Its original is Hiep's *strong effective openness*, part (ii) of the Main
theorem of P. H. Hiep, *The weighted log canonical threshold*, C. R. Acad. Sci.
Paris 352 (2014) 283--288 (`hiep14-weighted-lct:main-theorem-ii`):

> Let `f` be holomorphic on an open set `Ω ⊆ ℂⁿ` and `φ ∈ PSH(Ω)`.  Assume
> `∫_{Ω'} |f|² e^{-2cφ} < ∞` on some open `Ω' ⊆ Ω`.  When `ψ ∈ PSH(Ω')` converges
> to `φ` in `L¹(Ω')` with `ψ ≤ φ`, the function `|f|² e^{-2cψ}` converges to
> `|f|² e^{-2cφ}` in `L¹` on every relatively compact open `Ω'' ⋐ Ω'`.

`HiepStrongEffectiveOpenness n` states it for sequences, as Hiep's proof does
("since the `L¹` topology is metrizable, it is enough to work with a sequence"),
with `Ω = Ω'`.  Hiep's weight `e^{-2cφ}` is this project's
`multiplierWeight c φ = exp (-c φ)` at exponent `2c`; the statement quantifies over
every `c > 0`, so nothing is lost.  Because `ψ ≤ φ`, the `L¹` distance is the
honest extended-real integral `∫ (φ - ψ)⁺`, and the `L¹` difference of the weighted
densities is their truncated `ℝ≥0∞` difference; neither passes through `toReal`,
which would silently identify a pole with `0`.

This module does **not** prove `HiepStrongEffectiveOpenness`.  It proves, sorry-free,
`increasingStrongOpenness_of_hiep : HiepStrongEffectiveOpenness n →
IncreasingStrongOpenness n`.  The derivation is not written in either source; it is:

1. localize to a ball carrying one real upper bound for the family
   (`increasingStrongOpenness_of_ball`);
2. if every member is `⊥` near the centre, the regularized limit is `⊥` a.e. there,
   so finite weighted mass forces `f ≡ 0` near the centre and the conclusion is
   trivial;
3. otherwise some member `v j₀` is finite at a point `a` close to the centre.  On a
   ball around `a` the regularized limit `P` agrees a.e. with the pointwise limit
   (`ae_uscRegularization_iSup_eq_on_ball`), so `(P - v (j + j₀))⁺ ↓ 0` a.e.; it is
   dominated by the deficit `(C - v j₀)⁺`, whose integral over a ball centred at the
   non-pole `a` is finite by the ball submean inequality (`DiscPshOn.ball_deficit_le`).
   Dominated convergence gives `v (j + j₀) → P` in `L¹`, with `v (j + j₀) ≤ P`;
4. Hiep's theorem then makes `∫ |f|² (e^{-c v_j} - e^{-c P})` finite for large `j` on a
   small ball around the centre, hence `∫ |f|² e^{-c v_j}` finite there.

No finite generation of multiplier ideals is needed: `IncreasingStrongOpenness` is
a statement about one germ `f` at a time.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

/-- **Hiep's strong effective openness** (Main theorem (ii) of Hiep 2014,
`hiep14-weighted-lct:main-theorem-ii`), for sequences and with `Ω = Ω'`.

This is an interface: it is a published theorem, not a theorem of this
workspace.  Hiep proves it by induction on `n` together with part (i), from the
Ohsawa--Takegoshi `L²` extension theorem, Hironaka's division theorem and
Galligo's division estimate. -/
def HiepStrongEffectiveOpenness (n : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (Ω' : Set (ComplexModel n)) (φ : ComplexModel n → EReal)
      (f : ComplexModel n → ℂ) (c : ℝ),
    IsOpen Ω' → PlurisubharmonicOn φ Ω' → DifferentiableOn ℂ f Ω' → 0 < c →
    (∫⁻ x in Ω', multiplierDensity φ c f x) < ⊤ →
    ∀ ψ : ℕ → ComplexModel n → EReal, (∀ j, PlurisubharmonicOn (ψ j) Ω') →
      (∀ j, ∀ x ∈ Ω', ψ j x ≤ φ x) →
      Tendsto (fun j => ∫⁻ x in Ω', (φ x - ψ j x).toENNReal) atTop (𝓝 0) →
      ∀ Ω'' : Set (ComplexModel n), IsOpen Ω'' → IsCompact (closure Ω'') →
        closure Ω'' ⊆ Ω' →
        Tendsto (fun j => ∫⁻ x in Ω'',
          (multiplierDensity (ψ j) c f x - multiplierDensity φ c f x)) atTop (𝓝 0)

/-- Hiep's strong effective openness implies the ball form of strong openness for
increasing sequences. -/
theorem ballIncreasingStrongOpenness_of_hiep (n : ℕ)
    (hH : HiepStrongEffectiveOpenness n) : BallIncreasingStrongOpenness n := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro z r v C hr hpsh hmono hbound c hc f hf hL2
  set P : ComplexModel n → EReal := uscRegularization (⨆ j, v j) with hP
  have hPfun : (fun y => ⨆ j, v j y) = ⨆ j, v j := funext fun y => (iSup_apply ..).symm
  have hr16 : 0 < r / 16 := by positivity
  set V : Set (ComplexModel n) := ball z (r / 16) with hVdef
  have hVB : V ⊆ ball z r := ball_subset_ball (by linarith)
  by_cases hex : ∃ j, ∃ a ∈ V, v j a ≠ ⊥
  · obtain ⟨j₀, a, ha, hva⟩ := hex
    have haz : dist a z < r / 16 := ha
    set w : ℕ → ComplexModel n → EReal := fun j => v (j + j₀) with hw
    set Ω' : Set (ComplexModel n) := ball a (3 * r / 8) with hΩ'def
    have hSB : ball a (3 * r / 4) ⊆ ball z r := ball_subset_ball' (by linarith)
    have hΩ'B : Ω' ⊆ ball z r := (ball_subset_ball (by linarith)).trans hSB
    have hVΩ' : closure V ⊆ Ω' := by
      rw [hVdef, closure_ball z hr16.ne']
      exact closedBall_subset_ball' (by rw [dist_comm]; linarith)
    -- The regularized limit is plurisubharmonic and dominates every member.
    have hbddB : LocallyUniformlyBoundedAbove (range v) (ball z r) := fun x _ =>
      ⟨univ, univ_mem, C, by rintro _ ⟨j, rfl⟩ y ⟨_, hy⟩; exact hbound j y hy⟩
    have hPpsh : PlurisubharmonicOn P (ball z r) := by
      have := plurisubharmonicOn_uscRegularization_sSup isOpen_ball (range_nonempty v)
        (by rintro _ ⟨j, rfl⟩; exact hpsh j) hbddB
      rwa [sSup_range] at this
    have hvP : ∀ j x, v j x ≤ P x := fun j x =>
      (le_iSup (fun k => v k x) j).trans
        (by rw [← iSup_apply]; exact le_uscRegularization (⨆ k, v k) x)
    -- `P` is the pointwise limit a.e. on `Ω'`.
    have hae : ∀ᵐ x ∂volume, x ∈ Ω' → P x = ⨆ j, v j x := by
      have h := ae_uscRegularization_iSup_eq_on_ball (fun j => (hpsh j).discPshOn) hmono
        volume a (S := 3 * r / 4) (C := C) (by positivity) hSB
        (fun j y hy => hbound j y (hSB hy))
      filter_upwards [h] with x hx hxΩ'
      rw [hP, ← hPfun]
      exact hx (by rwa [show 3 * r / 4 / 2 = 3 * r / 8 by ring])
    -- `L¹` convergence of `w j` to `P` on `Ω'`, by dominated convergence.
    have hwmeas : ∀ j, AEMeasurable (w j) (volume.restrict Ω') := fun j =>
      UpperSemicontinuousOn.aemeasurable_restrict_of_isOpen
        (((hpsh _).discPshOn).upperSemicontinuousOn.mono hΩ'B) isOpen_ball
    have hPmeas : AEMeasurable P (volume.restrict Ω') :=
      (upperSemicontinuous_uscRegularization _).measurable.aemeasurable
    have hL1 : Tendsto (fun j => ∫⁻ x in Ω', (P x - w j x).toENNReal) atTop (𝓝 0) := by
      have hlim := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict Ω') (F := fun j x => (P x - w j x).toENNReal)
        (f := fun _ => 0) (fun x => ((C : EReal) - w 0 x).toENNReal)
        (fun j => (hPmeas.add (hwmeas j).neg).ereal_toENNReal) ?_ ?_ ?_
      · simpa using hlim
      · intro j
        filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with x hx hxΩ'
        refine EReal.toENNReal_le_toENNReal (EReal.sub_le_sub ?_ ?_)
        · rw [hx hxΩ']
          exact iSup_le fun k => hbound k x (hΩ'B hxΩ')
        · exact hmono x (hΩ'B hxΩ') (Nat.add_le_add_right (Nat.zero_le j) j₀)
      · have hdef := ((hpsh j₀).discPshOn).ball_deficit_le volume a (3 * r / 8) C hΩ'B
          (fun y hy => hbound j₀ y (hΩ'B hy))
        have hw0 : w 0 = v j₀ := by simp [hw]
        rw [hw0]
        refine ne_top_of_le_ne_top (ENNReal.mul_ne_top measure_ball_lt_top.ne ?_) hdef
        have htop : v j₀ a ≠ ⊤ := ((hpsh j₀).discPshOn).ne_top a (hΩ'B (mem_ball_self (by positivity)))
        rw [← EReal.coe_toReal htop hva, ← EReal.coe_sub, EReal.real_coe_toENNReal]
        exact ENNReal.ofReal_ne_top
      · filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with x hx hxΩ'
        have hmx : Monotone fun j => v j x := hmono x (hΩ'B hxΩ')
        have hwsup : (⨆ j, w j x) = ⨆ j, v j x := hmx.iSup_nat_add j₀
        rw [hx hxΩ']
        by_cases hbot : (⨆ j, v j x) = ⊥
        · have hwb : ∀ j, w j x = ⊥ := fun j =>
            eq_bot_iff.mpr (hbot ▸ le_iSup (fun k => v k x) (j + j₀))
          simp [hbot, hwb]
        · have hle : (⨆ j, v j x) ≤ (C : EReal) := iSup_le fun k => hbound k x (hΩ'B hxΩ')
          have hnetop : (⨆ j, v j x) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) hle
          obtain ⟨p, hp⟩ : ∃ p : ℝ, (p : EReal) = ⨆ j, v j x :=
            ⟨_, EReal.coe_toReal hnetop hbot⟩
          have h := tendsto_coe_sub_iSup_toENNReal (C := p)
            (b := fun j => w j x) (fun i k hik => hmx (Nat.add_le_add_right hik j₀))
          rw [hwsup, ← hp, ← EReal.coe_sub, sub_self, EReal.coe_zero,
            EReal.toENNReal_zero] at h
          rw [← hp]
          exact h
    -- Hiep's theorem on `Ω'`, read off on the small ball `V` around the centre.
    have hconv := hH Ω' P f c isOpen_ball (hPpsh.mono hΩ'B) (hf.mono hΩ'B) hc
      (hL2.mono hΩ'B).2 w (fun j => (hpsh _).mono hΩ'B) (fun j x _ => hvP _ x) hL1
      V isOpen_ball (by rw [hVdef, closure_ball z hr16.ne']; exact isCompact_closedBall _ _)
      hVΩ'
    obtain ⟨j₁, hj₁⟩ := (hconv.eventually (Iio_mem_nhds zero_lt_one)).exists
    have hL2V := hL2.mono hVB
    refine ⟨j₁ + j₀, hc, V, isOpen_ball, mem_ball_self hr16, hf.mono hVB, ?_, ?_⟩
    · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn isOpen_ball
        (fun y hy => (hpsh _ y (hVB hy)).quasiPlurisubharmonicAt) hc.ne'
        (hf.continuousOn.mono hVB)
    · calc ∫⁻ x in V, multiplierDensity (v (j₁ + j₀)) c f x
          ≤ ∫⁻ x in V, ((multiplierDensity (w j₁) c f x - multiplierDensity P c f x) +
              multiplierDensity P c f x) :=
            lintegral_mono fun x => le_tsub_add
        _ = (∫⁻ x in V, (multiplierDensity (w j₁) c f x - multiplierDensity P c f x)) +
              ∫⁻ x in V, multiplierDensity P c f x :=
            lintegral_add_right' _ hL2V.1
        _ < ⊤ := ENNReal.add_lt_top.mpr ⟨(show _ < (1 : ℝ≥0∞) from hj₁).trans ENNReal.one_lt_top, hL2V.2⟩
  · -- Every member is a pole throughout `V`: then `f ≡ 0` on `V`.
    push Not at hex
    have hae := ae_uscRegularization_iSup_eq_on_ball (fun j => (hpsh j).discPshOn) hmono
      volume z hr subset_rfl hbound
    have hPbot : ∀ᵐ x ∂(volume.restrict V), P x = ⊥ := by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with x hx hxV
      rw [hP, ← hPfun, hx (ball_subset_ball (by linarith) hxV)]
      exact iSup_eq_bot.mpr fun j => hex j x hxV
    have hL2V := hL2.mono hVB
    have hf0 : f =ᵐ[volume.restrict V] 0 := by
      filter_upwards [ae_lt_top' hL2V.1 hL2V.2.ne, hPbot] with x hx hxP
      by_contra hne
      exact hx.ne (multiplierDensity_eq_top_at_pole hc hxP hne)
    have hfV : EqOn f 0 V :=
      Measure.eqOn_open_of_ae_eq hf0 isOpen_ball (hf.continuousOn.mono hVB) continuousOn_const
    refine ⟨0, hc, V, isOpen_ball, mem_ball_self hr16, hf.mono hVB, ?_⟩
    exact (weightedL2On_zero (v 0) c V volume).congr measurableSet_ball (fun _ _ => rfl)
      (fun y hy => (hfV hy).symm)

/-- **Strong openness for increasing sequences from Hiep's theorem.**  Hiep's
strong effective openness in dimension `n` discharges the hypothesis
`IncreasingStrongOpenness n` carried by `Hironaka.StrongOpennessEnvelope`. -/
theorem increasingStrongOpenness_of_hiep (n : ℕ)
    (hH : HiepStrongEffectiveOpenness n) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ball n (ballIncreasingStrongOpenness_of_hiep n hH)

end

end Hironaka
