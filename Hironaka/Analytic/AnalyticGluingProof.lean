import Hironaka.Analytic.AnalyticGluingData
import Hironaka.Analytic.KahlerCurrentPerturbation
import Hironaka.Analytic.LelongNumberPole
import Hironaka.Analytic.ERealChordUSC
import Hironaka.Analytic.LocalPotentialIndependence
import Hironaka.Analytic.GlobalPotentialTransforms
import Hironaka.Analytic.PotentialTheory.LocalPotentials
import Hironaka.Analytic.KahlerDomination

set_option autoImplicit false

/-!
# Proof of the gluing proposition

Source: Copy-4, `prop:gluing` (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:gluing`.

This module proves, sorry-free, the statement of
`Hironaka.AnalyticGluing.exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses`
(same hypotheses, same conclusion).  It is a separate module only because that
file belongs to a different write set; the open statement there can be closed by
a one-line appeal to `exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses`
below.

## Proof

Let `θ + ddᶜφ_G ≥ ω_G` globally and `θ + ddᶜφ_U ≥ ω_U` over `Ω ⊇ closure U₂`.

* *One lower bound.*  Compactness gives `A > 0` with `ω_U ≤ A ω_G`, so
  `ω' := ω_U / (A + 1)` is a Kähler form below both
  (`exists_kahlerBackground_le_both`); both potentials are `(θ - ω')`-PSH
  (`thetaPlurisubharmonicOn_add_of_semipositive` for the local one).
* *The glued potential* is `φ = max(φ_U - C, φ_G)` on `U₂` and `φ_G` elsewhere.
  On `U₂ \ U₁` the collar inequality gives `φ = φ_G`, so `φ = φ_G` off `U₁`.
  At a chart point over `closure U₁` both branches are PSH after adding the SAME
  local potential of `θ - ω'` (two potentials of one form differ by a
  pluriharmonic function, `smoothLocalPotential_psh_iff`), and a maximum of PSH
  functions is PSH.  At a chart point off `closure U₁`, `φ = φ_G` nearby.
  `φ ≥ φ_G` gives local nondegeneracy.
* *Smooth near `p`.*  `φ_G` is upper semicontinuous with `φ_G(p) = -∞`, and
  `φ_U` is smooth near `p`, so `φ_U - C > φ_G` near `p` and `φ = φ_U - C` there.
* *`p ∉ E_nK`.*  A positive Lelong number would force `φ(p) = -∞`
  (`eq_bot_of_lelongNumber_pos`), but `φ(p)` is finite.  In dimension zero the
  hypotheses are contradictory: charts are single points, so local
  nondegeneracy of `φ_G` forbids `φ_G(p) = -∞`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.AnalyticGluingProof

open Hironaka Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.AnalyticGluingData

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Enlarging the background form by a semipositive form preserves the
theta-PSH criterion over a set. -/
theorem thetaPlurisubharmonicOn_add_of_semipositive {a b : ClosedRealOneOneForm n Y}
    {u : Y → EReal} {Ω : Set Y} (hu : ThetaPlurisubharmonicOn a.val u Ω)
    (hb : b.val.IsSemipositive) : ThetaPlurisubharmonicOn (a + b).val u Ω := by
  have hb0 := (Hironaka.LocalPotentials.thetaPlurisubharmonic_zero_iff
    b).mpr hb
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  obtain ⟨V, σ, hzV, hσ, hq⟩ := hb0 e z hz
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  refine ⟨W ∩ V, fun y => ρ y + σ y, ⟨hzW, hzV⟩,
    Hironaka.LocalPotentials.localPotential_add
      (hρ.mono hWV inter_subset_left) (hσ.mono hWV inter_subset_right), ?_⟩
  have hfun :
      (fun y => chartFunction u e y + ((ρ y + σ y : ℝ) : EReal)) =
      (fun y => (chartFunction u e y + (ρ y : EReal)) +
        (chartFunction (fun _ => (0 : EReal)) e y + (σ y : EReal))) := by
    funext y
    simp only [chartFunction, EReal.coe_add, zero_add]
    ac_rfl
  rw [hfun]
  exact (hp.mono inter_subset_left).add (hq.mono inter_subset_right)

/-- On a compact manifold two Kähler forms dominate a common Kähler form. -/
theorem exists_kahlerBackground_le_both [CompactSpace Y]
    (ω₁ ω₂ : KahlerBackground n Y) :
    ∃ ω' : KahlerBackground n Y, (ω₁.form - ω'.form).val.IsSemipositive ∧
      (ω₂.form - ω'.form).val.IsSemipositive := by
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω₁ (-ω₂.form)
  have hc : 0 < 1 / (A + 1) := by positivity
  have hcA : 1 / (A + 1) * A ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hc1 : 1 / (A + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  refine ⟨KahlerBackground.smul hc ω₂, fun e z hz v => ?_, fun e z hz v => ?_⟩
  · have h1 := hsemi e z hz v
    have h2 := ω₁.isSemipositive e z hz v
    simp only [KahlerBackground.smul_form, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  · have h3 := ω₂.isSemipositive e z hz v
    simp only [KahlerBackground.smul_form, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at ⊢
    nlinarith

/-- **Gluing a global and a local positive branch** (Copy-4, `prop:gluing`). -/
theorem exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses
    [CompactSpace Y] [ConnectedSpace Y] (hKahler : Nonempty (KahlerBackground n Y))
    (θY : ClosedRealOneOneForm n Y) (U₁ U₂ : Set Y) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hU₁₂ : RelCompactSubset U₁ U₂) (p : Y) (hp : p ∈ U₁) (φG φU : Y → EReal)
    (hglue : GluingHypotheses θY U₁ U₂ p φG φU) :
    (∃ T : KahlerCurrent (RealBottChern.ofRepresentative θY),
        IsSmoothNear (n := n) T.potential p) ∧
      p ∉ nonKahlerLocus (RealBottChern.ofRepresentative θY) := by
  classical
  obtain ⟨⟨⟨ωG, hG⟩, hGp⟩, ⟨⟨Ω, -, hU₂Ω, ωU, hU⟩, hsmooth⟩, C, hC⟩ := hglue
  obtain ⟨ω', hG', hU'⟩ := exists_kahlerBackground_le_both ωG ωU
  have hGη : IsThetaPshPotential (θY - ω'.form).val φG := by
    have h : θY - ω'.form = (θY - ωG.form) + (ωG.form - ω'.form) := by abel
    rw [h]
    exact Hironaka.LocalPotentials.isThetaPshPotential_add_of_semipositive
      hG hG'
  have hUη : ThetaPlurisubharmonicOn (θY - ω'.form).val φU Ω := by
    have h : θY - ω'.form = (θY - ωU.form) + (ωU.form - ω'.form) := by abel
    rw [h]
    exact thetaPlurisubharmonicOn_add_of_semipositive hU.1 hU'
  -- The glued potential.
  let φ : Y → EReal := fun y =>
    if y ∈ U₂ then max (φU y + ((-C : ℝ) : EReal)) (φG y) else φG y
  have hU₁U₂ : U₁ ⊆ U₂ := subset_closure.trans hU₁₂.2
  have hcollar : ∀ y ∈ U₂, y ∉ U₁ → φU y + ((-C : ℝ) : EReal) ≤ φG y := by
    intro y hy hy1
    have h := hC y ⟨subset_closure hy, hy1⟩
    calc φU y + ((-C : ℝ) : EReal) ≤ (φG y + (C : EReal)) + ((-C : ℝ) : EReal) := by
          gcongr
      _ = φG y := by
          rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  have hφ_out : ∀ y, y ∉ U₁ → φ y = φG y := by
    intro y hy1
    by_cases hy : y ∈ U₂
    · simp only [φ, if_pos hy]
      exact max_eq_right (hcollar y hy hy1)
    · simp only [φ, if_neg hy]
  have hφ_in : ∀ y ∈ U₂, φ y = max (φU y + ((-C : ℝ) : EReal)) (φG y) :=
    fun y hy => if_pos hy
  have hφ_ge : ∀ y, φG y ≤ φ y := by
    intro y
    by_cases hy : y ∈ U₂
    · rw [hφ_in y hy]
      exact le_max_right _ _
    · rw [hφ_out y (fun h => hy (hU₁U₂ h))]
  have hpsh : ThetaPlurisubharmonic (θY - ω'.form).val φ := by
    intro e z hz
    obtain ⟨W, ρ, hzW, hρ, hpG⟩ := hGη.1 e z hz
    by_cases hyc : e.val.symm z ∈ closure U₁
    · have hyΩ : e.val.symm z ∈ Ω := hU₂Ω (subset_closure (hU₁₂.2 hyc))
      obtain ⟨V, σ, hzV, hσ, hpU⟩ := hUη e z hz hyΩ
      have hW'o : IsOpen (W ∩ V ∩ (e.val.target ∩ e.val.symm ⁻¹' U₂)) :=
        (hρ.1.inter hσ.1).inter (e.val.isOpen_inter_preimage_symm hU₂)
      have hρ' := hρ.mono hW'o (inter_subset_left.trans inter_subset_left)
      have hσ' := hσ.mono hW'o (inter_subset_left.trans inter_subset_right)
      have hpU' : PlurisubharmonicOn (fun y => chartFunction φU e y + (ρ y : EReal))
          (W ∩ V ∩ (e.val.target ∩ e.val.symm ⁻¹' U₂)) :=
        (_root_.Hironaka.PotentialTheory.GlobalPotentials.smoothLocalPotential_psh_iff _ e _ σ ρ hσ' hρ' (chartFunction φU e)).mp
          (hpU.mono (inter_subset_left.trans inter_subset_right))
      have hconst : PlurisubharmonicOn (fun _ => ((-C : ℝ) : EReal))
          (W ∩ V ∩ (e.val.target ∩ e.val.symm ⁻¹' U₂)) :=
        plurisubharmonicOn_coe_of_smoothDDC_eq_zero (h := fun _ => -C) hW'o contDiffOn_const
          (fun w _ => GlobalPotentialTransforms.smoothDDC_const _ w)
      have hmax := (hpU'.add hconst).max (hpG.mono (inter_subset_left.trans inter_subset_left))
      refine ⟨W ∩ V ∩ (e.val.target ∩ e.val.symm ⁻¹' U₂), ρ,
        ⟨⟨hzW, hzV⟩, hz, hU₁₂.2 hyc⟩, hρ', fun w hw => (hmax w hw).congr ?_⟩
      filter_upwards [hW'o.mem_nhds hw] with q hq
      simp only [chartFunction]
      rw [hφ_in _ hq.2.2, ← max_add_add_right, add_right_comm]
    · have hW'o : IsOpen (W ∩ (e.val.target ∩ e.val.symm ⁻¹' (closure U₁)ᶜ)) :=
        hρ.1.inter (e.val.isOpen_inter_preimage_symm isClosed_closure.isOpen_compl)
      refine ⟨W ∩ (e.val.target ∩ e.val.symm ⁻¹' (closure U₁)ᶜ), ρ, ⟨hzW, hz, hyc⟩,
        hρ.mono hW'o inter_subset_left, fun w hw => (hpG w hw.1).congr ?_⟩
      filter_upwards [hW'o.mem_nhds hw] with q hq
      simp only [chartFunction]
      rw [hφ_out _ (fun h => hq.2.2 (subset_closure h))]
  have hnd : LocallyNondegenerate φ := by
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hGη.2 x U hU hxU
    exact ⟨y, hyU, fun hbot => hy (eq_bot_iff.mpr (hbot ▸ hφ_ge y))⟩
  let T : KahlerCurrent (RealBottChern.ofRepresentative θY) :=
    ⟨θY, rfl, φ, ω', ⟨hpsh, hnd⟩⟩
  -- Smoothness near `p`.
  obtain ⟨U₀, hU₀o, hpU₀, h₀, hh₀, hφU₀⟩ := hsmooth
  have hh₀cont : ContinuousAt h₀ p := by
    have hps := mem_complexChartAt_source (n := n) p
    have hzt : (complexChartAt (n := n) p).val p ∈ (complexChartAt (n := n) p).val.target ∩
        (complexChartAt (n := n) p).val.symm ⁻¹' U₀ :=
      ⟨(complexChartAt (n := n) p).val.map_source hps, by
        simp [(complexChartAt (n := n) p).val.left_inv hps, hpU₀]⟩
    have hc : ContinuousAt (fun z => h₀ ((complexChartAt (n := n) p).val.symm z))
        ((complexChartAt (n := n) p).val p) :=
      (hh₀ (complexChartAt (n := n) p)).continuousOn.continuousAt
        (((complexChartAt (n := n) p).val.isOpen_inter_preimage_symm hU₀o).mem_nhds hzt)
    refine (hc.comp ((complexChartAt (n := n) p).val.continuousAt hps)).congr ?_
    filter_upwards [(complexChartAt (n := n) p).val.open_source.mem_nhds hps] with y hy
    simp [Function.comp_apply, (complexChartAt (n := n) p).val.left_inv hy]
  have husc : UpperSemicontinuous φG := hGη.1.quasiPlurisubharmonic.upperSemicontinuous
  have hev1 : ∀ᶠ y in 𝓝 p, φG y < ((h₀ p - C - 1 : ℝ) : EReal) :=
    husc p _ (by show φG p < _; rw [hGp]; exact EReal.bot_lt_coe _)
  have hev2 : ∀ᶠ y in 𝓝 p, h₀ p - 1 < h₀ y :=
    hh₀cont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨V, hVP, hVo, hpV⟩ := eventually_nhds_iff.mp (hev1.and hev2)
  have hφ_near : ∀ y ∈ U₀ ∩ U₁ ∩ V, φ y = ((h₀ y - C : ℝ) : EReal) := by
    intro y hy
    rw [hφ_in y (hU₁U₂ hy.1.2), hφU₀ y hy.1.1]
    have hle : φG y ≤ ((h₀ y : ℝ) : EReal) + ((-C : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      refine (hVP y hy.2).1.le.trans (EReal.coe_le_coe_iff.mpr ?_)
      linarith [(hVP y hy.2).2]
    rw [max_eq_left hle, ← EReal.coe_add, sub_eq_add_neg]
  have hTsmooth : IsSmoothNear (n := n) T.potential p :=
    ⟨U₀ ∩ U₁ ∩ V, (hU₀o.inter hU₁).inter hVo, ⟨⟨hpU₀, hp⟩, hpV⟩, fun y => h₀ y - C,
      fun e => ((hh₀ e).sub contDiffOn_const).mono
        (inter_subset_inter_right _ (preimage_mono (inter_subset_left.trans inter_subset_left))),
      hφ_near⟩
  refine ⟨⟨T, hTsmooth⟩, fun hpE => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hps := mem_complexChartAt_source (n := 0) p
    obtain ⟨y, hy, hyne⟩ := hG.2 p _ (complexChartAt (n := 0) p).val.open_source hps
    have hyp : y = p :=
      (complexChartAt (n := 0) p).val.injOn hy hps (Subsingleton.elim _ _)
    exact hyne (hyp ▸ hGp)
  · have hbot := eq_bot_of_lelongNumber_pos hn hpsh (hpE T)
    change φ p = ⊥ at hbot
    rw [hφ_near p ⟨⟨hpU₀, hp⟩, hpV⟩] at hbot
    exact EReal.coe_ne_bot _ hbot

end

end Hironaka.AnalyticGluingProof
