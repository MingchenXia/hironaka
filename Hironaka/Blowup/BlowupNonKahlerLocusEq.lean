import Hironaka.Blowup.BlowupPushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The non-Kähler locus of the pullback of a big class under one blowup

Source: CT22, Lemma 4.1; Boucksom, *Divisorial Zariski decompositions*, Prop. 2.3.

`nonKahlerLocus_pullback_eq`: for the blowup `π : Z → Y` of a compact Kähler manifold along a
closed submanifold, `E_nK(π^* {θ}) = π⁻¹ E_nK({θ}) ∪ Exc π`.

`⊆` is `BlowupNonKahlerLocus.nonKahlerLocus_pullback_subset`.  For `⊇`, push a Kähler current `S`
in `π^* {θ}` down (`BlowupPushforward.exists_pushforward`): `u_S - h_Z = ψ ∘ π + δ ε log (U ∘ π)`.

* At `z ∈ Exc π`: `U ∘ π = |h|² U'` with `h(z) = 0`, so `|h| ≤ c ‖z' - z‖` and
  `u_S - h_Z ≤ M + 2 δ ε log ‖z' - z‖ + C` near `z`.
* At `z ∉ Exc π` with `π z ∈ E_nK`: `ψ` is a Kähler current in `{θ}`, so `ν(ψ, π z) > 0`, and
  `ν(u_S, z) ≥ ν(ψ ∘ π, z) ≥ ν(ψ, π z)` since `log (U ∘ π)` is continuous near `z`.
-/

open Set Filter Asymptotics
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupNonKahlerLocusEq

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  BlanchardWeight FactorizedWeightForm FactorizedWeightPsh BlowupExceptionalCentre
  LelongNumberComparison

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- A theta-PSH function takes no value `⊤`. -/
theorem ThetaPlurisubharmonic.ne_top {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) (x : M) : u x ≠ ⊤ := by
  set e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hxW, -, hpsh⟩ := hu e (e.val x) (e.val.map_source hx)
  obtain ⟨V, -, hxV, hdisc⟩ := hpsh _ hxW
  have h := hdisc.ne_top _ hxV
  simp only [chartFunction, e.val.left_inv hx] at h
  intro htop
  rw [htop, EReal.top_add_coe] at h
  exact h rfl

/-- **`E_nK(π^* α) = π⁻¹ E_nK(α) ∪ Exc π`** (CT22, Lemma 4.1). -/
theorem nonKahlerLocus_pullback_eq [CompactSpace Y]
    (hKahler : Nonempty (KahlerBackground n Y)) (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) =
      g ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪ exceptionalLocus n g := by
  refine Subset.antisymm (BlowupNonKahlerLocus.nonKahlerLocus_pullback_subset θ hg) ?_
  intro z hz S
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact BlowupNonKahlerLocus.lelongNumber_pos_of_dim_eq_zero hn _ _
  obtain ⟨omega⟩ := hKahler
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  obtain ⟨D, -, hflatC⟩ := exists_blanchardData_exceptionalCentre hg
  have hC₂C := exceptionalCentre_subset hg
  have hexc : ∀ z', g z' ∉ exceptionalCentre n g → z' ∉ exceptionalLocus n g :=
    fun z' h hE => h ⟨z', hE, rfl⟩
  obtain ⟨F, ε, hε, hK⟩ := BlowupKahler.exists_isKahler_pullback_add_of_flat omega hg D hflatC
    (isClosed_exceptionalCentre hg) hC₂C hexc
  obtain ⟨δ, hδ, ψ, hψ, hZ, hhZ, hid⟩ :=
    BlowupPushforward.exists_pushforward omega θ hg D F hε hK S
  refine lt_of_lt_of_le ?_ (KahlerCurrentMax.lelongNumber_sub_le (u := S.potential)
    (KahlerCurrentMax.continuous_of_chartSmooth hhZ).continuousAt)
  rw [show (fun z => S.potential z - (hZ z : EReal)) = fun z => ψ (g z) +
    ((δ * ε : ℝ) : EReal) * logWeight (fun z => D.weight (g z)) z from funext hid]
  have hgc : Continuous g := hg.contMDiff.continuous
  have hδε : 0 < δ * ε := mul_pos hδ hε
  by_cases hzE : z ∈ exceptionalLocus n g
  · -- positivity on the exceptional locus
    have hgzC : g z ∈ exceptionalCentre n g := by
      rw [← preimage_exceptionalCentre hg] at hzE; exact hzE
    have hU0 : D.weight (g z) = 0 := D.weight_eq_zero_of_mem hgzC
    have hzdom := F.mem_domain z
    have hgen0 : F.gen z z = 0 := by
      have h := F.factor z z hzdom
      rw [hU0] at h
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact Complex.normSq_eq_zero.mp h'
      · exact absurd h' (F.pos z z hzdom).ne'
    -- `ψ ∘ g` is bounded above near `z`
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ψ (g z) < M := by
      induction h : ψ (g z) using EReal.rec with
      | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
      | top => exact absurd h (ThetaPlurisubharmonic.ne_top hψ.1 _)
      | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
    have hψM : ∀ᶠ z' in 𝓝 z, ψ (g z') < M :=
      hgc.continuousAt.eventually (hψ.1.quasiPlurisubharmonic.upperSemicontinuous (g z) M hM)
    -- the smooth part is bounded near `z`
    set e := complexChartAt (n := n) z
    have hze : z ∈ e.val.source := mem_complexChartAt_source z
    have hspc : ContinuousAt (F.smoothPart z) z := by
      have h1 : ContinuousAt (fun ζ => F.smoothPart z (e.val.symm ζ)) (e.val z) := by
        have hmem : e.val z ∈ e.val.target ∩ e.val.symm ⁻¹' F.domain z :=
          ⟨e.val.map_source hze, by rw [mem_preimage, e.val.left_inv hze]; exact hzdom⟩
        exact ((F.smooth z e).continuousOn _ hmem).continuousAt
          ((e.val.isOpen_inter_preimage_symm (F.isOpen_domain z)).mem_nhds hmem)
      have h2 := h1.comp (e.val.continuousAt hze)
      refine h2.congr ?_
      filter_upwards [e.val.open_source.mem_nhds hze] with z' hz'
      simp [e.val.left_inv hz']
    set B := F.smoothPart z z + 1
    have hspB : ∀ᶠ z' in 𝓝 z, F.smoothPart z z' < B :=
      hspc.eventually (gt_mem_nhds (lt_add_one _))
    -- the generator is Lipschitz and vanishes at `z`
    have hGd : DifferentiableAt ℂ (fun ζ => F.gen z (e.val.symm ζ)) (e.val z) :=
      differentiableAt_comp_chart_symm e (e.val.map_source hze)
        (by rw [e.val.left_inv hze]; exact F.gen_mdifferentiable z z hzdom)
    obtain ⟨c, hc, hcw⟩ := hGd.hasFDerivAt.isBigO_sub.exists_pos
    have hlip : ∀ᶠ z' in 𝓝 z, ‖F.gen z z'‖ ≤ c * ‖e.val z' - e.val z‖ := by
      filter_upwards [(e.val.continuousAt hze).eventually hcw.bound,
        e.val.open_source.mem_nhds hze] with z' hz' hz'e
      simpa [e.val.left_inv hz'e, e.val.left_inv hze, hgen0] using hz'
    refine lelongNumber_pos_of_le_log (γ := 2 * (δ * ε)) (by positivity)
      (C := M + (δ * ε) * (2 * Real.log c + Real.log B)) ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hψM, hspB, hlip, e.val.open_source.mem_nhds hze,
      (F.isOpen_domain z).mem_nhds hzdom] with z' h1 h2 h3 h4 h5 hz'z
    have hψtop : ψ (g z') ≠ ⊤ := ne_top_of_lt h1
    have hsp := F.pos z z' h5
    by_cases hg0 : F.gen z z' = 0
    · have hU : D.weight (g z') = 0 := by rw [F.factor z z' h5, hg0]; simp
      have hlog : logWeight (fun z => D.weight (g z)) z' = ⊥ := by simp [logWeight, hU]
      rw [hlog, EReal.coe_mul_bot_of_pos hδε, EReal.add_bot]
      exact bot_le
    have hd : 0 < ‖e.val z' - e.val z‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact fun h => hz'z (e.val.injOn h4 hze h)
    have hng : 0 < ‖F.gen z z'‖ := norm_pos_iff.mpr hg0
    have hns : 0 < Complex.normSq (F.gen z z') := Complex.normSq_pos.mpr hg0
    have hUpos : 0 < D.weight (g z') := by rw [F.factor z z' h5]; exact mul_pos hns hsp
    rw [logWeight_of_pos (U := fun z => D.weight (g z)) hUpos, ← EReal.coe_mul]
    have hbound : δ * ε * Real.log (D.weight (g z')) ≤
        2 * (δ * ε) * Real.log ‖e.val z' - e.val z‖ + (δ * ε) * (2 * Real.log c + Real.log B) := by
      rw [F.factor z z' h5, Real.log_mul hns.ne' hsp.ne', Complex.normSq_eq_norm_sq,
        Real.log_pow]
      have hl1 : Real.log ‖F.gen z z'‖ ≤ Real.log c + Real.log ‖e.val z' - e.val z‖ := by
        rw [← Real.log_mul hc.ne' hd.ne']; exact Real.log_le_log hng h3
      have hl2 : Real.log (F.smoothPart z z') ≤ Real.log B := Real.log_le_log hsp h2.le
      push_cast
      nlinarith [hl1, hl2, hδε]
    calc ψ (g z') + ((δ * ε * Real.log (D.weight (g z')) : ℝ) : EReal)
        ≤ (M : EReal) + ((δ * ε * Real.log (D.weight (g z')) : ℝ) : EReal) :=
          by gcongr
      _ ≤ _ := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith
  · -- off the exceptional locus
    rcases hz with hzY | hzE'
    swap
    · exact absurd hzE' hzE
    have hgzC : g z ∉ exceptionalCentre n g := fun h => hzE (by
      rw [← preimage_exceptionalCentre hg]; exact h)
    set T : KahlerCurrent (RealBottChern.ofRepresentative θ) :=
      ⟨θ, rfl, ψ, KahlerBackground.smul hδ omega, hψ⟩
    have hT : 0 < lelongNumber (n := n) ψ (g z) := hzY T
    have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g z :=
      (hg.contMDiff z).mdifferentiableAt (by simp)
    have hcomp := lelongNumber_le_comp hmd (u := ψ)
      fun hpos => eq_bot_of_lelongNumber_pos hn hψ.1 hpos
    have hUc : Continuous fun z => D.weight (g z) :=
      (KahlerCurrentMax.continuous_of_chartSmooth D.chartSmooth_weight).comp hgc
    have hpos : ∀ᶠ z' in 𝓝 z, 0 < D.weight (g z') :=
      hUc.continuousAt.eventually (lt_mem_nhds (D.weight_pos_of_notMem hgzC))
    set k : Z → ℝ := fun z' => δ * ε * Real.log (D.weight (g z'))
    have hkc : ContinuousAt k z :=
      continuousAt_const.mul (hUc.continuousAt.log (D.weight_pos_of_notMem hgzC).ne')
    have heq : (fun z' => ψ (g z') + ((δ * ε : ℝ) : EReal) *
        logWeight (fun z => D.weight (g z)) z') =ᶠ[𝓝 z] fun z' => ψ (g z') + (k z' : EReal) := by
      filter_upwards [hpos] with z' hz'
      rw [logWeight_of_pos (U := fun z => D.weight (g z)) hz', ← EReal.coe_mul]
    rw [lelongNumber_congr heq]
    have hadd := lelongNumber_add_le (n := n) (u := fun z' => ψ (g z') + (k z' : EReal))
      (h := fun z' => -k z') hkc.neg
    have hfun : (fun z' => ψ (g z') + (k z' : EReal) + ((-k z' : ℝ) : EReal)) =
        fun z' => ψ (g z') := by
      funext z'
      rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
    rw [hfun] at hadd
    exact hT.trans_le (hcomp.trans hadd)

end

end Hironaka.BlowupNonKahlerLocusEq
