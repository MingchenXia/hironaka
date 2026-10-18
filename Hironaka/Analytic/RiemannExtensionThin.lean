/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.RiemannBoundedExact
import Hironaka.Analytic.RiemannExtension
import Hironaka.Analytic.HolomorphicZeroSetThin

set_option autoImplicit false

/-!
# Riemann extension across a thin analytic set

Blueprint `rem:riemann-extension-thin` (Demailly, *Complex analytic and differential geometry*,
II.4.2).  Let `U ⊆ ℂ^d` be open and `T ⊆ U` a set which is, near each of its points `t`, contained
in the zero set of a holomorphic function `h_t` on a ball around `t` that does not vanish
identically near `t` (for instance an analytic subset of `U` with empty interior).  If `U \ T` is
open and `f` is holomorphic on `U \ T` and locally bounded near `T`, then `f` extends to a
holomorphic function on `U` (`exists_extension_of_thin`).

The local extensions are those of `RiemannExtension.exists_extension_of_bounded` (translated to
`t`).  On a ball around `t` the local extension `G_t` agrees with `f` off `T`: off `h_t⁻¹(0)` by
construction, and on the rest of `U \ T` by continuity, since `U \ h_t⁻¹(0)` is dense
(`RiemannExtension.dense_compl_zeroSet`).  The global extension takes at a point of `T` the limit
of `f` along `U \ T`, which therefore equals `G_t` near every `t ∈ T`.
-/

open Set Filter Topology Metric

noncomputable section

namespace Hironaka.RiemannExtensionThin

variable {d : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin d)

/-- **The local extension at a point of `T`, agreeing with `f` on the whole ball off `T`.** -/
theorem exists_local_extension {U T : Set E} (hUT : IsOpen (U \ T)) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (U \ T)) {t : E} {r : ℝ} (hr : 0 < r) (hrU : ball t r ⊆ U)
    {h : E → ℂ} (hh : DifferentiableOn ℂ h (ball t r)) (hne : ¬ ∀ᶠ z in 𝓝 t, h z = 0)
    (hTh : ∀ z ∈ ball t r, z ∈ T → h z = 0) {C : ℝ} (hC : ∀ z ∈ ball t r \ T, ‖f z‖ ≤ C) :
    ∃ ρ > 0, ρ ≤ r ∧ ball t ρ ⊆ closure (ball t ρ \ T) ∧ ∃ G : E → ℂ,
      DifferentiableOn ℂ G (ball t ρ) ∧ ∀ z ∈ ball t ρ \ T, G z = f z := by
  -- translate to the origin
  set H : E → ℂ := fun z => h (t + z) with hH
  set Fz : E → ℂ := fun z => f (t + z) with hFz
  have hball : ∀ z : E, z ∈ ball (0 : E) r ↔ t + z ∈ ball t r := by
    intro z
    simp [mem_ball, dist_eq_norm]
  have hHd : DifferentiableOn ℂ H (ball 0 r) := fun z hz =>
    ((hh (t + z) ((hball z).1 hz)).comp z (differentiableAt_id.const_add t).differentiableWithinAt
      (fun w hw => (hball w).1 hw))
  have hHne : ¬ ∀ᶠ z in 𝓝 (0 : E), H z = 0 := by
    intro hev
    apply hne
    have hcont : Tendsto (fun w : E => w - t) (𝓝 t) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [hcont.eventually hev] with w hw
    simpa [hH] using hw
  have hFd : DifferentiableOn ℂ Fz (ball 0 r \ H ⁻¹' {0}) := by
    intro z hz
    have hzU : t + z ∈ U \ T := by
      refine ⟨hrU ((hball z).1 hz.1), fun hzT => hz.2 ?_⟩
      exact hTh _ ((hball z).1 hz.1) hzT
    exact (((hf _ hzU).differentiableAt (hUT.mem_nhds hzU)).comp z
      (differentiableAt_id.const_add t)).differentiableWithinAt
  have hFb : ∃ C', ∀ z ∈ ball (0 : E) r \ H ⁻¹' {0}, ‖Fz z‖ ≤ C' := by
    refine ⟨C, fun z hz => hC _ ⟨(hball z).1 hz.1, fun hzT => hz.2 ?_⟩⟩
    exact hTh _ ((hball z).1 hz.1) hzT
  obtain ⟨ρ, hρ, G₀, hG₀, hG₀f⟩ := RiemannExtension.exists_extension_of_bounded hr hHd hHne hFd hFb
  set ρ' := min ρ r with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ hr
  set G : E → ℂ := fun w => G₀ (w - t) with hG
  have hballt : ∀ w : E, w ∈ ball t ρ' → w - t ∈ ball (0 : E) ρ := by
    intro w hw
    have : dist w t < ρ := lt_of_lt_of_le hw (min_le_left _ _)
    simpa [mem_ball, dist_eq_norm] using this
  have hballr : ball t ρ' ⊆ ball t r := ball_subset_ball (min_le_right _ _)
  have hGd : DifferentiableOn ℂ G (ball t ρ') := fun w hw =>
    ((hG₀ (w - t) (hballt w hw)).comp w (differentiableAt_id.sub_const t).differentiableWithinAt
      (fun v hv => hballt v hv))
  -- agreement off `h⁻¹(0)` and then, by density, off `T`
  have hoff : EqOn G f (ball t ρ' \ h ⁻¹' {0}) := by
    intro w hw
    have h1 := hG₀f (w - t) (hballt w hw.1) (by simpa [hH] using hw.2)
    simpa [hG, hFz] using h1
  have hdense : ball t ρ' ⊆ closure (ball t ρ' \ h ⁻¹' {0}) := by
    refine RiemannExtension.dense_compl_zeroSet isOpen_ball (convex_ball t ρ').isPreconnected
      (hh.mono hballr) (mem_ball_self hρ'pos) hne
  have hopen : IsOpen (ball t ρ' \ T) := by
    have : ball t ρ' \ T = ball t ρ' ∩ (U \ T) := by
      ext w
      constructor
      · rintro ⟨hw, hwT⟩
        exact ⟨hw, hrU (hballr hw), hwT⟩
      · rintro ⟨hw, -, hwT⟩
        exact ⟨hw, hwT⟩
    rw [this]
    exact isOpen_ball.inter hUT
  have hsubT : ball t ρ' \ h ⁻¹' {0} ⊆ ball t ρ' \ T := fun w hw =>
    ⟨hw.1, fun hwT => hw.2 (hTh w (hballr hw.1) hwT)⟩
  refine ⟨ρ', hρ'pos, min_le_right _ _, fun w hw => closure_mono hsubT (hdense hw), G, hGd, ?_⟩
  refine EqOn.of_subset_closure hoff (hGd.continuousOn.mono sdiff_subset) ?_ ?_ ?_
  · exact (hf.mono fun w hw => ⟨hrU (hballr hw.1), hw.2⟩).continuousOn
  · intro w hw
    exact ⟨hw.1, fun hwT => hw.2 (hTh w (hballr hw.1) hwT)⟩
  · exact fun w hw => closure_mono (fun v hv => hv) (hdense hw.1)

/-- **Riemann extension across a thin set** (`rem:riemann-extension-thin`).  Let `T ⊆ U` with
`U \ T` open, near each of its points contained in the zero set of a holomorphic function on a
ball that does not vanish identically near the point; a function holomorphic on `U \ T` and
locally bounded near `T` extends holomorphically to `U`. -/
theorem exists_extension_of_thin {U T : Set E} (hUT : IsOpen (U \ T)) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (U \ T))
    (hloc : ∀ t ∈ T, ∃ r > 0, ball t r ⊆ U ∧ ∃ h : E → ℂ, DifferentiableOn ℂ h (ball t r) ∧
      (¬ ∀ᶠ z in 𝓝 t, h z = 0) ∧ ∀ z ∈ ball t r, z ∈ T → h z = 0)
    (hbdd : ∀ t ∈ T, ∃ V ∈ 𝓝 t, ∃ C, ∀ z ∈ V \ T, ‖f z‖ ≤ C) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U \ T) := by
  classical
  have hext : ∀ t ∈ T, ∃ ρ > 0, ball t ρ ⊆ U ∧ ball t ρ ⊆ closure (ball t ρ \ T) ∧
      ∃ G : E → ℂ, DifferentiableOn ℂ G (ball t ρ) ∧ ∀ z ∈ ball t ρ \ T, G z = f z := by
    intro t ht
    obtain ⟨r, hr, hrU, h, hh, hne, hTh⟩ := hloc t ht
    obtain ⟨V, hV, C, hC⟩ := hbdd t ht
    obtain ⟨r', hr', hr'V⟩ := Metric.mem_nhds_iff.1 hV
    have hr'' : 0 < min r r' := lt_min hr hr'
    have hsub : ball t (min r r') ⊆ ball t r := ball_subset_ball (min_le_left _ _)
    obtain ⟨ρ, hρ, hρr, hden, G, hG, hGf⟩ := exists_local_extension hUT hf hr'' (hsub.trans hrU)
      (hh.mono hsub) hne (fun z hz hzT => hTh z (hsub hz) hzT) (C := C)
      (fun z hz => hC z ⟨hr'V (ball_subset_ball (min_le_right _ _) hz.1), hz.2⟩)
    exact ⟨ρ, hρ, (ball_subset_ball hρr).trans (hsub.trans hrU), hden, G, hG, hGf⟩
  choose! ρ hρ hρU hden G hG hGf using hext
  let F : E → ℂ := fun z => if z ∈ T then limUnder (𝓝[U \ T] z) f else f z
  have hFG : ∀ t ∈ T, ∀ z ∈ ball t (ρ t), F z = G t z := by
    intro t ht z hz
    by_cases hzT : z ∈ T
    · have hcl : z ∈ closure (U \ T) :=
        closure_mono (fun w (hw : w ∈ ball t (ρ t) \ T) => (⟨hρU t ht hw.1, hw.2⟩ : w ∈ U \ T))
          (hden t ht hz)
      have hne : (𝓝[U \ T] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
      have htend : Tendsto f (𝓝[U \ T] z) (𝓝 (G t z)) := by
        have hGc : ContinuousAt (G t) z :=
          (hG t ht).continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
        refine (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [inter_mem_nhdsWithin (U \ T) (isOpen_ball.mem_nhds hz)] with w hw
        exact hGf t ht w ⟨hw.2, hw.1.2⟩
      simp only [F, if_pos hzT]
      exact htend.limUnder_eq
    · simp only [F, if_neg hzT]
      exact (hGf t ht z ⟨hz, hzT⟩).symm
  refine ⟨F, fun z hz => ?_, fun z hz => by simp [F, hz.2]⟩
  by_cases hzT : z ∈ T
  · have hev : F =ᶠ[𝓝 z] G z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hρ z hzT))] with w hw
      exact hFG z hzT w hw
    exact (((hG z hzT).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ z hzT)))
      ).congr_of_eventuallyEq hev).differentiableWithinAt
  · have hzU : z ∈ U \ T := ⟨hz, hzT⟩
    have hev : F =ᶠ[𝓝 z] f := by
      filter_upwards [hUT.mem_nhds hzU] with w hw
      simp [F, hw.2]
    exact (((hf z hzU).differentiableAt (hUT.mem_nhds hzU)).congr_of_eventuallyEq hev
      ).differentiableWithinAt

end Hironaka.RiemannExtensionThin
