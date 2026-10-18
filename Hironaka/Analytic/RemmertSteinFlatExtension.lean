/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.RemmertSteinFlatGraph
import Hironaka.Analytic.RiemannExtensionThin

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The flat case of Remmert--Stein: extension of bounded holomorphic functions over the bad set

Blueprint `rem:remmert-stein-flat`, paragraph "Canonical defining functions" (Demailly, *Complex
analytic and differential geometry*, II.8.7): a bounded holomorphic function on the good base
`B'₀ = (B' \ N) \ Σ₀` extends holomorphically to the ball `B'` (`exists_extension`), by
`RiemannExtensionThin` applied twice: across `Σ₀` in `B' \ N` (a local equation of `Σ₀` which is not
identically zero exists because `Σ₀` has dimension `≤ s - 1`, hence empty interior), then across the
linear subspace `N ∩ B'` (the coordinate `z_p` is a local equation), the bound on `B' \ N` coming from
the density of `B'₀` there (`subset_closure_goodBase`).

Sorry-free.
-/

open Set Filter Topology Metric TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertSteinFlat

open AnalyticDimensionBasics AnalyticSubsetOpens RemmertStatements

variable {n p t : ℕ} {Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t))}
  {a : ComplexModel n} {δ : ℝ}

/-- `Σ₀` has empty interior in `Y₀`. -/
theorem not_mem_nhds_of_dimLE (ht : 1 ≤ t) {Sig₀ : Set (coverTarget Λ a δ)}
    (hSigdim : DimLE (n := p + t) Sig₀ (p + t - 1)) (σ : coverTarget Λ a δ) : Sig₀ ∉ 𝓝 σ :=
  fun h => by
    have := hSigdim σ _ (regularAtDim_of_mem_nhds h)
    omega

/-- No open subset of `B' \ N` lies in `Σ₀`. -/
theorem not_subset_of_isOpen (ht : 1 ≤ t) {Sig₀ : Set (coverTarget Λ a δ)}
    (hSigdim : DimLE (n := p + t) Sig₀ (p + t - 1)) {O : Set (ComplexModel (p + t))}
    (hO : IsOpen O) {w : ComplexModel (p + t)} (hwO : w ∈ O)
    (hwB : w ∈ ball (Λ a).1 δ \ complexCoordinatePlane (p + t) p)
    (hOS : O ∩ (ball (Λ a).1 δ \ complexCoordinatePlane (p + t) p) ⊆ (↑) '' Sig₀) : False := by
  apply not_mem_nhds_of_dimLE ht hSigdim (⟨w, hwB⟩ : coverTarget Λ a δ)
  have hO' : ((↑) ⁻¹' O : Set (coverTarget Λ a δ)) ∈ 𝓝 (⟨w, hwB⟩ : coverTarget Λ a δ) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hO.mem_nhds hwO)
  refine mem_of_superset hO' fun y hy => ?_
  obtain ⟨y', hy', hyy'⟩ := hOS ⟨hy, y.2⟩
  rwa [Subtype.ext hyy'] at hy'

/-- **`B'₀` is dense in `B' \ N`.** -/
theorem subset_closure_goodBase (ht : 1 ≤ t) {Sig₀ : Set (coverTarget Λ a δ)}
    (hSigdim : DimLE (n := p + t) Sig₀ (p + t - 1)) :
    ball (Λ a).1 δ \ complexCoordinatePlane (p + t) p ⊆ closure (goodBase Λ a δ Sig₀) := by
  intro w hw
  rw [_root_.mem_closure_iff]
  intro O hO hwO
  by_contra hne
  refine not_subset_of_isOpen ht hSigdim hO hwO hw fun y hy => ?_
  by_contra hyS
  exact hne ⟨y, hy.1, hy.2, hyS⟩

/-- **Riemann extension over the bad set.** -/
theorem exists_extension (ht : 1 ≤ t) {Sig₀ : Set (coverTarget Λ a δ)}
    (hSiga : IsComplexAnalyticSubset (n := p + t) Sig₀)
    (hSigdim : DimLE (n := p + t) Sig₀ (p + t - 1)) {f : ComplexModel (p + t) → ℂ}
    (hf : DifferentiableOn ℂ f (goodBase Λ a δ Sig₀)) {C : ℝ}
    (hC : ∀ w ∈ goodBase Λ a δ Sig₀, ‖f w‖ ≤ C) :
    ∃ F : ComplexModel (p + t) → ℂ, DifferentiableOn ℂ F (ball (Λ a).1 δ) ∧
      EqOn F f (goodBase Λ a δ Sig₀) := by
  classical
  set N := complexCoordinatePlane (p + t) p with hN
  set U₁ := ball (Λ a).1 δ \ N with hU₁
  set T₁ : Set (ComplexModel (p + t)) := (↑) '' Sig₀ with hT₁
  have hU₁o : IsOpen U₁ := (coverTarget Λ a δ).isOpen
  have hgood : goodBase Λ a δ Sig₀ = U₁ \ T₁ := rfl
  have hT₁U : T₁ ⊆ U₁ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  -- step 1: across `Σ₀`
  have hloc₁ : ∀ t₀ ∈ T₁, ∃ r > 0, ball t₀ r ⊆ U₁ ∧ ∃ h : ComplexModel (p + t) → ℂ,
      DifferentiableOn ℂ h (ball t₀ r) ∧ (¬ ∀ᶠ z in 𝓝 t₀, h z = 0) ∧
      ∀ z ∈ ball t₀ r, z ∈ T₁ → h z = 0 := by
    intro t₀ ht₀
    have hpre : ((↑) ⁻¹' T₁ : Set (coverTarget Λ a δ)) = Sig₀ :=
      Subtype.val_injective.preimage_image Sig₀
    obtain ⟨P⟩ := nonempty_presentation_of_preimage_val (U := coverTarget Λ a δ)
      (by rw [hpre]; exact hSiga) (hT₁U ht₀)
    have hchart : (complexChartAt (n := p + t) t₀).val =
        OpenPartialHomeomorph.refl (ComplexModel (p + t)) := by
      simp [complexChartAt, chartAt_self_eq]
    have hW : P.coordinateNeighborhood ∈ 𝓝 t₀ := by
      have := P.center_mem_coordinateNeighborhood
      rw [hchart] at this
      exact P.isOpen_coordinateNeighborhood.mem_nhds this
    have hzero : ∀ y ∈ P.coordinateNeighborhood, (y ∈ T₁ ↔ ∀ i, P.generator i y = 0) := by
      intro y hy
      have := P.zeroLocus (y := y) (by rw [hchart]; trivial) (by rw [hchart]; exact hy)
      rwa [hchart] at this
    obtain ⟨i, hi⟩ : ∃ i, ¬ ∀ᶠ z in 𝓝 t₀, P.generator i z = 0 := by
      by_contra hall
      push Not at hall
      have hev : ∀ᶠ z in 𝓝 t₀, z ∈ T₁ := by
        filter_upwards [hW, Filter.eventually_all.mpr hall] with z hz hz'
        exact (hzero z hz).mpr hz'
      obtain ⟨O, hOT, hOo, ht₀O⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hev (hU₁o.mem_nhds (hT₁U ht₀)))
      exact not_subset_of_isOpen ht hSigdim hOo ht₀O (hT₁U ht₀)
        fun y hy => (hOT hy.1).1
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hU₁o.mem_nhds (hT₁U ht₀)))
    refine ⟨r, hr, fun z hz => (hrsub hz).2, P.generator i,
      (P.generator_holomorphic i).mono fun z hz => (hrsub hz).1, hi, fun z hz hzT => ?_⟩
    exact (hzero z (hrsub hz).1).mp hzT i
  have hbdd₁ : ∀ t₀ ∈ T₁, ∃ V ∈ 𝓝 t₀, ∃ C', ∀ z ∈ V \ T₁, ‖f z‖ ≤ C' :=
    fun t₀ ht₀ => ⟨U₁, hU₁o.mem_nhds (hT₁U ht₀), C, fun z hz => hC z hz⟩
  obtain ⟨F₁, hF₁d, hF₁eq⟩ := RiemannExtensionThin.exists_extension_of_thin
    (hgood ▸ isOpen_goodBase hSiga.isClosed) (hgood ▸ hf) hloc₁ hbdd₁
  -- the bound on `B' \ N`
  have hF₁C : ∀ z ∈ U₁, ‖F₁ z‖ ≤ C := by
    intro z hz
    have hzc := subset_closure_goodBase ht hSigdim hz
    rw [mem_closure_iff_nhdsWithin_neBot] at hzc
    have hcont : Tendsto F₁ (𝓝[goodBase Λ a δ Sig₀] z) (𝓝 (F₁ z)) :=
      ((hF₁d.continuousOn.continuousAt (hU₁o.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hcont.norm (eventually_nhdsWithin_of_forall fun w hw => ?_)
    rw [hF₁eq (hgood ▸ hw)]
    exact hC w hw
  -- step 2: across `N ∩ B'`
  set j : Fin (p + t) := Fin.natAdd p ⟨0, by omega⟩ with hj
  set e : ComplexModel (p + t) := EuclideanSpace.single j 1 with he
  have hloc₂ : ∀ t₀ ∈ N ∩ ball (Λ a).1 δ, ∃ r > 0, ball t₀ r ⊆ ball (Λ a).1 δ ∧
      ∃ h : ComplexModel (p + t) → ℂ, DifferentiableOn ℂ h (ball t₀ r) ∧
        (¬ ∀ᶠ z in 𝓝 t₀, h z = 0) ∧ ∀ z ∈ ball t₀ r, z ∈ N ∩ ball (Λ a).1 δ → h z = 0 := by
    intro t₀ ht₀
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball t₀ ht₀.2
    refine ⟨r, hr, hrsub, fun z => z j,
      (EuclideanSpace.proj j : ComplexModel (p + t) →L[ℂ] ℂ).differentiable.differentiableOn,
      ?_, fun z _ hz => hz.1 j (by simp [hj])⟩
    intro hev
    obtain ⟨r', hr', hr'sub⟩ := Metric.eventually_nhds_iff.mp hev
    have hmem : dist (t₀ + ((r' / 2 : ℝ) : ℂ) • e) t₀ < r' := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, PiLp.norm_single, norm_one,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have := hr'sub hmem
    have ht₀j : t₀ j = 0 := ht₀.1 j (by simp [hj])
    simp only [PiLp.add_apply, PiLp.smul_apply, he, PiLp.single_apply, if_true, smul_eq_mul,
      mul_one, ht₀j, zero_add] at this
    exact absurd this (by exact_mod_cast (half_pos hr').ne')
  have hU₂ : ball (Λ a).1 δ \ (N ∩ ball (Λ a).1 δ) = U₁ := by
    ext z
    simp only [hU₁, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hbdd₂ : ∀ t₀ ∈ N ∩ ball (Λ a).1 δ, ∃ V ∈ 𝓝 t₀, ∃ C', ∀ z ∈ V \ (N ∩ ball (Λ a).1 δ),
      ‖F₁ z‖ ≤ C' := fun t₀ ht₀ =>
    ⟨ball (Λ a).1 δ, isOpen_ball.mem_nhds ht₀.2, C, fun z hz => hF₁C z (hU₂ ▸ hz)⟩
  obtain ⟨F₂, hF₂d, hF₂eq⟩ := RiemannExtensionThin.exists_extension_of_thin
    (hU₂ ▸ hU₁o) (hU₂ ▸ hF₁d) hloc₂ hbdd₂
  refine ⟨F₂, hF₂d, fun w hw => ?_⟩
  rw [hF₂eq (hU₂.symm ▸ hw.1), hF₁eq (hgood ▸ hw)]

end Hironaka.RemmertSteinFlat
