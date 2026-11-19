import Hironaka.Analytic.RiemannExtensionThin
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Riemann extension for continuous maps of complex manifolds

A continuous map between complex manifolds which is holomorphic off a closed analytic subset with
empty interior is holomorphic (Demailly, *Complex analytic and differential geometry*, II.4.2;
blueprint `hironaka-g10-chowside-riemann-extension.tex`).  This is the manifold form, for maps, of
`RiemannExtensionThin.exists_extension_of_thin`: in a chart at a point of the analytic set, every
coordinate of the map is bounded and holomorphic off the thin zero set of a local equation, so it
extends holomorphically, and the extension agrees with the coordinate by continuity and density.

It replaces the finite mapping theorem in the proof of Hironaka's Chow lemma for manifolds: the
lift through a flat strict transform which is a homeomorphism is continuous, holomorphic off the
preimage of the exceptional set, hence holomorphic.

Main declarations:

* `exists_not_mem_of_interior_eq_empty` — chart coordinates of a set with empty interior.
* `mdifferentiableAt_of_continuousOn` — vector-valued Riemann extension at a point.
* `contMDiff_of_continuous_of_isComplexAnalyticSubset` — the map version.
-/

set_option autoImplicit false

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace Hironaka.HironakaG10ChowRiemannExtension

open Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {m : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (ComplexModel m) W]
  [IsComplexManifold m W]

omit [IsComplexManifold m W] in
/-- In the preferred chart at `t`, every nonempty open set of coordinates contains a point whose
inverse image lies outside a given set with empty interior. -/
theorem exists_not_mem_of_interior_eq_empty {A : Set W} (hAi : interior A = ∅) (t : W)
    {V : Set (ComplexModel m)} (hV : IsOpen V) (hVt : V ⊆ (chartAt (ComplexModel m) t).target)
    (hne : V.Nonempty) : ∃ z ∈ V, (chartAt (ComplexModel m) t).symm z ∉ A := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hne
  have hopen : IsOpen ((chartAt (ComplexModel m) t).symm '' V) :=
    (chartAt (ComplexModel m) t).isOpen_image_symm_of_subset_target hV hVt
  have hsub : (chartAt (ComplexModel m) t).symm '' V ⊆ A := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have hmem : (chartAt (ComplexModel m) t).symm z ∈ interior A :=
    interior_maximal hsub hopen ⟨z, hz, rfl⟩
  rw [hAi] at hmem
  exact hmem

/-- **Riemann extension at a point, vector-valued.**  Let `Φ : W → ℂ^d` be continuous on an open
set `O` and holomorphic at the points of `O` off a closed analytic set `A` with empty interior.
Then `Φ` is holomorphic at every point of `O`. -/
theorem mdifferentiableAt_of_continuousOn {d : ℕ} {Φ : W → ComplexModel d} {O A : Set W}
    (hO : IsOpen O) (hΦc : ContinuousOn Φ O) (hA : IsComplexAnalyticSubset (n := m) A)
    (hAc : IsClosed A) (hAi : interior A = ∅)
    (hΦ : ∀ w ∈ O, w ∉ A → MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) Φ w)
    {t : W} (ht : t ∈ O) : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) Φ t := by
  by_cases htA : t ∉ A
  · exact hΦ t ht htA
  obtain ⟨P⟩ := hA t
  set e := chartAt (ComplexModel m) t with he
  have hts : t ∈ e.source := mem_chart_source _ t
  set U : Set (ComplexModel m) := P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' O) with hU
  have hUo : IsOpen U := P.isOpen_coordinateNeighborhood.inter (e.isOpen_inter_preimage_symm hO)
  have hUt : U ⊆ e.target := fun z hz => hz.2.1
  have hetU : e t ∈ U := by
    refine ⟨P.center_mem_coordinateNeighborhood, e.map_source hts, ?_⟩
    change e.symm (e t) ∈ O
    rw [e.left_inv hts]
    exact ht
  set T : Set (ComplexModel m) := U ∩ e.symm ⁻¹' A with hT
  set ψ : ComplexModel m → ComplexModel d := fun z => Φ (e.symm z) with hψ
  have hzero : ∀ z ∈ U, (z ∈ T ↔ ∀ i, P.generator i z = 0) := by
    intro z hz
    have h1 : e.symm z ∈ e.source := e.map_target (hUt hz)
    have h2 : e (e.symm z) = z := e.right_inv (hUt hz)
    have h3 : e.symm z ∈ A ↔ ∀ i, P.generator i (e (e.symm z)) = 0 :=
      P.zeroLocus h1 (by change e (e.symm z) ∈ _; rw [h2]; exact hz.1)
    rw [h2] at h3
    exact ⟨fun h => h3.mp h.2, fun h => ⟨hz, h3.mpr h⟩⟩
  have hthin : ∀ V : Set (ComplexModel m), IsOpen V → V ⊆ U → V.Nonempty → ∃ z ∈ V, z ∉ T := by
    intro V hV hVU hne
    obtain ⟨z, hz, hzA⟩ := exists_not_mem_of_interior_eq_empty hAi t hV (hVU.trans hUt) hne
    exact ⟨z, hz, fun h => hzA h.2⟩
  have hUT : IsOpen (U \ T) := by
    have hset : U \ T = U ∩ (e.target ∩ e.symm ⁻¹' Aᶜ) := by
      ext z
      constructor
      · rintro ⟨hz, hzT⟩
        exact ⟨hz, hUt hz, fun hA' => hzT ⟨hz, hA'⟩⟩
      · rintro ⟨hz, -, hzA⟩
        exact ⟨hz, fun h => hzA h.2⟩
    rw [hset]
    exact hUo.inter (e.isOpen_inter_preimage_symm hAc.isOpen_compl)
  have hψc : ContinuousOn ψ U :=
    hΦc.comp (e.continuousOn_symm.mono hUt) (fun z hz => hz.2.2)
  have hψd : DifferentiableOn ℂ ψ (U \ T) := by
    intro z hz
    have hzt : z ∈ e.target := hUt hz.1
    have hw : e.symm z ∈ O := hz.1.2.2
    have hwA : e.symm z ∉ A := fun h => hz.2 ⟨hz.1, h⟩
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) e.symm z :=
      ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt (e.open_target.mem_nhds hzt)).mdifferentiableAt
        (by simp)
    have h2 := (hΦ _ hw hwA).comp z h1
    exact (mdifferentiableAt_iff_differentiableAt.mp h2).differentiableWithinAt
  have hdense : U ⊆ closure (U \ T) := by
    intro z hz
    rw [_root_.mem_closure_iff]
    intro o ho hzo
    obtain ⟨w, hw, hwT⟩ := hthin (o ∩ U) (ho.inter hUo) inter_subset_right ⟨z, hzo, hz⟩
    exact ⟨w, hw.1, hw.2, hwT⟩
  have hcoord : ∀ j : Fin d, DifferentiableOn ℂ (fun z => ψ z j) U := by
    intro j
    have hfj : DifferentiableOn ℂ (fun z => ψ z j) (U \ T) :=
      (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable.comp_differentiableOn hψd
    have hloc : ∀ t' ∈ T, ∃ r > 0, ball t' r ⊆ U ∧ ∃ h : ComplexModel m → ℂ,
        DifferentiableOn ℂ h (ball t' r) ∧ (¬ ∀ᶠ z in 𝓝 t', h z = 0) ∧
          ∀ z ∈ ball t' r, z ∈ T → h z = 0 := by
      intro t' ht'
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo t' ht'.1
      have hgen : ∃ i, ¬ ∀ᶠ z in 𝓝 t', P.generator i z = 0 := by
        by_contra hcon
        push Not at hcon
        have hall : ∀ᶠ z in 𝓝 t', ∀ i, P.generator i z = 0 := Filter.eventually_all.mpr hcon
        obtain ⟨V, hVsub, hVo, ht'V⟩ := _root_.mem_nhds_iff.mp (hall.and (hUo.mem_nhds ht'.1))
        obtain ⟨z, hzV, hzT⟩ := hthin V hVo (fun z hz => (hVsub hz).2) ⟨t', ht'V⟩
        exact hzT ((hzero z (hVsub hzV).2).mpr (hVsub hzV).1)
      obtain ⟨i, hi⟩ := hgen
      refine ⟨r, hr, hrU, P.generator i,
        (P.generator_holomorphic i).mono (fun z hz => (hrU hz).1), hi, ?_⟩
      intro z hz hzT
      exact (hzero z (hrU hz)).mp hzT i
    have hbdd : ∀ t' ∈ T, ∃ V ∈ 𝓝 t', ∃ C, ∀ z ∈ V \ T, ‖(fun z => ψ z j) z‖ ≤ C := by
      intro t' ht'
      have hcont : ContinuousAt (fun z => ψ z j) t' :=
        (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.continuousAt.comp
          (hψc.continuousAt (hUo.mem_nhds ht'.1))
      exact ⟨_, hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖ψ t' j‖)), ‖ψ t' j‖ + 1,
        fun z hz => le_of_lt hz.1⟩
    obtain ⟨G, hG, hGeq⟩ := RiemannExtensionThin.exists_extension_of_thin hUT hfj hloc hbdd
    have heq : EqOn G (fun z => ψ z j) U :=
      hGeq.of_subset_closure hG.continuousOn
        ((EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_continuousOn hψc) sdiff_subset hdense
    exact hG.congr (fun z hz => (heq hz).symm)
  have hψt : DifferentiableAt ℂ ψ (e t) :=
    (differentiableAt_piLp _).mpr (fun j => (hcoord j).differentiableAt (hUo.mem_nhds hetU))
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) e t :=
    ((contMDiffOn_chart (n := ∞)).contMDiffAt (e.open_source.mem_nhds hts)).mdifferentiableAt
      (by simp)
  have h3 := hψt.mdifferentiableAt.comp t h1
  apply h3.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hts] with w hw
  change Φ w = Φ (e.symm (e w))
  rw [e.left_inv hw]

/-- **Riemann extension for continuous maps of complex manifolds.**  A continuous map `g : W → Y`
of complex manifolds which is holomorphic at every point off a closed analytic subset `A ⊆ W` with
empty interior is holomorphic. -/
theorem contMDiff_of_continuous_of_isComplexAnalyticSubset {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {g : W → Y}
    (hg : Continuous g) {A : Set W} (hA : IsComplexAnalyticSubset (n := m) A) (hAc : IsClosed A)
    (hAi : interior A = ∅)
    (hgA : ∀ w, w ∉ A → MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) g w) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g := by
  intro t
  set O : Set W := g ⁻¹' (chartAt (ComplexModel n) (g t)).source with hOdef
  have hO : IsOpen O := (chartAt (ComplexModel n) (g t)).open_source.preimage hg
  have hΦc : ContinuousOn (fun w => extChartAt 𝓘(ℂ, ComplexModel n) (g t) (g w)) O :=
    (continuousOn_extChartAt (g t)).comp hg.continuousOn (fun w hw => by
      rw [extChartAt_source]
      exact hw)
  have hΦ : ∀ w ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n)
      (fun w => extChartAt 𝓘(ℂ, ComplexModel n) (g t) (g w)) w := by
    intro w hw
    refine mdifferentiableAt_of_continuousOn hO hΦc hA hAc hAi ?_ hw
    intro w' hw' hw'A
    exact (mdifferentiableAt_extChartAt hw').comp w' (hgA w' hw'A)
  rw [contMDiffAt_iff_target]
  refine ⟨hg.continuousAt, ?_⟩
  apply contMDiffAt_of_eventually_mdifferentiableAt
  filter_upwards [hO.mem_nhds (mem_chart_source _ (g t))] with w hw
  exact hΦ w hw

end

end Hironaka.HironakaG10ChowRiemannExtension
