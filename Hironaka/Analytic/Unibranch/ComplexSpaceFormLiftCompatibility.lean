import Hironaka.Analytic.Unibranch.ComplexSpaceFormDomainPullback

/-! Genuine tensor independence for holomorphic probes of the original
singular complex space. Primitive actual point coherence, no form-equality
or desired pullback certificate. Blueprint: complex-space-form-pullback.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
namespace Hironaka.Analytic.Unibranch.SpaceForm

private theorem pullback_germ_eq {m N k : ℕ}
    {F G : ComplexModel m → ComplexModel N} {z : ComplexModel m}
    (h : F =ᶠ[𝓝 z] G) (v : AmbientForm N k) :
    pullbackForm F v z = pullbackForm G v z := by
  simp only [pullbackForm,h.self_of_nhds,h.fderiv_eq]

/-- The original singular-chart tensor compatibility identifies all actual
holomorphic probes with the SAME original point image. -/
theorem pullback_eq_of_compatible_points {X : SourceReducedComplexSpace} {k m : ℕ}
    (θ : SpaceForm X k) (i j : θ.ι) {D : Set (ComplexModel m)} (hD : IsOpen D)
    {G : ComplexModel m → ComplexModel (θ.chart i).dim}
    {H : ComplexModel m → ComplexModel (θ.chart j).dim}
    (hG : DifferentiableOn ℂ G D) (_hH : DifferentiableOn ℂ H D)
    (hpoints : ∀ z ∈ D, ∃ (a : (θ.chart i).carrier) (b : (θ.chart j).carrier),
      a.val.val = G z ∧ b.val.val = H z ∧ (θ.chart i).toPoint a = (θ.chart j).toPoint b)
    {z : ComplexModel m} (hz : z ∈ D) :
    pullbackForm G (θ.rep i) z = pullbackForm H (θ.rep j) z := by
  obtain ⟨a,b,ha,hb,hab⟩ := hpoints z hz
  obtain ⟨W,T,haW,hT⟩ := (θ.chart i).exists_isTransition (θ.chart j) a ⟨b,hab.symm⟩
  let E : Set (ComplexModel m) := D ∩ G ⁻¹' W
  have hE : IsOpen E := hG.continuousOn.isOpen_inter_preimage hD hT.1
  have hzE : z ∈ E := ⟨hz,by change G z ∈ W; rw [← ha]; exact haW⟩
  have hmaps : ∀ w ∈ E, G w ∈ W ∧ ∃ a : (θ.chart i).carrier, a.val.val = G w := by
    intro w hw
    obtain ⟨a',-,ha',-⟩ := hpoints w hw.1
    exact ⟨hw.2,a',ha'⟩
  have hvan := θ.compatible i j W T hT m E G hE (hG.mono inter_subset_left) hmaps z hzE
  rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero] at hvan
  have heq : (T ∘ G) =ᶠ[𝓝 z] H := by
    filter_upwards [hE.mem_nhds hzE] with w hw
    obtain ⟨a',b',ha',hb',hab'⟩ := hpoints w hw.1
    obtain ⟨c,hc,hpc⟩ := hT.2.2.2.2 a' (by rw [ha']; exact hw.2)
    have hcb : c = b' := (θ.chart j).toPoint_injective (hpc.trans hab')
    change T (G w) = H w
    rw [← ha',← hc,hcb,hb']
  have hGr : DifferentiableAt ℝ G z :=
    (hG.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hTr : DifferentiableAt ℝ T (G z) :=
    (hT.2.2.1.differentiableAt (hT.1.mem_nhds hzE.2)).restrictScalars ℝ
  exact hvan.trans ((pullbackForm_comp hGr hTr (θ.rep j)).trans (pullback_germ_eq heq _))

end Hironaka.Analytic.Unibranch.SpaceForm
