import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Submersion
import Hironaka.Blowup.BlowupTowers
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v w t
namespace Hironaka.G3UniverseSubmersionConjugate
open BlowupTowers
noncomputable section
variable {n m : ℕ}
private theorem pulledChart_maximal {A : CMfd.{u} n} {B : CMfd.{v} n}
    (β : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (e : OpenPartialHomeomorph A (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A) :
    β.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ B := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (e ∘ β) (univ ∩ β ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      β.contMDiff.contMDiffOn (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (β.symm ∘ e.symm) (e.target ∩ e.symm ⁻¹' univ)
    exact β.symm.contMDiff.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)

/-- Actual conjugated submersions retain the genuine globally chosen complement and real charts. -/
theorem isSubmersion_conjugate {A : CMfd.{u} n} {A' : CMfd.{v} n} {B : CMfd.{w} m} {B' : CMfd.{t} m}
    (a : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : B' ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ B)
    {f : B → A} (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (a.symm ∘ f ∘ b) := by
  apply Manifold.IsSubmersionOfComplement.isSubmersion (F := hf.complement)
  intro z
  let h := hf.isSubmersionOfComplement_complement (b z)
  let d := b.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  let c := a.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv d c
  · exact ⟨mem_univ _,h.mem_domChart_source⟩
  · exact ⟨mem_univ _,by simpa using h.mem_codChart_source⟩
  · exact pulledChart_maximal b h.domChart h.domChart_mem_maximalAtlas
  · exact pulledChart_maximal a h.codChart h.codChart_mem_maximalAtlas
  · intro w hw
    exact ⟨mem_univ _,by simpa using h.source_subset_preimage_source hw.2⟩
  · intro w hw
    have hw' : w ∈ (h.domChart.extend 𝓘(ℂ, ComplexModel m)).target := by
      simpa [d,OpenPartialHomeomorph.extend,mfld_simps] using hw
    have he := h.writtenInCharts hw'
    simpa [d,c,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps] using he


/-- A biholomorphism between possibly different universes is a submersion. -/
theorem diffeo_isSubmersion {A : CMfd.{u} n} {B : CMfd.{v} n}
    (e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e := by
  have h := isSubmersion_conjugate (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) e
    (Manifold.IsSubmersion.id (I := 𝓘(ℂ,ComplexModel n)) (n := ∞) (M := A))
  simpa using h


end
end Hironaka.G3UniverseSubmersionConjugate
