/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticVertexCoefficientData
import Hironaka.Support.RealDomainOriginDictionaryExact

/-! True analytic monic origin generators generate the entire same original sheaf near the origin. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticNearbyVertexGenerators
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations OkaCoherence
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaSmoothCentreRealDomainInitialRelations HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalIdeal
  HironakaActualAnalyticVertexCoefficientData

/-- Entire finite original germ generation spreads genuine representative functions to ALL nearby stalks. -/
theorem exists_actual_nearby_representatives_of_origin_span {n : ℕ} {ι : Type} [Fintype ι]
    (A : GermIdeal n (ComplexModel n)) (hA : IdealFGAt A.mem 0)
    (G : ι → HolGerm (ComplexModel n)) (hspan : Ideal.span (range G)=originalCoherentOriginIdeal A) :
    ∃ (g : ι → ComplexModel n → ℂ) (hg : ∀ i,HolAt (g i) 0),
      (∀ i,HolGerm.mk (g i) (hg i)=G i) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        (∀ i,DifferentiableOn ℂ (g i) U) ∧
        ∀ y ∈ U,∀ f,A.mem y f ↔ InSpanAt g y f := by
  choose g hg hG using fun i => HolGerm.exists_eq_mk (G i)
  have hGs : (fun i => HolGerm.mk (g i) (hg i))=G := funext fun i => (hG i).symm
  have hspan' : Ideal.span (range fun i => HolGerm.mk (g i) (hg i))=originalCoherentOriginIdeal A := by
    rw [hGs,hspan]
  have hnear : ∀ᶠ y in 𝓝 (0 : ComplexModel n),∀ i,HolAt (g i) y :=
    eventually_all.mpr fun i => (show HolAt (g i) (0 : ComplexModel n) from hg i).eventually
  obtain ⟨V,hVsub,hV,h0V⟩ := mem_nhds_iff.mp hnear
  have hreg (i : ι) : DifferentiableOn ℂ (g i) V :=
    fun y hy => (hVsub hy i).self_of_nhds.differentiableWithinAt
  have hJ : IdealFGAt (fun y f => InSpanAt g y f) 0 :=
    ⟨V,hV,h0V,ι,inferInstance,g,hreg,fun _ _ _ => Iff.rfl⟩
  have hAhol (f : ComplexModel n → ℂ) (hf : A.mem 0 f) : HolAt f 0 := by
    obtain ⟨U,_hU,h0U,κ,hκ,s,_hs,hgen⟩ := hA
    let := hκ
    exact ((hgen 0 h0U f).mp hf).1
  have h0 (f : ComplexModel n → ℂ) : A.mem 0 f ↔ InSpanAt g 0 f := by
    by_cases hf : HolAt f 0
    · rw [← mk_mem_originalOriginIdeal_iff_of_local A hA hf,← hspan']
      exact (inSpanAt_zero_iff_mem_origin_span g hg hf).symm
    · exact ⟨fun h => (hf (hAhol f h)).elim,fun h => (hf h.1).elim⟩
  obtain ⟨U,hU,h0U,he⟩ := exists_open_coherent_equality hA hJ h0
  refine ⟨g,hg,fun i => (hG i).symm,U∩V,hU.inter hV,⟨h0U,h0V⟩,?_,?_⟩
  · exact fun i => (hreg i).mono inter_subset_right
  · exact fun y hy => he y hy.1

/-- ONLY original real-open coherence supplies SAME analytic vertices, functions and all nearby original stalks. -/
theorem exists_actual_original_nearby_vertex_coefficient_data (k s t : ℕ)
    (A : GermIdeal ((k+s)+t) (ComplexModel ((k+s)+t)))
    (W : Set (ComplexModel ((k+s)+t))) (hW : IsOpen W) (h0W : (0 : ComplexModel ((k+s)+t)) ∈ W)
    (hA : CoherentOn A W) :
    ∃ P : ActualAnalyticVertexCoefficientData k s t (originalCoherentOriginIdeal A),
      ∃ (g : HironakaActualFormalInitialDiagram.actualInitialVertices MonomialOrder.degLex
          (Ideal.map (HironakaActualCoefficientPresentationCentrePower.actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom
            (originalCoherentOriginIdeal A)) → ComplexModel ((k+s)+t) → ℂ)
        (hg : ∀ a,HolAt (g a) 0),
        (∀ a,HolGerm.mk (g a) (hg a)=P.generator a) ∧
        ∃ U : Set (ComplexModel ((k+s)+t)), IsOpen U ∧ (0 : ComplexModel ((k+s)+t)) ∈ U ∧ U ⊆ W ∧
          MapsTo (tangentProjection (k+s) t) U P.domain ∧
          (∀ a,MDifferentiableOn 𝓘(ℂ,ComplexModel ((k+s)+t)) 𝓘(ℂ,ℂ) (g a) U) ∧
          ∀ y ∈ U,∀ f,A.mem y f ↔ InSpanAt g y f := by
  obtain ⟨P⟩ := nonempty_actualAnalyticVertexCoefficientData k s t (originalCoherentOriginIdeal A)
  have hfg := idealFGAt_of_coherentOn A W hA h0W
  obtain ⟨g,hg,hG,U,hU,h0U,hreg,hgen⟩ :=
    exists_actual_nearby_representatives_of_origin_span A hfg P.generator P.generates
  let V := (tangentProjection (k+s) t) ⁻¹' P.domain
  have hV : IsOpen V := P.isOpen_domain.preimage (tangentProjection (k+s) t).continuous
  have h0V : (0 : ComplexModel ((k+s)+t)) ∈ V := by
    simpa only [V,mem_preimage,map_zero] using P.zero_mem_domain
  refine ⟨P,g,hg,hG,(U∩W)∩V,(hU.inter hW).inter hV,⟨⟨h0U,h0W⟩,h0V⟩,
    fun y hy => hy.1.2,fun y hy => hy.2,?_,?_⟩
  · intro a
    exact mdifferentiableOn_iff_differentiableOn.mpr ((hreg a).mono fun y hy => hy.1.1)
  · exact fun y hy => hgen y hy.1.1

end
end Hironaka.HironakaActualAnalyticNearbyVertexGenerators
