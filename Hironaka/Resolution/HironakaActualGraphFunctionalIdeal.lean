/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHolomorphicGraphIdeal
import Hironaka.Resolution.HironakaActualCylinderPullbackPoints

/-!
# The entire original functional ideal of an actual graph at every graph point

The independent graph vanishing ideal is transported through actual original
translations, retaining the entire infinite base function family and literal
finite graph equations. No coherence or ideal equality is input.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualGraphFunctionalIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm RelativePrincipalizationSpan
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualHolomorphicGraphIdeal
  HironakaActualCylinderPullbackOrigin HironakaActualCylinderPullbackPoints
variable {d t : ℕ}

/-- The literal finite original graph equation, before taking any germs. -/
def graphFunction (f : ComplexModel d → ComplexModel t) (i : Fin t) : ComplexModel (d+t) → ℂ :=
  fun z => z (i.natAdd d) - f (tangentProjection d t z) i

/-- ALL original base vanishing pullbacks together with the literal finite graph equations. -/
def graphFunctionFamily (f : ComplexModel d → ComplexModel t) (W : Set (ComplexModel d))
    (x : ComplexModel d) : (ComplexModel (d+t) → ℂ) → Prop :=
  fun s => (∃ a : ComplexModel d → ℂ,(vanishingIdeal (n := d) W).mem x a ∧ s=a∘tangentProjection d t) ∨
    ∃ i : Fin t,s=graphFunction f i

private theorem ordinaryHol {n : ℕ} {F : ComplexModel n → ℂ} (hF : HolomorphicAt n F 0) :
    ∀ᶠ z in nhds (0 : ComplexModel n),DifferentiableAt ℂ F z :=
  hF.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mp hz

private theorem graph_function_holomorphic (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (i : Fin t) :
    HolomorphicAt (d+t) (graphFunction f i) 0 := by
  have hp : Tendsto (tangentProjection d t) (nhds 0) (nhds 0) := by
    simpa using (tangentProjection d t).continuous.tendsto 0
  exact (hp.eventually hf).mono fun z hz =>
    ((EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.sub
      ((EuclideanSpace.proj i : ComplexModel t →L[ℂ] ℂ).differentiableAt.comp z
        (hz.comp z (tangentProjection d t).differentiableAt))).mdifferentiableAt

private theorem graph_family_holomorphic (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (W : Set (ComplexModel d)) :
    ∀ s,graphFunctionFamily f W 0 s → HolomorphicAt (d+t) s 0 := by
  rintro s (⟨a,ha,rfl⟩|⟨i,rfl⟩)
  · have hh : HolomorphicAt d a (tangentProjection d t 0) := by simpa only [map_zero] using ha.1
    exact hh.comp_contMDiff (Eventually.of_forall fun z => (tangentProjection d t).contDiff.contMDiff.contMDiffAt)
  · exact graph_function_holomorphic f hf i

private theorem graph_function_germ (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (i : Fin t) :
    HolGerm.mk (graphFunction f i) (ordinaryHol (graph_function_holomorphic f hf i)) = graphRelation f hf i := rfl

private theorem graph_function_family_germ_span_eq (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (W : Set (ComplexModel d)) :
    actualFunctionGermSpan (graphFunctionFamily f W 0) (graph_family_holomorphic f hf W) =
      Ideal.map (tangentPullback d t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W) ⊔
        graphRelations f hf := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨a,ha,rfl⟩|⟨i,rfl⟩ := hs
    · apply Ideal.mem_sup_left
      have hg : HolGerm.mk a (ordinaryHol ha.1) ∈ AnalyticGermDecomposition.vanishingIdeal W :=
        AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr ha.2
      exact Ideal.mem_map_of_mem (tangentPullback d t).toRingHom hg
    · apply Ideal.mem_sup_right
      exact Ideal.subset_span ⟨i,rfl⟩
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      obtain ⟨a,ha,rfl⟩ := HolGerm.exists_eq_mk g
      have hm : (vanishingIdeal (n := d) W).mem 0 a :=
        ⟨ha.mono (fun _ hz => hz.mdifferentiableAt),AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg⟩
      exact Ideal.subset_span ⟨a∘tangentProjection d t,Or.inl ⟨a,hm,rfl⟩,rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Ideal.subset_span ⟨graphFunction f i,Or.inr ⟨i,rfl⟩,rfl⟩

/-- ENTIRE independently defined original functional graph membership at the actual origin. -/
theorem graph_functional_mem_zero_iff (f : ComplexModel d → ComplexModel t)
    (hf : ∀ᶠ x in nhds 0,DifferentiableAt ℂ f x) (h0 : f 0=0)
    (W : Set (ComplexModel d)) (F : ComplexModel (d+t) → ℂ) :
    (vanishingIdeal (n := d+t) (graphCarrier f W)).mem 0 F ↔
      IsInSpanAt (n := d+t) (graphFunctionFamily f W 0) 0 F := by
  constructor
  · intro hF
    apply (isInSpanAt_zero_iff_mem_actual_germ_span _ (graph_family_holomorphic f hf W) F (ordinaryHol hF.1)).mpr
    rw [graph_function_family_germ_span_eq f hf W,← graph_vanishingIdeal_eq f hf h0 W]
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr hF.2
  · intro hF
    have hg := (isInSpanAt_zero_iff_mem_actual_germ_span _ (graph_family_holomorphic f hf W) F (ordinaryHol hF.1)).mp hF
    rw [graph_function_family_germ_span_eq f hf W,← graph_vanishingIdeal_eq f hf h0 W] at hg
    exact ⟨hF.1,AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg⟩

/-- The actual original centred function, obtained by literal translations. -/
def recenteredGraphFunction (f : ComplexModel d → ComplexModel t) (x : ComplexModel d) :
    ComplexModel d → ComplexModel t := fun u => f (u+x)-f x

/-- The literal graph itself commutes with the genuine original translation. -/
theorem translated_graph_eq (f : ComplexModel d → ComplexModel t) (W : Set (ComplexModel d))
    (x : ComplexModel d) :
    translatedSet (graphSection f x) (graphCarrier f W) =
      graphCarrier (recenteredGraphFunction f x) (translatedSet x W) := by
  ext z
  change (tangentProjection d t (z+graphSection f x) ∈ W ∧
      actualJointNormalProjection d t (z+graphSection f x) = f (tangentProjection d t (z+graphSection f x))) ↔
    tangentProjection d t z+x ∈ W ∧
      actualJointNormalProjection d t z = f (tangentProjection d t z+x)-f x
  simp only [map_add,projection_graphSection,normalProjection_graphSection,eq_sub_iff_add_eq]

private theorem translated_graphFunction (f : ComplexModel d → ComplexModel t)
    (x : ComplexModel d) (i : Fin t) :
    graphFunction f i ∘ (fun z => z+graphSection f x) = graphFunction (recenteredGraphFunction f x) i := by
  funext z
  simp only [graphFunction,Function.comp_apply,map_add,projection_graphSection,recenteredGraphFunction]
  simp [graphSection]
  ring

/-- The ENTIRE original generator family, including all base functions, commutes with actual recentering. -/
theorem translated_graph_function_family_eq (f : ComplexModel d → ComplexModel t)
    (W : Set (ComplexModel d)) (x : ComplexModel d) :
    translatedFamily (graphSection f x) (graphFunctionFamily f W x) =
      graphFunctionFamily (recenteredGraphFunction f x) (translatedSet x W) 0 := by
  funext s
  apply propext
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩|⟨i,rfl⟩ := ha
    · left
      refine ⟨b∘(fun u => u+x),(vanishingIdeal_translation_iff x W b).mp hb,?_⟩
      funext z
      simp only [Function.comp_def,map_add,projection_graphSection]
    · exact Or.inr ⟨i,translated_graphFunction f x i⟩
  · rintro (⟨b,hb,rfl⟩|⟨i,rfl⟩)
    · let a : ComplexModel d → ℂ := fun u => b (u-x)
      have ha : (vanishingIdeal (n := d) W).mem x a := by
        apply (vanishingIdeal_translation_iff x W a).mpr
        simpa only [a,Function.comp_def,add_sub_cancel_right] using hb
      refine ⟨a∘tangentProjection d t,Or.inl ⟨a,ha,rfl⟩,?_⟩
      funext z
      simp only [a,Function.comp_def,map_add,projection_graphSection,add_sub_cancel_right]
    · exact ⟨graphFunction f i,Or.inr ⟨i,rfl⟩,(translated_graphFunction f x i).symm⟩

/-- ENTIRE independently defined original functional graph membership at EVERY actual graph point. -/
theorem graph_functional_mem_iff (f : ComplexModel d → ComplexModel t)
    (x : ComplexModel d) (hf : ∀ᶠ u in nhds x,DifferentiableAt ℂ f u)
    (W : Set (ComplexModel d)) (F : ComplexModel (d+t) → ℂ) :
    (vanishingIdeal (n := d+t) (graphCarrier f W)).mem (graphSection f x) F ↔
      IsInSpanAt (n := d+t) (graphFunctionFamily f W x) (graphSection f x) F := by
  have ht : Tendsto (fun u : ComplexModel d => u+x) (nhds 0) (nhds x) := by
    have hc : Continuous (fun u : ComplexModel d => u+x) := continuous_id.add continuous_const
    simpa only [zero_add] using hc.tendsto (0 : ComplexModel d)
  have hfc : ∀ᶠ u in nhds 0,DifferentiableAt ℂ (recenteredGraphFunction f x) u := by
    filter_upwards [ht.eventually hf] with u hu
    exact (hu.comp u (differentiableAt_id.add_const x)).sub_const (f x)
  have hc0 : recenteredGraphFunction f x 0=0 := by simp [recenteredGraphFunction]
  rw [vanishingIdeal_translation_iff,translated_graph_eq,
    graph_functional_mem_zero_iff _ hfc hc0]
  have hs := isInSpanAt_translation_iff (graphSection f x) (graphFunctionFamily f W x) F
  rw [translated_graph_function_family_eq] at hs
  exact hs.symm

end
end Hironaka.HironakaActualGraphFunctionalIdeal
