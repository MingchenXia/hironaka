/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRetractContactLocalization

/-!
# Every original singular strict transform through the same actual contact

The literal closed contact-stratum inclusion transports whole strict closures
of EVERY subset. Original true-open graph data internally supply the genuine
lower blowup and all simultaneous strict-image identities. Intrinsic ideal
restriction and canonical marked/history comparison remain separate.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualContactStrictTransform
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupStrictSubmanifold HironakaActualRetractContactLocalization
  HironakaActualLocalCommonGraphModel HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceRegularityConverse
  CategoryTheory AlgebraicGeometry
variable {d : ℕ} {X A Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [IsComplexManifold d X] [TopologicalSpace A] [ChartedSpace (ComplexModel (d+1)) A]
  [IsComplexManifold (d+1) A] [TopologicalSpace Y]

omit [IsComplexManifold d X] in
/-- The SAME actual closed contact inclusion transports whole strict transforms of EVERY original subset. -/
theorem strictTransform_image (s : X → A) (p : A → X)
    (hs : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ s)
    (hp : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ p)
    (hps : p∘s=id) (π : Y → A) (hπ : Continuous π) (D W : Set X) :
    (Subtype.val : geoStrictTransform π (s '' D) (range s) → Y) ''
        geoStrictTransform (restrictedProjection s p π D) D W=
      geoStrictTransform π (s '' D) (s '' W) := by
  let S := geoStrictTransform π (s '' D) (range s)
  let σ := restrictedProjection s p π D
  let j : S → Y := Subtype.val
  have hfactor (z : S) : π z.val=s (σ z) := by
    obtain ⟨x,hx⟩ := geoStrictTransform_subset_preimage hπ
      (range_section_closed s p hs hp hps) z.property
    change π z.val=s (p (π z.val))
    rw [← hx]
    exact congrArg s (congrFun hps x).symm
  have himage : j '' (σ ⁻¹' (W\D))=π ⁻¹' ((s '' W)\(s '' D)) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change π z.val∈s '' W ∧ π z.val∉s '' D
      refine ⟨⟨σ z,hz.1,(hfactor z).symm⟩,?_⟩
      rintro ⟨x,hxD,he⟩
      have hxe : x=σ z := by
        have ht := congrArg p (he.trans (hfactor z))
        have hx : p (s x)=x := congrFun hps x
        have hz' : p (s (σ z))=σ z := congrFun hps (σ z)
        simpa only [hx,hz'] using ht
      exact hz.2 (hxe ▸ hxD)
    · rintro ⟨⟨x,hxW,he⟩,hyD⟩
      have hyS : y∈S := subset_closure ⟨⟨x,he⟩,hyD⟩
      refine ⟨⟨y,hyS⟩,?_,rfl⟩
      have hσ : σ ⟨y,hyS⟩=x := by
        change p (π y)=x
        rw [← he]
        exact congrFun hps x
      change σ ⟨y,hyS⟩∈W ∧ σ ⟨y,hyS⟩∉D
      rw [hσ]
      exact ⟨hxW,fun hxD => hyD ⟨x,hxD,he⟩⟩
  change j '' closure (σ ⁻¹' (W\D))=closure (π ⁻¹' ((s '' W)\(s '' D)))
  calc
    j '' closure (σ ⁻¹' (W\D))=closure (j '' (σ ⁻¹' (W\D))) :=
      ((isClosed_closure : IsClosed S).isClosedEmbedding_subtypeVal.closure_image_eq _).symm
    _=closure (π ⁻¹' ((s '' W)\(s '' D))) := congrArg closure himage

private theorem graph_section_holo (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U) :
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ (openGraphSection U f) := by
  have hf' : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel 1) ∞ (fun x : U => f x.val) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt)
  apply (ContMDiff.subtypeVal_comp_iff (firstWideDomain U) _).mp
  exact ((tangentInclusion d 1).contMDiff.comp contMDiff_subtype_val).add
    ((actualJointNormalInclusion d 1).contMDiff.comp hf')

private theorem graph_projection_holo (U : Opens (ComplexModel d)) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel d) ∞ (openGraphProjection U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (tangentProjection d 1).contMDiff.comp contMDiff_subtype_val

private theorem graph_projection_section (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) : openGraphProjection U∘openGraphSection U f=id := by
  funext x
  apply Subtype.ext
  simp [openGraphProjection,openGraphSection,tangentProjection_tangentInclusion]

private theorem graph_range (U : Opens (ComplexModel d)) (f : ComplexModel d → ComplexModel 1) :
    range (openGraphSection U f)=firstGraphSubset U f univ := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    constructor
    · exact mem_univ _
    · simp [openGraphSection,tangentProjection_tangentInclusion]
  · intro hz
    refine ⟨openGraphProjection U z,?_⟩
    apply Subtype.ext
    change tangentInclusion d 1 (tangentProjection d 1 z.val)+
      actualJointNormalInclusion d 1 (f (tangentProjection d 1 z.val))=z.val
    rw [← hz.2]
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

private theorem graph_regular (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ z∈range (openGraphSection U f),RegularAtDim (n := d+1) (range (openGraphSection U f)) z d := by
  have hm : ∀ x∈(univ : Set U),openGraphSection U f x∈firstGraphSubset U f univ := by
    intro x _hx
    rw [← graph_range U f]
    exact ⟨x,rfl⟩
  let : IsIso (actualSubspaceMap (graph_section_holo U f hf) hm) := by
    change IsIso (firstGraphModelIso U f hf univ).hom
    infer_instance
  intro z hz
  obtain ⟨x,rfl⟩ := hz
  rw [graph_range U f]
  exact regularAtDim_of_holomorphic_model_open_immersion (graph_section_holo U f hf) hm x

/-- ORIGINAL true-open graph data supply a genuine lower blowup and SIMULTANEOUS whole strict-image equalities for EVERY subset. -/
theorem openGraph_exists_restrictedBlowup_strictTransforms (U : Opens (ComplexModel d))
    (f : ComplexModel d → ComplexModel 1) (hf : ContDiffOn ℂ ∞ f U)
    (D : Set U) (hD : IsClosedSubmanifold d D) (hDint : interior D=∅)
    [ChartedSpace (ComplexModel (d+1)) Y] [IsComplexManifold (d+1) Y]
    {π : Y → firstWideDomain (m := 1) U}
    (hπ : IsBlowupAlong (d+1) (openGraphSection U f '' D) π) :
    let S := geoStrictTransform π (openGraphSection U f '' D) (range (openGraphSection U f))
    ∃ (_ : ChartedSpace (ComplexModel d) S) (_ : IsComplexManifold d S),
      IsBlowupAlong d D (restrictedProjection (openGraphSection U f) (openGraphProjection U) π D) ∧
      ∀ W : Set U,(Subtype.val : S → Y) ''
        geoStrictTransform (restrictedProjection (openGraphSection U f) (openGraphProjection U) π D) D W=
          geoStrictTransform π (openGraphSection U f '' D) (openGraphSection U f '' W) := by
  let cs := strictChartedSpace (openGraphSection U f) (openGraphProjection U)
    (graph_section_holo U f hf) (graph_projection_holo U) (graph_projection_section U f)
    (graph_regular U f hf) hπ
  have hm := strict_isComplexManifold (openGraphSection U f) (openGraphProjection U)
    (graph_section_holo U f hf) (graph_projection_holo U) (graph_projection_section U f)
    (graph_regular U f hf) hπ
  have hb := openGraph_restrictedProjection_isBlowupAlong U f hf D hD hDint hπ
  refine ⟨cs,hm,hb,?_⟩
  intro W
  exact strictTransform_image (openGraphSection U f) (openGraphProjection U)
    (graph_section_holo U f hf) (graph_projection_holo U) (graph_projection_section U f)
    π hπ.contMDiff.continuous D W

end
end Hironaka.HironakaActualContactStrictTransform
