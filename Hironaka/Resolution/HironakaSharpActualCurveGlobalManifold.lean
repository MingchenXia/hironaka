/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveOriginalRecipeAtlas

/-! The original-only actual sharp atlas constructs its genuine global
complex manifold and proper holomorphic projection. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalManifold
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic
  NormalCrossings
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

theorem endpointSpace_t2 (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) : T2Space (endpointGluedSpace A) :=
  t2Space_of_actual_saturated_projection_atlas (gluedProjection A) (gluedProjection A).continuous
    A.openSet hcover (endpointLocalInclusion A) (endpointLocalInclusion_openEmbedding A) (localInclusion_range A)

theorem endpointSpace_secondCountable (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) : SecondCountableTopology (endpointGluedSpace A) :=
  secondCountable_of_actual_saturated_projection_atlas (gluedProjection A) A.openSet hcover
    (endpointLocalInclusion A) (endpointLocalInclusion_openEmbedding A) (localInclusion_range A)

@[instance_reducible]
def endpointChartedSpace (A : ActualEndpointHistories X J) :
    ChartedSpace (ComplexModel n) (endpointGluedSpace A) :=
  actualLiftedTerminalChartedSpace n (endpointLocalInclusion A) (endpointLocalInclusion_openEmbedding A)
    (endpointLocalInclusion_jointly_surjective A)

attribute [local instance] endpointChartedSpace

theorem endpointSpace_isComplexManifold (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) :
    letI := endpointChartedSpace A
    IsComplexManifold n (endpointGluedSpace A) := by
  let := endpointChartedSpace A
  have : T2Space (endpointGluedSpace A) := endpointSpace_t2 A hcover
  have : SecondCountableTopology (endpointGluedSpace A) := endpointSpace_secondCountable A hcover
  have : IsManifold 𝓘(ℂ,ComplexModel n) ∞ (endpointGluedSpace A) :=
    actualLiftedTerminalChartedSpace_isManifold (endpointLocalInclusion A)
      (endpointLocalInclusion_openEmbedding A) (endpointLocalInclusion_jointly_surjective A)
      (embeddingTransition A) (embeddingTransition_inclusion A)
  exact {}

/-- The actual topology and charts, with genuinely proved separation and countability. -/
def endpointManifold (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) : CMfd.{u} n :=
  letI := endpointChartedSpace A
  letI := endpointSpace_isComplexManifold A hcover
  CMfd.of (endpointGluedSpace A)

theorem localInclusion_contMDiff (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (endpointLocalInclusion A i : A.finalSpace i → endpointManifold A hcover) :=
  actualLiftedTerminal_local_inclusion_contMDiff (endpointLocalInclusion A)
    (endpointLocalInclusion_openEmbedding A) (endpointLocalInclusion_jointly_surjective A)
    (embeddingTransition A) (embeddingTransition_inclusion A) i

theorem gluedProjection_contMDiff (A : ActualEndpointHistories X J)
    (hcover : ∀ x : X,∃ i : J,x∈A.openSet i) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (gluedProjection A : endpointManifold A hcover → X) := by
  intro z
  obtain ⟨i,x,rfl⟩ := endpointLocalInclusion_jointly_surjective A z
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (endpointLocalInclusion_openEmbedding A i)
  have hc : c∈atlas (ComplexModel n) (endpointManifold A hcover) :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx : x∈e.source := mem_chart_source (ComplexModel n) x
  have hz : endpointLocalInclusion A i x∈c.source := ⟨x,hx,rfl⟩
  have heMax : e∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (A.finalSpace i) := chart_mem_maximalAtlas x
  have hcMax : c∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (endpointManifold A hcover) := subset_maximalAtlas hc
  have hlocal : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localProjection A i) :=
    endpointProjection_contMDiff (A.openSet i) (A.prefixTower i) (A.tail i)
  have hcx : c (endpointLocalInclusion A i x)=e x :=
    e.lift_openEmbedding_apply (endpointLocalInclusion_openEmbedding A i)
  have hsinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm
      (c (endpointLocalInclusion A i x)) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hx)
  have hh := (hlocal.contMDiffAt.comp _ hsinv).comp _ (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b,hb,rfl⟩ := hy
  change gluedProjection A (endpointLocalInclusion A i b)=
    localProjection A i (e.symm (c (endpointLocalInclusion A i b)))
  rw [gluedProjection_local,e.lift_openEmbedding_apply,e.left_inv hb]

theorem gluedProjection_local_full (A : ActualEndpointHistories X J) (i : J) (y : A.finalSpace i) :
    gluedProjection A (endpointLocalInclusion A i y)=
      ((A.prefixTower i |>.append (A.tail i)).proj y : X) := by
  rw [gluedProjection_local,BlowupTower.proj_append]
  rfl

/-- Whole saturated ranges place the ENTIRE global fibre in one genuine
finite blowup endpoint, with its exact original point in the local base. -/
theorem gluedProjection_fibre (A : ActualEndpointHistories X X)
    (hpoint : ∀ x : X,x∈A.openSet x) (x : X) :
    (gluedProjection A) ⁻¹' ({x} : Set X)=
      endpointLocalInclusion A x '' ((A.prefixTower x |>.append (A.tail x)).proj ⁻¹' {⟨x,hpoint x⟩}) := by
  ext z
  constructor
  · intro hz
    have hp : gluedProjection A z=x := hz
    have hr : z∈range (endpointLocalInclusion A x) := by
      rw [localInclusion_range]
      change gluedProjection A z∈A.openSet x
      rw [hp]
      exact hpoint x
    obtain ⟨y,rfl⟩ := hr
    refine ⟨y,?_,rfl⟩
    change (A.prefixTower x |>.append (A.tail x)).proj y=⟨x,_⟩
    apply Subtype.ext
    exact (gluedProjection_local_full A x y).symm.trans hp
  · rintro ⟨y,hy,rfl⟩
    have hy' : (A.prefixTower x |>.append (A.tail x)).proj y=⟨x,_⟩ := hy
    change gluedProjection A (endpointLocalInclusion A x y)=x
    rw [gluedProjection_local_full]
    exact congrArg Subtype.val hy'

theorem gluedProjection_fibre_isCompact (A : ActualEndpointHistories X X)
    (hpoint : ∀ x : X,x∈A.openSet x) (x : X) :
    IsCompact ((gluedProjection A) ⁻¹' ({x} : Set X)) := by
  rw [gluedProjection_fibre A hpoint]
  exact ((HironakaLocalPrincipalization.isProperMap_proj
    ((A.prefixTower x).append (A.tail x))).isCompact_preimage isCompact_singleton).image
      (endpointLocalInclusion_openEmbedding A x).continuous

theorem gluedProjection_isClosedMap (A : ActualEndpointHistories X X)
    (hpoint : ∀ x : X,x∈A.openSet x) : IsClosedMap (gluedProjection A) := by
  intro C hC
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let Γ := endpointLocalInclusion A x
  let u : A.openSet x := ⟨x,hpoint x⟩
  let T := (A.prefixTower x).append (A.tail x)
  let B : Set (A.finalSpace x) := Γ ⁻¹' C
  have hB : IsClosed B := hC.preimage (endpointLocalInclusion_openEmbedding A x).continuous
  have hcl : IsClosed (T.proj '' B) := (HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap B hB
  let V : Set (A.openSet x) := (T.proj '' B)ᶜ
  have hV : IsOpen V := hcl.isOpen_compl
  have hu : u∈V := by
    rintro ⟨y,hy,hyp⟩
    apply hx
    refine ⟨Γ y,hy,?_⟩
    exact (gluedProjection_local_full A x y).trans (congrArg Subtype.val hyp)
  refine ⟨Subtype.val '' V,?_,?_,⟨u,hu,rfl⟩⟩
  · rintro z ⟨v,hv,rfl⟩ hz
    obtain ⟨w,hw,hpw⟩ := hz
    have hr : w∈range Γ := by
      change w∈range (endpointLocalInclusion A x)
      rw [localInclusion_range]
      change gluedProjection A w∈A.openSet x
      rw [hpw]
      exact v.property
    obtain ⟨y,hΓy⟩ := hr
    apply hv
    refine ⟨y,?_,?_⟩
    · change Γ y∈C
      rw [hΓy]
      exact hw
    · apply Subtype.ext
      have hlocal := gluedProjection_local_full A x y
      change gluedProjection A (Γ y)=(T.proj y).val at hlocal
      exact hlocal.symm.trans ((congrArg (gluedProjection A) hΓy).trans hpw)
  · exact (A.openSet x).isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV

theorem gluedProjection_isProperMap (A : ActualEndpointHistories X X)
    (hpoint : ∀ x : X,x∈A.openSet x) : IsProperMap (gluedProjection A) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(gluedProjection A).continuous,gluedProjection_isClosedMap A hpoint,gluedProjection_fibre_isCompact A hpoint⟩

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY original data produce the real global complex endpoint manifold. -/
def originalEndpointManifold : CMfd.{u} n :=
  endpointManifold (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr)

def originalEndpointProjection : ContinuousMap (originalEndpointManifold hn hW hE hdense hr) X :=
  gluedProjection (originalEndpointHistories hn hW hE hdense hr)

theorem originalEndpointProjection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (originalEndpointProjection hn hW hE hdense hr) :=
  gluedProjection_contMDiff (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr)

theorem originalEndpointProjection_isProperMap : IsProperMap (originalEndpointProjection hn hW hE hdense hr) :=
  gluedProjection_isProperMap (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_point_mem hn hW hE hdense hr)

theorem originalLocalInclusion_contMDiff (x : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (endpointLocalInclusion (originalEndpointHistories hn hW hE hdense hr) x :
        (originalEndpointHistories hn hW hE hdense hr).finalSpace x → originalEndpointManifold hn hW hE hdense hr) :=
  localInclusion_contMDiff (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) x

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalManifold
