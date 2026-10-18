/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBoundaryCoordinates

/-! Actual saturated chart ranges descend the retained SAME-map local
original-good isomorphisms to the whole genuine global projection. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalGoodIsomorphism
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalManifold
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  NormalCrossings NormalCrossingsInvariance
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}
attribute [local instance] endpointChartedSpace

/-- Real open coordinate transport preserves the entire original finite
boundary family, without deleting/relabeling any incident position. -/
theorem originalGoodLocus_preimage_val {W : Set X} {E : List (Set X)}
    (U : Opens X) (x : U) (hx : x.val∈originalGoodLocus (n := n) W E) :
    x∈originalGoodLocus (n := n) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  change x.val∉W ∨ x.val∈W ∧ normalCrossingsAt (n := n) W E x.val at hx
  change x.val∉W ∨ x.val∈W ∧ normalCrossingsAt (n := n)
    ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) x
  rcases hx with hx | ⟨hxW,S₀,S,hcoord,hcard⟩
  · exact Or.inl hx
  · right
    refine ⟨hxW,S₀,fun i => S (Fin.cast (List.length_map _) i),?_,?_⟩
    · have hpre := isCoordinateFamilyAt_preimage_val_iff.mpr hcoord
      exact IsCoordinateFamilyAt.reindex hpre (Option.map (Fin.cast (List.length_map _)))
        (by rintro (_|i);rfl;exact get_map_preimage E i)
        (by rintro (_|i) <;> rfl)
    · intro i hi
      rw [get_map_preimage] at hi
      exact hcard _ hi

/-- The actual whole fibre belongs to one saturated chart range. Real
local injectivity/surjectivity and the differential chain rule descend. -/
theorem gluedProjection_isIsomorphismOver (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (G : Set X)
    (hLocal : ∀ i,IsIsomorphismOver n ((A.prefixTower i).append (A.tail i)).proj
      ((Subtype.val : A.openSet i → X) ⁻¹' G)) :
    IsIsomorphismOver n (gluedProjection A : endpointManifold A hc → X) G := by
  refine ⟨⟨fun _ hx => hx,?_,?_⟩,?_⟩
  · intro q hq r hr hqr
    obtain ⟨i,hi⟩ := hc (gluedProjection A q)
    have hqRange : q∈range (endpointLocalInclusion A i) := by
      rw [localInclusion_range]
      exact hi
    have hrRange : r∈range (endpointLocalInclusion A i) := by
      rw [localInclusion_range]
      change gluedProjection A r∈A.openSet i
      rw [←hqr]
      exact hi
    obtain ⟨z,rfl⟩ := hqRange
    obtain ⟨w,rfl⟩ := hrRange
    have hz : ((A.prefixTower i).append (A.tail i)).proj z∈
        (Subtype.val : A.openSet i → X) ⁻¹' G := by
      change (((A.prefixTower i).append (A.tail i)).proj z).val∈G
      rw [←gluedProjection_local_full A i z]
      exact hq
    have hw : ((A.prefixTower i).append (A.tail i)).proj w∈
        (Subtype.val : A.openSet i → X) ⁻¹' G := by
      change (((A.prefixTower i).append (A.tail i)).proj w).val∈G
      rw [←gluedProjection_local_full A i w]
      exact hr
    have hp : ((A.prefixTower i).append (A.tail i)).proj z=
        ((A.prefixTower i).append (A.tail i)).proj w := by
      apply Subtype.ext
      simpa only [gluedProjection_local_full] using hqr
    exact congrArg (endpointLocalInclusion A i) ((hLocal i).1.2.1 hz hw hp)
  · intro x hx
    obtain ⟨i,hi⟩ := hc x
    obtain ⟨z,_hz,hp⟩ := (hLocal i).1.2.2 (show (⟨x,hi⟩ : A.openSet i)∈
      (Subtype.val : A.openSet i → X) ⁻¹' G from hx)
    have hPoint : gluedProjection A (endpointLocalInclusion A i z)=x :=
      (gluedProjection_local_full A i z).trans (congrArg Subtype.val hp)
    exact ⟨endpointLocalInclusion A i z,by change gluedProjection A _∈G;rw [hPoint];exact hx,hPoint⟩
  · apply disjoint_left.mpr
    intro q hq hqExc
    obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
    let T := (A.prefixTower i).append (A.tail i)
    have hz : T.proj z∈(Subtype.val : A.openSet i → X) ⁻¹' G := by
      change (T.proj z).val∈G
      rw [←gluedProjection_local_full A i z]
      exact hq
    have hzNot : z∉exceptionalLocus n T.proj := fun h => disjoint_left.mp (hLocal i).2 hz h
    have hValNot : T.proj z∉exceptionalLocus n (Subtype.val : A.openSet i → X) := by
      intro h
      apply h
      rw [BlowupIsomorphismOff.mfderiv_subtype_val]
      exact Function.bijective_id
    have hCompositeNot : z∉exceptionalLocus n ((Subtype.val : A.openSet i → X) ∘ T.proj) := by
      rw [exceptionalLocus_comp ((contMDiff_subtype_val (n := ∞) :
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
          (Subtype.val : A.openSet i → X)).mdifferentiable (by simp))
        (T.contMDiff_proj.mdifferentiable (by simp))]
      exact fun h => h.elim hzNot hValNot
    have hSquare : (gluedProjection A : endpointManifold A hc → X) ∘ endpointLocalInclusion A i=
        (Subtype.val : A.openSet i → X) ∘ T.proj := funext (gluedProjection_local_full A i)
    have hBad : z∈exceptionalLocus n ((gluedProjection A : endpointManifold A hc → X) ∘
        endpointLocalInclusion A i) := by
      rw [exceptionalLocus_comp ((gluedProjection_contMDiff A hc).mdifferentiable (by simp))
        ((localInclusion_contMDiff A hc i).mdifferentiable (by simp))]
      exact Or.inr hqExc
    rw [hSquare] at hBad
    exact hCompositeNot hBad

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY original data retain the real local good-locus isomorphisms on
SAME old histories, before actual global bijectivity/nonexceptionality. -/
theorem originalEndpointProjection_isIsomorphismOver_good :
    IsIsomorphismOver n (originalEndpointProjection hn hW hE hdense hr)
      (originalGoodLocus (n := n) W E) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  apply gluedProjection_isIsomorphismOver A (originalEndpointHistories_cover hn hW hE hdense hr)
  intro i
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,_hTest,_hZ,_hD,_hProper,_hDom,_hSNC,_hTrans,hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hSub : (Subtype.val : A.openSet i → X) ⁻¹' originalGoodLocus (n := n) W E ⊆
      originalGoodLocus (n := n) ((Subtype.val : A.openSet i → X) ⁻¹' W)
        (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·)) := fun y hy =>
    originalGoodLocus_preimage_val (A.openSet i) y hy
  refine ⟨⟨fun _ hy => hy,?_,?_⟩,?_⟩
  · intro z hz w hw hp
    exact hIso.1.2.1 (hSub hz) (hSub hw) hp
  · intro y hy
    obtain ⟨z,_hz,hp⟩ := hIso.1.2.2 (hSub hy)
    exact ⟨z,by change _∈(Subtype.val : A.openSet i → X) ⁻¹' originalGoodLocus (n := n) W E;rw [hp];exact hy,hp⟩
  · exact disjoint_left.mpr fun z hz hExc => disjoint_left.mp hIso.2 (hSub hz) hExc

/-- The ENTIRE exceptional image lies in the ORIGINAL sharp bad set. -/
theorem originalEndpointProjection_exceptionalImage_subset_bad :
    (originalEndpointProjection hn hW hE hdense hr) ''
      exceptionalLocus n (originalEndpointProjection hn hW hE hdense hr) ⊆
        originalSharpBadLocus (n := n) W E := by
  rintro x ⟨q,hq,rfl⟩
  rw [originalSharpBadLocus_eq_compl_good]
  exact fun hGood => disjoint_left.mp
    (originalEndpointProjection_isIsomorphismOver_good hn hW hE hdense hr).2 hGood hq

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalGoodIsomorphism
