/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalGoodIsomorphism
import Hironaka.Support.MarkOneCarrierDensityExact
import Hironaka.Support.OpensExceptionalLocusExact

/-! Actual TEST carrier density, full exceptional chart dictionaries and
the EXISTING conventional strict closure of the SAME global projection. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalStrictClosure
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowerTransforms HomogenizedGlueingTower
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveLocalRangeBiholomorphism HironakaSharpActualCurveGluedStrictSets
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualCurveStrictSetOverlaps
  NormalCrossings NormalCrossingsInvariance
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}
attribute [local instance] endpointChartedSpace

/-- Real nonzero-along germs and actual cosupport produce density, not
an assumed nowhere-dense-centre certificate. -/
theorem carrier_subset_closure_diff_of_mark_one {M : MarkedIdeal n X} {k : ℕ}
    (hM : IsInvDomain k M) (hd : M.d=1) {C : Set X} (hC : C⊆M.cosupp) :
    M.N⊆closure (M.N \ C) := by
  intro x hx
  by_cases hxC : x∈C
  · exact mem_closure_iff_frequently.mpr
      (FactorizationFromResolution.frequently_mem_N_notMem_of_isInvDomain hM hd hC x hxC)
  · exact subset_closure ⟨hx,hxC⟩

/-- The SAME literal composite, every empty step retained, gives the
conventional strict transform of the actual carrier on ANY mark-one TEST. -/
theorem carrier_eq_strictTransform (M : MarkedIdeal n X) {k : ℕ}
    (hM : IsInvDomain k M) (hd : M.d=1) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      (geoTransformAlong M T).N=strictTransform n T.proj M.N
  | _,.refl,_ => by
    simp only [geoTransformAlong_refl,BlowupTower.proj_refl,strictTransform,
      exceptionalLocus_id,preimage_id,sdiff_empty,hM.isWellFormed.isClosedSubmanifold_N.1.closure_eq]
  | _,.step T C π hπ,hT => by
    have hPrev := carrier_eq_strictTransform M hM hd T hT.1
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT.1
    have hMark : (geoTransformAlong M T).d=1 := (d_geoTransformAlong M T).trans hd
    have hDense := carrier_subset_closure_diff_of_mark_one hCurrent hMark hT.2.2.1
    change BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong M T).N=_
    rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp
      T.contMDiff_proj hπ.contMDiff,BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hDense,hPrev]

/-- Actual holomorphic inverse and real open inclusion prove that the
WHOLE chart inclusion has empty differential exceptional locus. -/
theorem exceptionalLocus_localInclusion (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    exceptionalLocus n (endpointLocalInclusion A i : A.finalSpace i → endpointManifold A hc)=∅ := by
  let e := localBiholomorphism A hc i
  have he : exceptionalLocus n e=∅ := eq_empty_iff_forall_notMem.mpr fun z =>
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      e.contMDiff e.symm.contMDiff e.apply_symm_apply e.symm_apply_apply z
  have hFactor : (endpointLocalInclusion A i : A.finalSpace i → endpointManifold A hc)=
      (Subtype.val : localRangeOpen A hc i → endpointManifold A hc) ∘ e :=
    funext fun z => (localBiholomorphism_point A hc i z).symm
  have hComposite : exceptionalLocus n
      ((Subtype.val : localRangeOpen A hc i → endpointManifold A hc) ∘ e)=∅ := by
    rw [exceptionalLocus_comp ((contMDiff_subtype_val (n := ∞) :
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (Subtype.val : localRangeOpen A hc i → endpointManifold A hc)).mdifferentiable (by simp))
      (e.contMDiff.mdifferentiable (by simp)),he,OpensRestrictionMeasure.exceptionalLocus_val,
      preimage_empty,union_empty]
  exact (congrArg (fun φ : A.finalSpace i → endpointManifold A hc => exceptionalLocus n φ) hFactor).trans hComposite

/-- BOTH entire exceptional-locus pullback directions on the exact old
finite local projection follow from two genuine differential chain rules. -/
theorem preimage_exceptionalLocus_gluedProjection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    endpointLocalInclusion A i ⁻¹'
      exceptionalLocus n (gluedProjection A : endpointManifold A hc → X)=
        exceptionalLocus n ((A.prefixTower i).append (A.tail i)).proj := by
  let T := (A.prefixTower i).append (A.tail i)
  have hSquare : (gluedProjection A : endpointManifold A hc → X) ∘ endpointLocalInclusion A i=
      (Subtype.val : A.openSet i → X) ∘ T.proj := funext (gluedProjection_local_full A i)
  calc
    _=exceptionalLocus n ((gluedProjection A : endpointManifold A hc → X) ∘ endpointLocalInclusion A i) := by
      rw [exceptionalLocus_comp ((gluedProjection_contMDiff A hc).mdifferentiable (by simp))
        ((localInclusion_contMDiff A hc i).mdifferentiable (by simp)),
        exceptionalLocus_localInclusion A hc i,empty_union]
    _=exceptionalLocus n ((Subtype.val : A.openSet i → X) ∘ T.proj) :=
      congrArg (exceptionalLocus n) hSquare
    _=_ := by
      rw [exceptionalLocus_comp ((contMDiff_subtype_val (n := ∞) :
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
          (Subtype.val : A.openSet i → X)).mdifferentiable (by simp))
        (T.contMDiff_proj.mdifferentiable (by simp)),OpensRestrictionMeasure.exceptionalLocus_val,
        preimage_empty,union_empty]

/-- Genuine continuous open chart inclusions commute with closure, while
the separate entire projection/exceptional dictionaries identify its argument. -/
theorem preimage_strictTransform_gluedProjection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (B : Set X) :
    endpointLocalInclusion A i ⁻¹'
      strictTransform n (gluedProjection A : endpointManifold A hc → X) B=
        strictTransform n ((A.prefixTower i).append (A.tail i)).proj
          ((Subtype.val : A.openSet i → X) ⁻¹' B) := by
  unfold strictTransform
  rw [(endpointLocalInclusion_openEmbedding A i).isOpenMap.preimage_closure_eq_closure_preimage
    (endpointLocalInclusion_openEmbedding A i).continuous,
    preimage_sdiff,preimage_exceptionalLocus_gluedProjection A hc i]
  congr 2
  ext z
  change gluedProjection A (endpointLocalInclusion A i z)∈B ↔
    (((A.prefixTower i).append (A.tail i)).proj z).val∈B
  rw [gluedProjection_local_full]

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY original inputs give the literal local curve's conventional
strict-transform identity on the SAME actual finite recipe. -/
theorem original_localStrictSet_eq_strictTransform (i : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    localStrictSet A W i=strictTransform n ((A.prefixTower i).append (A.tail i)).proj
      ((Subtype.val : A.openSet i → X) ⁻¹' W) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let M := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,hTest,_hZ,_hD,_hProper,_hDom,_hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hrU : ∀ y ∈ WU,RegularAtDim (n := n) WU y 1 :=
    fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  have hDenseU : WU⊆closure (WU \ ⋃ H ∈ EU,H) := by
    intro y hy
    have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hM : IsInvDomain n M :=
    originalMemberProductMarked_isInvDomain hn hWU hEU hn hrU hDenseU le_rfl
  have hCarrier := carrier_eq_strictTransform M hM rfl ((A.prefixTower i).append (A.tail i)) hTest
  rw [N_geoTransformAlong] at hCarrier
  exact hCarrier

/-- The independently constructed global curve is exactly the EXISTING
closure of the SAME global projection's nonexceptional inverse image. -/
theorem originalGluedStrictCurve_eq_strictTransform :
    originalGluedStrictSet hn hW hE hdense hr W=
      strictTransform n (originalEndpointProjection hn hW hE hdense hr) W := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  ext q
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  have hLocal := original_localStrictSet_eq_strictTransform hn hW hE hdense hr i
  have hTrace := preimage_strictTransform_gluedProjection A hc i W
  have hEq : endpointLocalInclusion A i ⁻¹'
      strictTransform n (gluedProjection A : endpointManifold A hc → X) W=localStrictSet A W i :=
    hTrace.trans hLocal.symm
  have hMembership := congrArg (fun B : Set (A.finalSpace i) => z∈B) hEq
  exact (mem_gluedStrictSet_iff A W hW.1 i z).trans ⟨Eq.mpr hMembership,Eq.mp hMembership⟩

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalStrictClosure
