import Hironaka.Resolution.HironakaStepOneZeroContactCurveNonzeroExtension
import Hironaka.Resolution.HironakaActualRawRecordPullbacks
import Hironaka.Resolution.HironakaActualNativeSectionContactChoices
import Hironaka.Resolution.HironakaActualNativeSectionPositiveLowerRecords

/-! Whole ORIGINAL zero-contact records in every dimension. Selected
component absence is derived from actual current bar Z1 avoidance, and
all original/born boundary positions are retained on genuine windows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualZeroContactWholeRecords
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept MaximalOrderStepOneB
  ContactStageInvDomain ContactEquivalenceStage CoefficientIdealRestriction HomogenizedIdealAlong
  HomogenizedIdealAlongTower GermIdealOrder CodimOneSupportAlong
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderGlueing
  HironakaStepOneZeroContactCurveNonzeroExtension
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaActualRawRecordPullbacks TangentDirectionAlong
universe u
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Literal inclusion of one genuine current open into another. -/
def windowInclusion (V O : Opens Y) (h : O≤V) : O→V:=fun p=>⟨p.val,h p.property⟩

theorem windowInclusion_contMDiff (V O : Opens Y) (h : O≤V) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (windowInclusion V O h) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact contMDiff_subtype_val

/-- Geometric Z1 and original-member avoidance internally recover the
ENTIRE original contact record from its kept-position remainder. -/
theorem contact_remainder_eq_on_zero_window
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hd : 1≤M.d) (U : Opens X) (w : X→ℂ)
    (hw : IsTangentDirectionAlong M.N M.ideal M.d U w)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (O : Opens Y) (hOU : O≤openPreimage T U)
    (hOZ : ∀y∈O,y∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d)
    (hOE : ∀H∈origMembers M T,∀y∈O,y∉H) :
    MarkedIdeal.pullback (windowInclusion (openPreimage T U) O hOU)
      (contactRemainderMarked (contactMarkedKept M w T (openPreimage T U)) M.E.length)=
        contactMarkedKept M w T O := by
  let V:=openPreimage T U
  let L:=contactMarkedKept M w T V
  let f:=windowInclusion V O hOU
  have hTa := ((coeff_homAlong_wEquiv M hN hI hd).2 T).1.mp hT
  have hLN : IsClosedSubmanifold n L.N:=
    isClosedSubmanifold_strictAlong_stage_of_le M hN hI hd U hw T hTa V subset_rfl
  have hSel : ∀p : O,f p∉selectedComponents (n:=n) L.N L.cosupp:=by
    intro p hp
    exact hOZ p.val p.property
      (selected_contact_components_subset_codimOnePartAlong M hN hI hd U w hw T hT hp)
  have hCount : M.E.length≤L.E.length:=by
    change M.E.length≤((geoTransformAlong (barMarked M) T).E.map ((Subtype.val : V→Y) ⁻¹' ·)).length
    rw [List.length_map,length_E_geoTransformAlong]
    exact Nat.le_add_right _ _
  have hTake : (L.E.take M.E.length).map (f ⁻¹' ·)=List.replicate M.E.length ∅:=by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_,?_⟩
    · simp only [List.length_map,List.length_take,Nat.min_eq_left hCount]
    · intro B hB
      obtain ⟨H,hH,rfl⟩:=List.mem_map.mp hB
      change H∈((geoTransformAlong (barMarked M) T).E.map ((Subtype.val : V→Y) ⁻¹' ·)).take M.E.length at hH
      rw [←List.map_take] at hH
      obtain ⟨H₀,hH₀,rfl⟩:=List.mem_map.mp hH
      exact eq_empty_iff_forall_notMem.mpr (fun p=>hOE H₀ hH₀ p.val p.property)
  have hRem : MarkedIdeal.pullback f (contactRemainderMarked L M.E.length)=
      MarkedIdeal.pullback f L:=by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · change f ⁻¹' remainingComponents (n:=n) L.N L.cosupp=f ⁻¹' L.N
      rw [remainingComponents_eq_diff_selected hLN]
      ext p
      exact and_iff_left (hSel p)
    · change (List.replicate M.E.length ∅ ++ L.E.drop M.E.length).map (f ⁻¹' ·)=L.E.map (f ⁻¹' ·)
      rw [List.map_append,List.map_replicate,preimage_empty]
      conv_rhs=>rw [←List.take_append_drop M.E.length L.E,List.map_append,hTake]
    · rfl
    · rfl
  have hHead : (withN (coeffMarkedAlong (geoTransformAlong (barMarked M) T))
      (strictAlong T (M.N∩{x | w x=0}))).ideal.IsCoherent:=
    isCoherent_restrictedCoeff M hI hN w T hT
  apply hRem.trans
  exact marked_pullback_comp_hhol
    (J:=withN (coeffMarkedAlong (geoTransformAlong (barMarked M) T)) (strictAlong T (M.N∩{x | w x=0})))
    (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hHead hg)
    contMDiff_subtype_val (windowInclusion_contMDiff V O hOU) (fun _=>rfl)

/-- ORIGINAL selected contact open, ORIGINAL nonempty zero mask and ENTIRE
lowerMarkedB are recovered internally at every original test prefix,
without a dimension-three restriction or canonicality premise. -/
theorem original_zero_mask_remainder_record
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : 1≤M.d)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (p : Y) (hp : p∈(geoTransformAlong (barMarked M) T).cosupp)
    (hl : level M T p=0)
    (hZ : p∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d) :
    ∃U : Opens X,(U : Set X)=(tangentChoice M (T.proj p)).1 ∧
      ∃hMU : maskB M T p≤openPreimage T U,
        p∈maskB M T p ∧ T.proj p∈U ∧
          IsTangentDirectionAlong M.N M.ideal M.d U (tangentChoice M (T.proj p)).2 ∧
          MarkedIdeal.pullback (windowInclusion (openPreimage T U) (maskB M T p) hMU)
            (contactRemainderMarked
              (contactMarkedKept M (tangentChoice M (T.proj p)).2 T (openPreimage T U)) M.E.length)=
            lowerMarkedB M T p := by
  obtain ⟨hpU,hu⟩:=tangentChoice_spec M (exists_tangent_of_mem_cosupp M hM hd hmax T hT hp)
  let U : Opens X:=⟨(tangentChoice M (T.proj p)).1,hu.isOpen⟩
  have hMU : maskB M T p≤openPreimage T U:=by
    intro y hy
    exact (interior_subset hy).1
  have hRecord:=contact_remainder_eq_on_zero_window M hM.isClosedSubmanifold_N hM.isCoherent
    hd U (tangentChoice M (T.proj p)).2 hu T hT (maskB M T p) hMU
    (fun y hy=>(interior_subset hy).2.2)
    (fun H hH y hy=>(interior_subset hy).2.1 H hH)
  exact ⟨U,rfl,hMU,mem_maskB M hM hd hmax T hT hp hl hZ,hpU,hu,hRecord⟩

end
end Hironaka.HironakaActualZeroContactWholeRecords
