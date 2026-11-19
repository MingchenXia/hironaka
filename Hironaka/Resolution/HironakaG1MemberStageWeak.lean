import Hironaka.Resolution.HironakaG1CoeffBarLocal
import Hironaka.Resolution.HironakaG8MemberWeakEquiv
import Hironaka.Resolution.HironakaG8MemberProjectionWeak
import Hironaka.Resolution.HironakaG8PowerLowerGeometry
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold
namespace Hironaka.HironakaG1MemberStageWeak
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec HironakaG1CoeffBarLocal HironakaG8MemberProjectionWeak HironakaG8MemberWeakEquiv
  HironakaActualProjectionTestRecord HironakaG8MemberLoci HironakaCoherentTransformExtension
  HironakaG8LocalHistory HironakaG8ProjEquiv HironakaG8HomStable HironakaG8PowerLowerGeometry
  StepOneValue StepOneBridge InvDomainMemberRestriction InvDomainRebase InvDomainTowerAlong
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen

/-- At every common prefix and every open containing its anchor, controlled
and projected tests agree for the literal member-restricted bar records. -/
theorem member_stage_weak_of_local {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (U : Opens Y) (z : Y) (hz : z ∈ U) :
    let P := geoTransformAlong (barMarked A) T
    let Q := geoTransformAlong (barMarked B) T
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict P (membersThrough P.E (origMembers A T) z))
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict Q (membersThrough Q.E (origMembers B T) z))
    WEquiv P' Q' ∧ WEquiv (projectionTest P') (projectionTest Q') := by
  let P := geoTransformAlong (barMarked A) T
  let Q := geoTransformAlong (barMarked B) T
  let PU := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) P
  let QU := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y) Q
  let E₀ := origMembers A T
  let p : U := ⟨z,hz⟩
  have hBT := (hL.wEquiv.2 T).1.mp hT
  have hTP := ((bar_local_any_boundary A hA).wEquiv.2 T).1.mp hT
  have hTQ := ((bar_local_any_boundary B hB).wEquiv.2 T).1.mp hBT
  have hPD := isInvDomain_geoTransformAlong (isInvDomain_barMarked A hA) T hTP
  have hQD := isInvDomain_geoTransformAlong (isInvDomain_barMarked B hB) T hTQ
  have hPU := isInvDomain_pullback_val U hPD
  have hQU := isInvDomain_pullback_val U hQD
  have hE0 : A.E = B.E := hL.wEquiv.1
  have hNT : P.N = Q.N := geoTransformAlong_N_eq_of_N_eq (by simpa only [barMarked_N] using hN) T
  have hET : P.E = Q.E := E_geoTransformAlong_eq (by simpa only [barMarked_E] using hE0) T
  have hNU : PU.N = QU.N := by change (Subtype.val : U → Y) ⁻¹' P.N = (Subtype.val : U → Y) ⁻¹' Q.N; rw [hNT]
  have hEU : PU.E = QU.E := by change P.E.map ((Subtype.val : U → Y) ⁻¹' ·) = Q.E.map ((Subtype.val : U → Y) ⁻¹' ·); rw [hET]
  have hBar := bar_local_of_local A B hA hB hL
  have hStage := (hBar.geoTransformAlong T hTP).restrict U
  have hOrig : origMembers A T = origMembers B T := origMembers_eq_of_E_eq hE0 T
  have hmem : ∀ H ∈ E₀, H ∈ P.E := fun H hH => List.mem_of_mem_take hH
  have hPpull := pullback_val_memberRestrict_membersThrough hPD.isWellFormed hPD.one_le_d hmem U p
  have hQmem : ∀ H ∈ origMembers B T, H ∈ Q.E := fun H hH => List.mem_of_mem_take hH
  have hQpull := pullback_val_memberRestrict_membersThrough hQD.isWellFormed hQD.one_le_d hQmem U p
  have hWeak := memberRestrict_membersThrough_wEquiv (X := CMfd.of (n := n) U) (A := PU) (B := QU)
    hn hPU.isWellFormed hQU.isWellFormed hPU.one_le_d hQU.one_le_d hNU hEU hStage.wEquiv (E₀.map ((Subtype.val : U → Y) ⁻¹' ·)) p
  have hProj := projection_memberRestrict_membersThrough_wEquiv (X := CMfd.of (n := n) U) (A := PU) (B := QU)
    hn hPU hQU hNU hEU hStage.projEquiv.projectionTest_wEquiv (E₀.map ((Subtype.val : U → Y) ⁻¹' ·)) p
  constructor <;> rw [hPpull,hQpull,←hOrig]
  · exact hWeak
  · exact hProj
end
end Hironaka.HironakaG1MemberStageWeak
