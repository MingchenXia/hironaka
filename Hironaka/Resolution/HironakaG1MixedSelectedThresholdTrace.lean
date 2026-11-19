import Hironaka.Invariant.ContactEquivalenceStage
import Hironaka.Resolution.HironakaG1InitialPositiveSpecialRecoding
import Hironaka.Resolution.HironakaG1PositiveNormalRestartCarrier
import Hironaka.Invariant.StepOneCompare

/-! # The actual selected member threshold of a paired mixed companion -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1MixedSelectedThresholdTrace
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong
  InvDomainMemberRestriction MarkedIdealRestrictOpen StepOneMaskTower
  HomogenizedGlueingTower TangentDirectionAlong MemberInterLocusAlong CodimOneSupportAlong
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci
  HironakaG1PositiveNormalRestartCarrier HironakaG1InitialPositiveSpecialRecoding

set_option maxHeartbeats 1500000 in
/-- On the actual twice restricted selected tail, a source window class
comparison transports the parent cosupport together with the retained
old-member condition. Equality of the old level identifies these with
the members through the actual section endpoint. -/
theorem selected_threshold_of_source_window_class {n k s : ℕ} {X Y Z : CMfd.{0} n}
    (hn : 0 < n) (P Sec : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hSec : IsInvDomain k Sec)
    (hClass : LocWPEquiv P Sec) (hE : P.E = Sec.E)
    (H : BlowupTower X Y) (R : BlowupTower Y Z) (hT : IsGeoTestTower P (H.append R))
    (z : Z) (hLevel : level P (H.append R) z = level P H (R.proj z))
    (hp : R.proj z ∈ maskA P H (R.proj z)) :
    let W := maskA P H (R.proj z)
    let L := lowerMarkedM (X := X) P (s+1) H (R.proj z)
    let V := restrict W R
    IsGeoTestTower L V →
    ∀ (O : Opens (CMfd.of (n := n) W)) (J : MarkedIdeal n (CMfd.of (n := n) O)),
      LocWPEquiv J (MarkedIdeal.pullback (Subtype.val : O → W) L) →
      ∀ w : openPreimage V O,
        let A := geoTransformAlong (barMarked Sec) (H.append R)
        let i : openPreimage V O → Z := fun x => x.val.val
        w ∈ (geoTransformAlong J (restrict O V)).cosupp ↔
          i w ∈ A.cosupp ∧
          ∀ D ∈ origMembers Sec (H.append R), z ∈ D → i w ∈ D := by
  intro W L V hLV O J hPair w A i
  let TP := H.append R
  let B := geoTransformAlong (barMarked P) TP
  have hPTBar := ((bar_local_any_boundary P hP).wEquiv.2 TP).1.mp hT
  have hCosBar : B.cosupp = A.cosupp :=
    (((bar_local_any_boundary P hP).wEquiv.2 TP).2 hT).symm.trans
      ((((hClass.trans (bar_local_any_boundary Sec hSec)).wEquiv.2 TP).2 hT))
  have hHInc := (selected_carrier_strictAlong_of_level_eq P hP.isWellFormed H R hPTBar z hLevel).1
  have hOld : origMembers Sec TP = (origMembers P H).map (strictAlong R) := by
    rw [← origMembers_eq_of_E_eq hE TP, origMembers_append]
  have hDomL : L.IsWellFormed := by
    change (MarkedIdeal.pullback (Subtype.val : W → Y)
      (memberRestrict (geoTransformAlong (barMarked P) H)
        (membersThrough (geoTransformAlong (barMarked P) H).E (origMembers P H) (R.proj z)))).IsWellFormed
    have hWH := ((isGeoTestTower_append_iff _ H R).mp hPTBar).1
    have hBarH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H hWH
    exact IsWellFormed.pullback_val (isWellFormed_memberRestrict hn hBarH _) W
  have hRestr := (isGeoTestTower_restrict (U := O) hDomL.isClosedSubmanifold_N hDomL.isCoherent V hLV)
  have hComp := (hPair.wEquiv.2 (restrict O V)).2
    (((hPair.wEquiv.2 (restrict O V)).1).mpr hRestr)
  have hCosL := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hDomL.isClosedSubmanifold_N hDomL.isCoherent O V hLV
  have hActual : w.val ∈ (geoTransformAlong L V).cosupp ↔
      i w ∈ B.cosupp ∧ ∀ D ∈ origMembers P H, R.proj z ∈ D → i w ∈ strictAlong R D :=
    StepOneCompare.mem_cosupp_lowerMarked_succ_iff P hP.isWellFormed hn (s := s)
      H R hPTBar hp hLV w.val
  rw [hComp, hCosL]
  change w.val ∈ (geoTransformAlong L V).cosupp ↔ i w ∈ A.cosupp ∧ _
  rw [hActual, hCosBar]
  constructor
  · rintro ⟨hw, hD⟩
    refine ⟨hw, ?_⟩
    intro D hMem hzD
    rw [hOld] at hMem
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hMem
    exact hD F hF ((hHInc F hF).mp hzD)
  · rintro ⟨hw, hD⟩
    refine ⟨hw, fun D hMem hProj => hD (strictAlong R D) ?_ ((hHInc D hMem).mpr hProj)⟩
    rw [hOld]
    exact List.mem_map.mpr ⟨D, hMem, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A local contact saturation test needs the section threshold only on
the actual selected member germ. This version can consume the threshold
computed from the source window class. -/
theorem codimOne_iff_member_of_selected_threshold {n : ℕ} {Y Z : CMfd.{0} n}
    (B : MarkedIdeal n Z) (A : MarkedIdeal n Y) (E : List (Set Y)) (i : Z → Y) (w : Z)
    (hi : Topology.IsOpenEmbedding i) (hB : B.IsWellFormed) (hd : 1 ≤ B.d)
    (hw : w ∈ B.cosupp) {Ω : Set Z} {u : Z → ℂ}
    (hwΩ : w ∈ Ω) (hu : IsTangentDirectionAlong B.N B.ideal B.d Ω u)
    (hThreshold : ∀ x : Z, x ∈ B.cosupp ↔
      i x ∈ A.cosupp ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D)
    (hContact : ∀ᶠ x in 𝓝 w, x ∈ B.N ∩ {z | u z = 0} ∩ Ω ↔
      i x ∈ A.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D) :
    w ∈ codimOnePartAlong B.N B.ideal B.d ↔ i w ∈ memberInterLocus A.N E A.cosupp := by
  have hy := ((hThreshold w).mp hw).1
  rw [codimOnePartAlong_iff_contact_saturated B hB hd hu hw hwΩ, mem_memberInterLocus_iff,
    and_iff_right hy, ← hi.map_nhds_eq w]
  change (∀ᶠ x in 𝓝 w, x ∈ B.N ∩ {z | u z = 0} ∩ Ω → x ∈ B.cosupp) ↔
    ∀ᶠ x in 𝓝 w, i x ∈ A.N → (∀ D ∈ E, i w ∈ D → i x ∈ D) → i x ∈ A.cosupp
  constructor
  · intro hSat
    filter_upwards [hSat, hContact] with x hx hct hxA hxE
    exact ((hThreshold x).mp (hx (hct.mpr ⟨hxA, hxE⟩))).1
  · intro hSat
    filter_upwards [hSat, hContact] with x hx hct hxB
    obtain ⟨hxA, hxE⟩ := hct.mp hxB
    exact (hThreshold x).mpr ⟨hx hxA hxE, hxE⟩

set_option maxHeartbeats 950000 in
/-- Along the actual test, a source tangent and a strict member-carrier
trace suffice once the threshold has been computed by selected transport. -/
theorem codimOne_iff_member_of_tested_selected_trace {n : ℕ} {X Y Z : CMfd.{0} n}
    (J : MarkedIdeal n X) (R : BlowupTower X Z) (hJ : J.IsWellFormed)
    (hd : 1 ≤ J.d) (hR : IsGeoTestTower J R)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d (⊤ : Opens X) u)
    (A : MarkedIdeal n Y) (E : List (Set Y)) (i : Z → Y) (w : Z)
    (hi : Topology.IsOpenEmbedding i) (hw : w ∈ (geoTransformAlong J R).cosupp)
    (hThreshold : ∀ x : Z, x ∈ (geoTransformAlong J R).cosupp ↔
      i x ∈ A.cosupp ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D)
    (hTrace : ∀ᶠ x in 𝓝 w, x ∈ strictAlong R (J.N ∩ {z | u z = 0}) ↔
      i x ∈ A.N ∧ ∀ D ∈ E, i w ∈ D → i x ∈ D) :
    w ∈ codimOnePartAlong (geoTransformAlong J R).N (geoTransformAlong J R).ideal
        (geoTransformAlong J R).d ↔ i w ∈ memberInterLocus A.N E A.cosupp := by
  let B := geoTransformAlong J R
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ R hR
  have hdB : 1 ≤ B.d := (d_geoTransformAlong J R).symm ▸ hd
  obtain ⟨W, hwW, _, v, hv, hNew⟩ := ContactEquivalenceStage.exists_isTangentDirectionAlong_stage
    J hJ.isClosedSubmanifold_N hJ.isCoherent hd ⊤ hu R hR (B.cosupp_subset_N hw) (mem_univ _)
  apply codimOne_iff_member_of_selected_threshold B A E i w hi hB hdB hw hwW hv hThreshold
  filter_upwards [W.isOpen.mem_nhds hwW, hTrace] with x hxW hx
  rw [hNew]
  exact ⟨fun h => hx.mp h.1, fun h => ⟨hx.mpr h, hxW⟩⟩

set_option maxHeartbeats 1200000 in
/-- At the actual selected tail and its second source mask, a window
class match supplies the endpoint threshold for specialness. The
remaining local geometry is the strict trace of a source tangent. -/
theorem zero_companion_special_iff_of_selected_source_class
    {n k s : ℕ} {X Y Z : CMfd.{0} n} (hn : 0 < n) (P Sec : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hSec : IsInvDomain k Sec)
    (hClass : LocWPEquiv P Sec) (hE : P.E = Sec.E)
    (H : BlowupTower X Y) (R : BlowupTower Y Z) (hT : IsGeoTestTower P (H.append R))
    (z : Z) (hLevel : level P (H.append R) z = level P H (R.proj z))
    (hPositive : 0 < level Sec (H.append R) z) (hp : R.proj z ∈ maskA P H (R.proj z)) :
    let W := maskA P H (R.proj z)
    let L := lowerMarkedM (X := X) P (s+1) H (R.proj z)
    let V := restrict W R
    IsGeoTestTower L V →
    ∀ (O : Opens (CMfd.of (n := n) W)) (J : MarkedIdeal n (CMfd.of (n := n) O)),
      let B := barMarked J
      let S := restrict O V
      let A := geoTransformAlong (barMarked Sec) (H.append R)
      let i : openPreimage V O → Z := fun x => x.val.val
      LocWPEquiv B (MarkedIdeal.pullback (Subtype.val : O → W) L) →
      B.IsWellFormed → 1 ≤ B.d →
      ∀ w : openPreimage V O, i w = z →
      w ∈ (geoTransformAlong B S).cosupp → level J S w = 0 →
      ∀ u : O → ℂ, IsTangentDirectionAlong B.N B.ideal B.d univ u →
      (∀ᶠ x in 𝓝 w, x ∈ strictAlong S (B.N ∩ {y | u y = 0}) ↔
        i x ∈ A.N ∧ ∀ D ∈ origMembers Sec (H.append R), z ∈ D → i x ∈ D) →
      (IsSpecial J S w ↔ IsSpecial Sec (H.append R) z) := by
  intro W L V hLV O J B S A i hPair hB hd w hwz hw hZero u hu hTrace
  have hDomL : L.IsWellFormed := by
    have hBarTest := ((bar_local_any_boundary P hP).wEquiv.2 (H.append R)).1.mp hT
    have hHead := ((isGeoTestTower_append_iff _ H R).mp hBarTest).1
    have hBarH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H hHead
    change (MarkedIdeal.pullback (Subtype.val : W → Y)
      (memberRestrict (geoTransformAlong (barMarked P) H)
        (membersThrough (geoTransformAlong (barMarked P) H).E (origMembers P H) (R.proj z)))).IsWellFormed
    exact IsWellFormed.pullback_val (isWellFormed_memberRestrict hn hBarH _) W
  have hRestr := isGeoTestTower_restrict (U := O) hDomL.isClosedSubmanifold_N hDomL.isCoherent V hLV
  have hTestB : IsGeoTestTower B S := ((hPair.wEquiv.2 S).1).mpr hRestr
  have hi : Topology.IsOpenEmbedding i :=
    (openPreimage R W).isOpen.isOpenEmbedding_subtypeVal.comp
      (openPreimage V O).isOpen.isOpenEmbedding_subtypeVal
  have hThreshold (x : openPreimage V O) :
      x ∈ (geoTransformAlong B S).cosupp ↔
        i x ∈ A.cosupp ∧ ∀ D ∈ origMembers Sec (H.append R), i w ∈ D → i x ∈ D := by
    rw [hwz]
    exact selected_threshold_of_source_window_class (s := s)
      hn P Sec hP hSec hClass hE H R hT z hLevel hp hLV O B hPair x
  have hTrace' : ∀ᶠ x in 𝓝 w, x ∈ strictAlong S (B.N ∩ {y | u y = 0}) ↔
      i x ∈ A.N ∧ ∀ D ∈ origMembers Sec (H.append R), i w ∈ D → i x ∈ D := by
    rw [hwz]
    exact hTrace
  have hLocal := codimOne_iff_member_of_tested_selected_trace B S hB hd hTestB u hu A
    (origMembers Sec (H.append R)) i w hi hw hThreshold hTrace'
  rw [hwz] at hLocal
  have hNo : ¬ (1 ≤ (0 : ℕ)) := by decide
  have hPos : 1 ≤ level Sec (H.append R) z := hPositive
  simpa only [IsSpecial, hZero, true_and, hNo, false_and, or_false, Nat.ne_of_gt hPositive,
    false_or, hPos] using hLocal

end
end Hironaka.HironakaG1MixedSelectedThresholdTrace
