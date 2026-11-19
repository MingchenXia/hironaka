import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Invariant.StepOneMaskTower

/-! # The selected carrier at an actual positive section restart -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalRestartCarrier

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  StepOneMaskTower BoundaryCount InvDomainMemberRestriction MemberInterLocusAlong BlowupStrictSubmanifold
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaActualSectionBoundaryGeometry HironakaG8LocalHistory
  HironakaG1PositiveNormalPhase HironakaG1PositiveNormalChronology HironakaG8HomStable
  HironakaG8MemberLoci HomogenizedIdealAlong
open HomogenizedGlueingTower (strictAlong)

universe u

private theorem member_prefix {n : ℕ} {X Y : CMfd.{u} n}
    (A : MarkedIdeal n X) (T : BlowupTower X Y) :
    ∀ D ∈ origMembers A T, D ∈ (geoTransformAlong (barMarked A) T).E :=
  fun _ hD => List.mem_of_mem_take hD

/-- Along a genuine upper test, retaining the original level keeps every
old-member incidence and gives the exact strict transform of the selected
carrier. The member restriction is computed independently at each end. -/
theorem selected_carrier_strictAlong_of_level_eq {n : ℕ} {X Y Z : CMfd.{u} n}
    (A : MarkedIdeal n X) (hA : A.IsWellFormed) (H : BlowupTower X Y)
    (M : BlowupTower Y Z) (hTest : IsGeoTestTower (barMarked A) (H.append M))
    (z : Z) (hLevel : level A (H.append M) z = level A H (M.proj z)) :
    let B := geoTransformAlong (barMarked A) H
    let B' := geoTransformAlong (barMarked A) (H.append M)
    let p := M.proj z
    let D := origMembers A H
    let D' := origMembers A (H.append M)
    (∀ F ∈ D, z ∈ strictAlong M F ↔ p ∈ F) ∧
      strictAlong M (memberRestrict B (membersThrough B.E D p)).N =
        (memberRestrict B' (membersThrough B'.E D' z)).N := by
  classical
  let B := geoTransformAlong (barMarked A) H
  let B' := geoTransformAlong (barMarked A) (H.append M)
  let p := M.proj z
  let D := origMembers A H
  let D' := origMembers A (H.append M)
  obtain ⟨hHead, hTail⟩ := (isGeoTestTower_append_iff _ H M).mp hTest
  have hB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked A hA) H hHead
  have hOld : D' = D.map (strictAlong M) := origMembers_append A H M
  have hCount : boundaryCount D' z = boundaryCount D p := hLevel
  have hProjection (F : Set Y) (hF : F ∈ D) (hzF : z ∈ strictAlong M F) : p ∈ F :=
    MemberInterTowerAlong.strictAlong_subset_preimage M (hB.isSNCDivisor.1 F (member_prefix A H F hF)) hzF
  have hIncidence : ∀ F ∈ D, z ∈ strictAlong M F ↔ p ∈ F := by
    rw [hOld, boundaryCount_map] at hCount
    change (Finset.univ.filter fun i : Fin D.length => z ∈ strictAlong M (D.get i)).card =
      (Finset.univ.filter fun i : Fin D.length => p ∈ D.get i).card at hCount
    have hSub : (Finset.univ.filter fun i : Fin D.length => z ∈ strictAlong M (D.get i)) ⊆
        (Finset.univ.filter fun i : Fin D.length => p ∈ D.get i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hProjection _ (List.get_mem D i) hi
    have hEqual := Finset.eq_of_subset_of_card_le hSub hCount.symm.le
    intro F hF
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hF
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Finset.ext_iff.mp hEqual i
  refine ⟨hIncidence, ?_⟩
  change strictAlong M (B.N ∩ memberInter B.E (membersThrough B.E D p)) =
    B'.N ∩ memberInter B'.E (membersThrough B'.E D' z)
  rw [memberInter_membersThrough (member_prefix A H),
    memberInter_membersThrough (member_prefix A (H.append M)),
    strictAlong_inter_forall_mem B hB (member_prefix A H) (fun F => p ∈ F) M hTail]
  have hTrans : geoTransformAlong B M = B' := (geoTransformAlong_append _ H M).symm
  rw [hTrans, origMembers_append A H M]
  ext w
  exact and_congr_right fun _ => ⟨fun hw F' hF' hzF' => by
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hF'
    exact hw F hF ((hIncidence F hF).mp hzF'),
    fun hw F hF hpF => hw _ (List.mem_map_of_mem hF) ((hIncidence F hF).mpr hpF)⟩

/-- Positive specialness persists through an actual blowup wherever the
upper carrier survives and the original level is unchanged. -/
theorem positive_special_step_of_level_eq {n : ℕ} {X Y Z : CMfd.{u} n}
    (A : MarkedIdeal n X) (hA : A.IsWellFormed) (H : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower (barMarked A) (.step H C π hπ)) (z : Z)
    (hz : z ∈ (geoTransformAlong (barMarked A) (.step H C π hπ)).N)
    (hLevel : level A (.step H C π hπ) z = level A H (π z))
    (hPositive : 0 < level A H (π z)) (hp : IsSpecial A H (π z)) :
    IsSpecial A (.step H C π hπ) z := by
  let B := geoTransformAlong (barMarked A) H
  let B' := geoTransformAlong (barMarked A) (.step H C π hπ)
  let D := origMembers A H
  let D' := origMembers A (.step H C π hπ)
  let K := B.N ∩ {w | ∀ F ∈ D, π z ∈ F → w ∈ F}
  let K' := B'.N ∩ {w | ∀ F ∈ D', z ∈ F → w ∈ F}
  let M : BlowupTower Y Z := .step .refl C π hπ
  have hCar := (selected_carrier_strictAlong_of_level_eq A hA H M hTest z hLevel).2
  change geoStrictTransform π C (B.N ∩ memberInter B.E (membersThrough B.E D (π z))) =
    B'.N ∩ memberInter B'.E (membersThrough B'.E D' z) at hCar
  rw [memberInter_membersThrough (member_prefix A H),
    memberInter_membersThrough (member_prefix A (.step H C π hπ))] at hCar
  have hK : geoStrictTransform π C K = K' := hCar
  have hpMem : π z ∈ memberInterLocus B.N D B.cosupp := by
    rcases hp with ⟨hZero, _⟩ | ⟨_, hMem⟩
    · exact (Nat.ne_of_gt hPositive hZero).elim
    · exact hMem
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp (mem_memberInterLocus_iff.mp hpMem).2
  have hB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked A hA) H hTest.1
  have hB' := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked A hA) (.step H C π hπ) hTest
  have hClosed : IsClosed B'.cosupp := GiraudAlong.isClosed_cosupport_along
    hB'.isCoherent hB'.isClosedSubmanifold_N _
  have hHol : ∀ x f, B.ideal.mem x f → HolomorphicAt n f x := fun _ _ hf =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hf
  have hOpen : IsOpen (π ⁻¹' V) := hVopen.preimage hπ.contMDiff.continuous
  have hLocal (w : Z) (hwV : w ∈ π ⁻¹' V) (hwK : w ∈ K') : w ∈ B'.cosupp := by
    by_contra hOff
    rw [← hK, BlowupStrictSubmanifold.geoStrictTransform] at hwK
    obtain ⟨w', hw', hw'K⟩ := mem_closure_iff.mp hwK
      ((π ⁻¹' V) ∩ B'.cosuppᶜ) (hOpen.inter hClosed.isOpen_compl) ⟨hwV, hOff⟩
    exact hw'.2 ((TransformOffCentre.mem_cosupp_geoTransform_iff B
      hB.isClosedSubmanifold_N.1 hHol hπ hw'K.2).mpr
        (hVsub hw'.1 hw'K.1.1 hw'K.1.2))
  refine Or.inr ⟨hLevel ▸ hPositive, mem_memberInterLocus_iff.mpr ⟨?_, ?_⟩⟩
  · exact hLocal z hpV ⟨hz, fun _ _ h => h⟩
  · exact Filter.mem_of_superset (hOpen.mem_nhds hpV) fun w hw hwN hwD => hLocal w hw ⟨hwN, hwD⟩

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- At a nonspecial section endpoint of positive level on the actual
upper cosupport, the section and padded runs agree. A hypothetical
earlier section-special point would stay special across its next step,
since that step retains the level and the section carrier. -/
theorem positive_normal_section_run_eq_of_nonspecial {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hTest : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) T y) :
    regimeRun (stepRegime (sectionMarked Q) (s + 1)) T y =
      regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let r := regimeRun (stepRegime Sec (s + 1)) T y
  let H := head T (r + 1)
  let p := (tail T (r + 1)).proj y
  let z := (tail T r).proj y
  have hLe := (positive_normal_section_run Q hQ (s := s) T hTest y).1
  refine le_antisymm hLe (le_of_not_gt fun hStrict => ?_)
  have hCut := positive_normal_section_run_cutoff Q (s := s) T hTest y hStrict
  obtain ⟨C, π, hπ, hHead, hProj, _⟩ :=
    positive_normal_section_restart_centre Q hQ (s := s) T hTest y hNS hStrict
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hEquiv := (properNormalMarked_locWPEquiv_section Q hQ).trans (bar_local_any_boundary (X := X) Sec hSec)
  have hSecTest : IsGeoTestTower (barMarked Sec) T := (hEquiv.wEquiv.2 T).1.mp hTest
  have hySec : y ∈ (geoTransformAlong (barMarked Sec) T).cosupp := (hEquiv.wEquiv.2 T).2 hTest ▸ hy
  have hSecLevel : level Sec T y = s + 1 :=
    (level_eq_of_E_eq (show P.E = Sec.E from rfl) T y).symm.trans hLevel
  have hReg := stepRegime_and_mem_cosupp_head Sec hSec.isWellFormed T hSecTest hySec hNS
  rw [hSecLevel] at hReg
  have hNewTest : IsGeoTestTower (barMarked Sec) (head T r) :=
    ((isGeoTestTower_iff_head_tail (barMarked Sec) T r).mp hSecTest).1
  have hzN : z ∈ (geoTransformAlong (barMarked Sec) (head T r)).N :=
    (geoTransformAlong (barMarked Sec) (head T r)).cosupp_subset_N hReg.2
  have hNewLevel : level Sec (head T r) z = s + 1 := hReg.1.1
  have hOldLevel : level Sec H p = s + 1 :=
    (level_eq_of_E_eq (show P.E = Sec.E from rfl) H p).symm.trans hCut.2.1.1
  have hp : IsSpecial Sec H p := hCut.2.2
  rw [hHead] at hNewTest hzN hNewLevel
  have hpπ : IsSpecial Sec H (π z) := hProj.symm ▸ hp
  have hOldLevelπ : level Sec H (π z) = s + 1 := hProj.symm ▸ hOldLevel
  have hPos : 0 < level Sec H (π z) := by rw [hOldLevelπ]; exact Nat.succ_pos s
  have hSame : level Sec (.step H C π hπ) z = level Sec H (π z) := hNewLevel.trans hOldLevelπ.symm
  have hAfter : IsSpecial Sec (.step H C π hπ) z :=
    @positive_special_step_of_level_eq (n + 1) X (split T (r + 1)).1 (split T r).1
      Sec hSec.isWellFormed H C π hπ hNewTest z hzN hSame hPos hpπ
  rw [← hHead] at hAfter
  exact hReg.1.2 hAfter

end
end Hironaka.HironakaG1PositiveNormalRestartCarrier
