import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Resolution.HironakaG1LaterSelectedSectionCanonical
import Hironaka.Resolution.FactorizationFromResolution

/-! Recognizing the finite zero letter and its clock from the strict supported trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CompanionZeroBranchRecognition
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec InvDomainTowerAlong
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain StepOneMaskTower
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci BoundaryCount
  GermIdealOrder RelativePrincipalizationSpan CodimOneSupportAlong ContactStageInvDomain
  FactorizationFromResolution TangentDirectionAlong
  HironakaG1ActualLaterCommonTangent HironakaG1RecursiveMemberValueTransport
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  NonmonomialOrderTail GeneralValue CanonicalCentres InvDomainMemberRestriction
  HironakaG1LaterSelectedSectionCanonical CompanionRebase CompanionReductionAlong
open HomogenizedGlueingTower (N_geoTransformAlong strictAlong)

set_option maxHeartbeats 900000 in
/-- The literal supported trace prevents codimension-one saturation in the
larger current carrier. This uses nonvanishing on the strict support, with
no assumed later-stage non-special predicate. -/
theorem codim_one_absent_of_strict_supported_trace {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y) :
    let B := geoTransformAlong (barMarked J) T
    y ∉ codimOnePartAlong B.N B.ideal B.d := by
  intro B hsp
  let JT := geoTransformAlong J T
  let RT := geoTransformAlong R T
  have hBT := ((bar_local_any_boundary J hJ).wEquiv.2 T).1.mp hT
  have hRT := (hClass.wEquiv.2 T).1.mp hT
  have hDomR : IsInvDomain l RT := isInvDomain_geoTransformAlong hR T hRT
  have hDomB : IsInvDomain k B := isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked J hJ) T hBT
  have hCos : B.cosupp = RT.cosupp :=
    (((bar_local_any_boundary J hJ).wEquiv.2 T).2 hT).symm.trans ((hClass.wEquiv.2 T).2 hT)
  have hyB : y ∈ B.cosupp := codimOnePartAlong_subset hsp
  have hyR : y ∈ RT.N := RT.cosupp_subset_N (hCos ▸ hyB)
  have hyStrict : y ∈ strictAlong T (J.N ∩ {x | u x = 0}) := by
    rw [hTrace, ← N_geoTransformAlong]
    exact hyR
  have hu' : IsTangentDirectionAlong J.N J.ideal J.d (⊤ : Opens X) u := hu
  obtain ⟨j, hjJ, hjR⟩ := exists_regularAtDim_strictAlong_stage J
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
    ⊤ hu' T hT (by trivial) hyStrict
  have hNJB : JT.N = B.N := by
    change (geoTransformAlong J T).N = (geoTransformAlong (barMarked J) T).N
    rw [N_geoTransformAlong, N_geoTransformAlong]
    rfl
  have hjR' : RegularAtDim (n := n) RT.N y j := by
    rwa [hTrace, ← N_geoTransformAlong] at hjR
  obtain ⟨d, hdN, hdCos⟩ := hsp
  have hd : d = j := Nat.add_right_cancel
    (RegularPointDimension.eq_of_regularAtDim hdN (hNJB ▸ hjJ))
  have hjCos : RegularAtDim (n := n) B.cosupp y j := hd ▸ hdCos
  obtain ⟨g, hg, hfreq⟩ := hDomR.isNonzeroAlongAt y hyR
  have hmem := HomogenizedGlueing.eventually_mem hDomR.isWellFormed.isCoherent hg
  have hThin : ∃ᶠ z in 𝓝 y, z ∈ RT.N ∧ z ∉ B.cosupp := by
    apply (hfreq.and_eventually hmem).mono
    rintro z ⟨⟨hz, hgz⟩, hmemz⟩
    refine ⟨hz, fun hzc => hgz ?_⟩
    have hzc' : z ∈ RT.cosupp := hCos ▸ hzc
    exact (vanishesToOrderOn_one_iff hz
      (GermIdeal.IsCoherent.holomorphicAt_mem hDomR.isWellFormed.isCoherent hmemz)).mp
      ((hzc'.2 g hmemz).mono hDomR.one_le_d)
  have hAn : IsComplexAnalyticSubset (n := n) B.cosupp :=
    isComplexAnalyticSubset_cosupport_along hDomB.isWellFormed.isCoherent
      hDomB.isWellFormed.isClosedSubmanifold_N hDomB.one_le_d
  have hSub : B.cosupp ⊆ RT.N := fun _ hz => RT.cosupp_subset_N (hCos ▸ hz)
  exact (Nat.lt_irrefl j) (lt_of_regularAtDim_of_frequently hAn hSub hjCos hjR' hThin)

private theorem initial_level_zero_of_no_incidence {n : ℕ} {X : CMfd.{0} n}
    (J : MarkedIdeal n X) (p : X) (hp : ∀ D ∈ J.E, p ∉ D) :
    level J (.refl (X := X)) p = 0 := by
  classical
  change boundaryCount (J.E.take J.E.length) p = 0
  rw [List.take_length, boundaryCount, Finset.card_eq_zero]
  exact Finset.filter_eq_empty_iff.mpr fun i _ => hp _ (List.get_mem _ i)

set_option maxHeartbeats 1100000 in
/-- No incident retained member at the base gives the finite zero letter
and the full zero clock on an arbitrary actual ordinary test history.
New exceptional members of this history do not enter its original count. -/
theorem zero_step_regime_of_strict_supported_trace {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y)
    (hoff : ∀ D ∈ J.E, T.proj y ∉ D) :
    stepRegime J 0 T y ∧ regimeRun (stepRegime J 0) T y = T.length := by
  have hBase := initial_level_zero_of_no_incidence J (T.proj y) hoff
  have hZero {Z : CMfd.{0} n} (S : BlowupTower X Z) (z : Z)
      (h : level J (.refl (X := X)) (S.proj z) = 0) : level J S z = 0 := by
    have hLe := level_append_le J (fun D hD => hJ.isWellFormed.isSNCDivisor.1 D hD)
      (.refl (X := X)) S z
    rw [BlowupTower.refl_append, h] at hLe
    exact Nat.eq_zero_of_le_zero hLe
  have hReg {Z : CMfd.{0} n} (S : BlowupTower X Z) (hS : IsGeoTestTower J S) (z : Z)
      (h : level J (.refl (X := X)) (S.proj z) = 0) : stepRegime J 0 S z := by
    have hz := hZero S z h
    refine ⟨hz, ?_⟩
    rintro (⟨_, hsp⟩ | ⟨hp, _⟩)
    · exact codim_one_absent_of_strict_supported_trace J R hJ hR hClass u hu hTrace S hS z hsp
    · omega
  refine ⟨hReg T hT y hBase, le_antisymm (regimeRun_le_length (stepRegime J 0) T y) (le_of_not_gt ?_)⟩
  intro hlt
  let r := regimeRun (stepRegime J 0) T y + 1
  let H := head T r
  let S := tail T r
  let z := S.proj y
  have hH := ((isGeoTestTower_iff_head_tail J T r).mp hT).1
  have hProj : H.proj z = T.proj y := congrFun (proj_eq_comp T r).symm y
  have hz0 : level J (.refl (X := X)) (H.proj z) = 0 := by rw [hProj]; exact hBase
  exact not_regime_head_regimeRun (stepRegime J 0) T y hlt (hReg H hH z hz0)

/-- Zero level alone detects the finite regime on the actual common
test, even when the earlier retained members are incident. -/
theorem step_regime_zero_iff_level_of_strict_supported_trace {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y) :
    stepRegime J 0 T y ↔ level J T y = 0 := by
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  rintro (⟨_, hsp⟩ | ⟨hp, _⟩)
  · exact codim_one_absent_of_strict_supported_trace J R hJ hR hClass u hu hTrace T hT y hsp
  · omega

/-- On a nonempty test the full zero clock occurs exactly when the
projection misses every retained original member of the companion. -/
theorem full_zero_clock_iff_no_source_incidence {n k l : ℕ} {X Y : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (hLen : 0 < T.length) (y : Y) :
    regimeRun (stepRegime J 0) T y = T.length ↔ ∀ D ∈ J.E, T.proj y ∉ D := by
  classical
  refine ⟨fun h => ?_, fun h =>
    (zero_step_regime_of_strict_supported_trace J R hJ hR hClass u hu hTrace T hT y h).2⟩
  have hReg := regime_head_of_le_regimeRun (stepRegime J 0) T y T.length hLen h.ge
  change stepRegime J 0 (split T T.length).2.1 ((split T T.length).2.2.proj y) at hReg
  rw [StepOneEmptyPrefix.split_of_length_le T T.length le_rfl] at hReg
  have hl : level J (.refl (X := X)) (T.proj y) = 0 := hReg.1
  change boundaryCount (J.E.take J.E.length) (T.proj y) = 0 at hl
  rw [List.take_length, boundaryCount, Finset.card_eq_zero] at hl
  intro D hD hyD
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hD
  exact Finset.filter_eq_empty_iff.mp hl (Finset.mem_univ i) hyD

private theorem no_incidence_map {X Y : Type*} (f : Y → X)
    (E : List (Set X)) (y : Y) (h : ∀ F ∈ E, f y ∉ F) :
    ∀ F ∈ E.map (f ⁻¹' ·), y ∉ F := by
  intro F hF
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
  exact h G hG

private theorem off_positive_member_of_no_born {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) (W : Opens Y)
    (hW : W ≤ maskA P H p) (a : W) (ha : a.val = p)
    (hNoBorn : ∀ F ∈ (geoTransformAlong (barMarked P) H).E.drop P.E.length, p ∉ F) :
    ∀ F ∈ (positiveMemberOn P H p W).E, a ∉ F := by
  intro F hF hInc
  obtain ⟨G, hG, hEq⟩ := exists_born_member_of_mem_retained_on_mask P H p W hW hF hInc
  have hz : a.val ∈ G := by
    change a ∈ (Subtype.val : W → Y) ⁻¹' G
    rw [hEq]
    exact hInc
  exact hNoBorn G hG (ha ▸ hz)

set_option maxHeartbeats 1600000 in
/-- The actual localized companion starts a full finite zero run whenever
the upper cut anchor misses the inherited born members. The older
members through the anchor were deleted by positive selection. -/
theorem exists_actual_localized_companion_zero_recognition {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hl : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let J := compAt L L.d (.refl : BlowupTower A A)
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    (¬ IsSpecial Sec H p) →
    (∀ F ∈ (geoTransformAlong (barMarked P) H).E.drop P.E.length, p ∉ F) →
    ∃ (a : C) (W : Opens B) (u : W → ℂ) (haW : a ∈ W), a.val.val = p ∧
      let D := CMfd.of (n := n+1) W
      let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      let aw : W := ⟨a, haW⟩
      IsInvDomain (k+1) Jw ∧ IsInvDomain k Rw ∧ LocWPEquiv (X := D) Jw Rw ∧
      IsTangentDirectionAlong Jw.N Jw.ideal Jw.d univ u ∧
      Jw.N ∩ {x | u x = 0} = Rw.N ∧ (∀ F ∈ Jw.E, aw ∉ F) ∧
      ∀ {Z : CMfd.{0} (n+1)} (G : BlowupTower D Z) (_hG : IsGeoTestTower Jw G)
        (z : Z), G.proj z = aw →
        level Rw G z = 0 ∧ stepRegime Jw 0 G z ∧
        regimeRun (stepRegime Jw 0) G z = G.length := by
  intro X P Sec r H S p O A L C B J R hNSS hNoBorn
  obtain ⟨a, W, u, haW, ha, hJw, hRw, hClass, hu, hTrace, _, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent Q hQ T hCan y hy hl hNS hNSS
  let D := CMfd.of (n := n+1) W
  let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
  let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
  let aw : W := ⟨a, haW⟩
  have hE : J.E = L.E.map ((Subtype.val : C → A) ⁻¹' ·) := by
    change (companionOf (n+1) (M := B)
      (MarkedIdeal.pullback (Subtype.val : C → A) L) L.d).E = _
    exact companionAlong_E _ _ _ _ _ _
  have hoffL : ∀ K ∈ L.E, a.val ∉ K := by
    change ∀ K ∈ (positiveMemberOn P H p O).E, a.val ∉ K
    exact off_positive_member_of_no_born (X := X) P H p O le_rfl a.val ha hNoBorn
  have hoffJ : ∀ G ∈ J.E, a ∉ G :=
    hE.symm ▸ no_incidence_map (Subtype.val : C → A) L.E a hoffL
  have hoff : ∀ F ∈ Jw.E, aw ∉ F :=
    no_incidence_map (Subtype.val : W → B) J.E aw hoffJ
  refine ⟨a, W, u, haW, ha, hJw, hRw, hClass, hu, hTrace, hoff, ?_⟩
  intro Z G hG z hz
  have h := zero_step_regime_of_strict_supported_trace Jw Rw hJw hRw hClass u hu hTrace
    G hG z (fun F hF => by rw [hz]; exact hoff F hF)
  exact ⟨(level_eq_of_E_eq hClass.wEquiv.1 G z).symm.trans h.1.1, h⟩

end
end Hironaka.HironakaG1CompanionZeroBranchRecognition
