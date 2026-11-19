import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical

/-! The actual next-born special branch on the localized supported record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LocalizedLaterBornSpecial
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec
  CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  HironakaG1LocalizedLaterBornCanonical HironakaG1RecursiveMemberValueTransport
  HironakaG1BornSelectedCompanionPhase HironakaG1ChosenCommonContactClassData
  TangentDirectionAlong CoefficientIdealRestriction
  HironakaG1ActualLaterCommonTangent HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaActualSectionBoundaryGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci
  HironakaActualRelativeNormalGeometry HironakaCoherentTransformExtension
  NonmonomialOrderTail GeneralValue HomogenizedIdealAlong InvDomainMemberRestriction
  RelativePrincipalizationSpan MemberInterLocusAlong GermIdealOrder BoundaryCount

private theorem special_level_pullback {n : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (W : Opens X) (a : W) :
    level (MarkedIdeal.pullback (Subtype.val : W → X) P)
      (.refl (X := CMfd.of (n := n) W)) a = level P (.refl (X := X)) a.val := by
  change BoundaryCount.boundaryCount ((P.E.map ((Subtype.val : W → X) ⁻¹' ·)).take
    (P.E.map ((Subtype.val : W → X) ⁻¹' ·)).length) a =
      BoundaryCount.boundaryCount (P.E.take P.E.length) a.val
  rw [List.take_length, List.take_length, BoundaryCount.boundaryCount_map]
  rfl

private theorem special_read {n q b : ℕ} {X : CMfd.{0} n} (hn : 0 < n)
    (R : MarkedIdeal n X) (a : X) (hl : level R (.refl (X := X)) a = b+1)
    (hsp : IsSpecial R (.refl (X := X)) a) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) R (.refl (X := X)) a =
      toLex (b+1, (⊤ : WithTop (ValTy q))) := by
  have h := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (X := X) (invFamily hn q) R
    (lowerMarkedM R) (.refl (X := X)) (y := a) hsp
  exact h.trans (congrArg (fun l => toLex (l, (⊤ : WithTop (ValTy q)))) hl)

set_option maxHeartbeats 700000 in
/-- At a positive special point the selected carrier is locally contained
in the selected cosupport. No open through this point can give that
member record a recursive domain. -/
theorem positive_special_member_no_domain {n : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (R : MarkedIdeal n X) (hR : R.IsWellFormed) (a : X)
    (hPos : 0 < level R (.refl (X := X)) a)
    (hSp : IsSpecial R (.refl (X := X)) a) (W : Opens X) (haW : a ∈ W) :
    let S := positiveMemberOn R (.refl (X := X)) a W
    let w : W := ⟨a, haW⟩
    w ∈ S.cosupp ∧ (∀ᶠ z in 𝓝 w, z ∈ S.N → z ∈ S.cosupp) ∧
      ∀ k : ℕ, ¬ IsInvDomain k S := by
  intro S w
  let B := barMarked (X := X) R
  let E₀ := origMembers R (.refl (X := X))
  let K := memberRestrict B (membersThrough B.E E₀ a)
  have hE₀ : ∀ H ∈ E₀, H ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hB := isWellFormed_barMarked (X := X) R hR
  have hK := isWellFormed_memberRestrict hn hB (membersThrough B.E E₀ a)
  have hp : a ∈ memberInterLocus B.N E₀ B.cosupp := by
    rcases hSp with ⟨h0, _⟩ | ⟨_, hS⟩
    · exact (Nat.ne_of_gt hPos h0).elim
    · exact hS
  obtain ⟨ha, hSat⟩ := mem_memberInterLocus_iff.mp hp
  have hCos : K.cosupp = B.cosupp ∩ memberInter B.E (membersThrough B.E E₀ a) :=
    cosupp_memberRestrict hB (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) _
  have haK : a ∈ K.cosupp := by
    rw [hCos, memberInter_membersThrough hE₀]
    exact ⟨ha, fun _ _ h => h⟩
  have hKS : ∀ᶠ y in 𝓝 a, y ∈ K.N → y ∈ K.cosupp := by
    filter_upwards [hSat] with y hSatY hy
    change y ∈ B.N ∩ memberInter B.E (membersThrough B.E E₀ a) at hy
    rw [hCos]
    exact ⟨hSatY hy.1 (by
      have he := hy.2
      rwa [memberInter_membersThrough hE₀] at he), hy.2⟩
  have hPull : S.cosupp = (Subtype.val : W → X) ⁻¹' K.cosupp :=
    cosupp_pullback_val K (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent h) W
  have hw : w ∈ S.cosupp := hPull ▸ haK
  have hW : ∀ᶠ z in 𝓝 w, z ∈ S.N → z ∈ S.cosupp := by
    have ht : Tendsto (Subtype.val : W → X) (𝓝 w) (𝓝 a) :=
      continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually hKS] with z hz hzN
    exact hPull ▸ hz hzN
  refine ⟨hw, hW, fun k hD => ?_⟩
  obtain ⟨g, hg, hFreq⟩ := hD.isNonzeroAlongAt w (S.cosupp_subset_N hw)
  have hMem := HomogenizedGlueing.eventually_mem hD.isWellFormed.isCoherent hg
  obtain ⟨z, ⟨hzN, hzNe⟩, hzg, hzW⟩ := (hFreq.and_eventually (hMem.and hW)).exists
  exact hzNe ((vanishesToOrderOn_one_iff hzN
    (GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hzg)).mp
    (((hzW hzN).2 g hzg).mono hD.one_le_d))

set_option maxHeartbeats 1300000 in
/-- On the actual order mask, the next-born supported special branch
reads the top value before and after localization. Its attempted finite
positive member cut has no recursive domain on any window through
the anchor. -/
theorem exists_actual_localized_later_born_special_read {n k s b q : ℕ}
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
    let I : BlowupTower B B := .refl
    (¬ IsSpecial Sec H p) →
    (∀ a : C, a.val.val = p → level J I a = b + 1 ∧ IsSpecial R I a) →
    ∃ (a : C) (W : Opens B) (haW : a ∈ W), a.val.val = p ∧
      let D := CMfd.of (n := n+1) W
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      let aw : W := ⟨a, haW⟩
      let Hr := BlowupTower.refl (X := D)
      let V := invFamily (Nat.succ_pos n) q
      level R I a = b+1 ∧ IsInvDomain k Rw ∧ IsSpecial Rw Hr aw ∧
      Seq.StepOneValueMasked.stepOneInvM V R I a = toLex (b+1, (⊤ : WithTop (ValTy q))) ∧
      Seq.StepOneValueMasked.stepOneInvM V Rw Hr aw = toLex (b+1, (⊤ : WithTop (ValTy q))) ∧
      aw ∉ maskA Rw Hr aw ∧
      ∀ E : Opens D, aw ∈ E → ∀ l : ℕ, ¬ IsInvDomain l (positiveMemberOn Rw Hr aw E) := by
  intro X P Sec r H S p O A L C B J R I hNSS hBorn
  obtain ⟨a, W, u, haW, ha, hJw, hRw, hClass, _, _, _, _, _, _⟩ :=
    exists_actual_later_common_supported_tangent Q hQ T hCan y hy hl hNS hNSS
  let D := CMfd.of (n := n+1) W
  let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
  let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
  let aw : W := ⟨a, haW⟩
  let Hr := BlowupTower.refl (X := D)
  obtain ⟨hlJ, hSp⟩ := hBorn a ha
  have hlJw : level Jw Hr aw = b+1 := (special_level_pullback J W aw).trans hlJ
  have hlRw : level Rw Hr aw = b+1 :=
    (level_eq_of_E_eq hClass.wEquiv.1 Hr aw).symm.trans hlJw
  have hlR : level R I a = b+1 := (special_level_pullback R W aw).symm.trans hlRw
  have hR : R.IsWellFormed := by
    have hP := properNormalMarked_isInvDomain Q hQ
    have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
    have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily (Nat.succ_pos n) (k+1))
      P hP hMax (Nat.succ_pos n) T hCan).2.1
    have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
    let BS := geoTransformAlong (barMarked Sec) H
    have hSec : IsInvDomain (k+1) Sec := section_projected_domain (k+1) Q.N Q.E Q.ideal Q.d hQ
    have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hHeadTest
    have hBST := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
    have hBS : BS.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked Sec hSec.isWellFormed) H hBST
    exact IsWellFormed.pullback_val (IsWellFormed.pullback_val
      (isWellFormed_memberRestrict (Nat.succ_pos n) hBS _) O) C
  have hSpw : IsSpecial Rw Hr aw :=
    (initial_positive_special_pullback_open_iff R hR hRw.one_le_d W aw
      (hlR ▸ Nat.succ_pos b)).mpr hSp
  have hNoMask : aw ∉ maskA Rw Hr aw := fun haM => (interior_subset haM).2 ⟨rfl, hSpw⟩
  refine ⟨a, W, haW, ha, hlR, hRw, hSpw, ?_, ?_, hNoMask, ?_⟩
  · exact special_read (X := B) (q := q) (Nat.succ_pos n) R a hlR hSp
  · exact special_read (X := D) (q := q) (Nat.succ_pos n) Rw aw hlRw hSpw
  · intro E hE
    exact (positive_special_member_no_domain (X := D) (Nat.succ_pos n)
      Rw hRw.isWellFormed aw (hlRw ▸ Nat.succ_pos b) hSpw E hE).2.2

set_option maxHeartbeats 900000 in
/-- Even when the padded companion is nonspecial and gives a genuine
prescribed contact, the supported special branch forces that contact
out of every finite recursive domain. -/
theorem born_selected_contact_no_domain_of_supported_special {n k l b : ℕ}
    (hn : 0 < n) {X : CMfd.{0} n} (J R : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (a : X) (haR : a ∈ R.N) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {x | u x = 0} = R.N)
    (hLevel : level J (.refl (X := X)) a = b+1)
    (hNS : ¬ IsSpecial J (.refl (X := X)) a)
    (hSp : IsSpecial R (.refl (X := X)) a) :
    let H := BlowupTower.refl (X := X)
    ∃ (W : Opens X) (haW : a ∈ W), W ≤ maskA J H a ∧
      let K := positiveMemberOn J H a W
      let S := positiveMemberOn R H a W
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      let w : W := ⟨a, haW⟩
      IsInvDomain (k-1) K ∧ C.N = S.N ∧ C.E = S.E ∧
      LocWPEquiv (X := CMfd.of (n := n) W) C S ∧
      w ∈ C.cosupp ∧ ∀ q : ℕ, ¬ IsInvDomain q C := by
  intro H
  have hRJ : R.N ⊆ J.N := fun _ hx => (hTrace ▸ hx).1
  have hu' : IsTangentDirectionAlong J.N J.ideal J.d (⊤ : Opens X) u := hu
  have hTrace' : J.N ∩ {x | u x = 0} ∩ (⊤ : Opens X) = R.N ∩ (⊤ : Opens X) := by
    rw [hTrace]
  obtain ⟨W, haW, _, hMask, hK, _, hN, _, hE, _, hLoc⟩ :=
    exists_born_selected_companion_contact hn J R hJ hR hClass hRJ a haR hLevel hNS
      ⊤ trivial u hu' hTrace'
  let S := positiveMemberOn R H a W
  let K := positiveMemberOn J H a W
  let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
  let w : W := ⟨a, haW⟩
  have hLevR : level R H a = b+1 := (level_eq_of_E_eq hClass.wEquiv.1 H a).symm.trans hLevel
  obtain ⟨hwS, _, hNo⟩ := positive_special_member_no_domain hn R hR.isWellFormed a
    (hLevR ▸ Nat.succ_pos b) hSp W haW
  have hB := isWellFormed_barMarked (X := X) R hR.isWellFormed
  let B := barMarked (X := X) R
  let I := membersThrough B.E (origMembers R H) a
  have hS := IsWellFormed.pullback_val (isWellFormed_memberRestrict hn hB I) W
  have hd : 1 ≤ S.d := one_le_memberRestrict_d B I
  have hCos : C.cosupp = S.cosupp := hLoc.cosupp_eq_base
  refine ⟨W, haW, hMask, hK, hN, hE, hLoc, hCos.symm ▸ hwS, fun q hq => ?_⟩
  exact hNo q (isInvDomain_of_sameCarrier_cosupp (X := CMfd.of (n := n) W) S C hq
    hS.isCoherent hd hN.symm hE.symm hCos.symm)

end
end Hironaka.HironakaG1LocalizedLaterBornSpecial
