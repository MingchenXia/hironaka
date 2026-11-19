import Hironaka.Resolution.HironakaG1LocalizedBornWindowRestriction
import Hironaka.Resolution.HironakaG1OriginalContactClassAtStage
import Hironaka.Resolution.HironakaG1AdvancingOrderZeroContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1AdvancingSupportedBornContact
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres TangentDirectionAlong
  CompanionRebase GeneralValue GeneralCompare NonmonomialOrderTail
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong CoefficientIdealRestriction RestrictedIdealExtension
  InvDomainTowerAlong ContactStageKept
  StepOneValue StepOneRegime StepOneValueMasked
  HironakaG1AdvancingOrderZeroContact HironakaG1OriginalContactClassAtStage
  HironakaG1ClassReferenceContact HironakaG8ContactMax HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1CoefficientCarrierClassData HironakaG1OriginalUnequalMarkCanonical HironakaG1ChosenCommonContactClassData
  HironakaG8GapNormalizedExponent HironakaG11InvBMClass
  HironakaActualCoefficientDivisorExponentGap HironakaCoherentTransformExtension
  RelativePrincipalizationSpan GermIdealPullbackCalculus DivisorExponentAlong GermIdealOrder
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

/-- The supported contact representative follows precisely the same
geometric tests as the padded source and its bar. -/
theorem supported_contact_local_class {n k : ℕ} {X : CMfd.{0} n}
    (K S : MarkedIdeal n X) (hK : IsInvDomain k K) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = S.N)
    (hNS : IsClosedSubmanifold n S.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) S) :
    LocWPEquiv K S := by
  let F := K.N ∩ {z | u z = 0}
  have hF : IsClosedSubmanifold n F := by rw [show F = S.N from hTrace]; exact hNS
  have hMax : MaxContact K F := by
    simpa only [inter_univ] using maxContact_base K hK.isWellFormed.isCoherent hu
  have hKC : LocWPEquiv K (withN (coeffMarkedAlong K) F) :=
    locWPEquiv_of_reference_maxContact K K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      rfl (LocEquiv.refl _ K) F hF inter_subset_left hMax
  exact hKC.trans hClass

set_option maxHeartbeats 1400000 in
/-- Advance the original supported bare-contact class along the very same
tested prefix, then compare it with the selected kept contact on the
same actual open. The supported mark stays at its original value,
and both records carry the entire stage boundary. -/
theorem advancing_kept_contact_supported_stage {n k l : ℕ}
    {X Y : CMfd.{0} n} (K S : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hS : IsInvDomain l S) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = S.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) S)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let D := contactMarkedKept K u H O
    let S' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong S H)
    IsGeoTestTower S H ∧ IsInvDomain l D ∧ IsInvDomain l S' ∧
      D.N = S'.N ∧ D.E = S'.E ∧ S'.d = S.d ∧ LocWPEquiv (X := A) D S' ∧
      HasCosupportGap (X := A) D := by
  intro A D S'
  have hKB := bar_local_any_boundary K hK
  have hTK := ((hKB.wEquiv.2 H).1).mpr hH
  have hKS := supported_contact_local_class K S hK u hu hTrace hS.isWellFormed.isClosedSubmanifold_N hClass
  have hBS := hKB.symm.trans hKS
  have hTS := ((hBS.wEquiv.2 H).1).mp hH
  have hCT := original_bar_local_to_reference_contact K K hK hK rfl (LocEquiv.refl _ K)
    (⊤ : Opens X) u hu H hTK O (fun _ _ => trivial)
  have hDS : LocWPEquiv (X := A) D S' := hCT.symm.trans ((hBS.geoTransformAlong H hH).restrict O)
  have hST := isInvDomain_geoTransformAlong hS H hTS
  have hSO : IsInvDomain l S' := isInvDomain_pullback_val O hST
  have hN : D.N = S'.N := by
    change (Subtype.val : O → Y) ⁻¹' strictAlong H (K.N ∩ {z | u z = 0}) =
      (Subtype.val : O → Y) ⁻¹' (geoTransformAlong S H).N
    rw [N_geoTransformAlong, hTrace]
  have hBT := isInvDomain_geoTransformAlong (isInvDomain_barMarked K hK) H hH
  let M := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong (barMarked K) H)
  have hM : IsInvDomain k M := isInvDomain_pullback_val O hBT
  have hD : D = withN (coeffMarkedAlong M) D.N := by
    change withN (MarkedIdeal.pullback (Subtype.val : O → Y) (coeffMarkedAlong (geoTransformAlong (barMarked K) H)))
      D.N = _
    rw [pullback_val_coeffMarkedAlong O _ hBT.isWellFormed.isCoherent
      hBT.isWellFormed.isClosedSubmanifold_N hBT.one_le_d]
  have hDN : D.N ⊆ M.N := fun z hz =>
    MaximalContactAlongTower.strictAlong_subset_N (barMarked K)
      (fun _ h => h.1) H hz
  have hDcoh : D.ideal.IsCoherent := by
    rw [hD]
    exact isCoherent_coeffMarkedAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N
  have hDd : 1 ≤ D.d := by
    rw [hD]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d M
  have hDO : IsInvDomain l D :=
    isInvDomain_of_sameCarrier_cosupp (X := A) D S' hSO hDcoh hDd hN hDS.wEquiv.1 hDS.cosupp_eq_base
  refine ⟨hTS, hDO, hSO, hN, hDS.wEquiv.1, ?_, hDS, ?_⟩
  · exact d_geoTransformAlong S H
  · rw [hD]
    intro z _ hz
    change z ∈ cosupport n D.N (coeffMarkedAlong M).ideal 1 at hz
    change z ∈ cosupport n D.N (coeffMarkedAlong M).ideal (coeffMarkedAlong M).d
    rwa [← coefficient_restriction_cosupport_gap M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d D.N hDN]

set_option maxHeartbeats 1200000 in
/-- A supported coefficient gap at the actual advanced cut supplies the
remaining normalized exponent comparison and exact recursive canonicality. -/
theorem advancing_kept_contact_supported_canonical {n k l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K S : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hS : IsInvDomain l S) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = S.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) S)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked K) H) (O : Opens Y) :
    let A := CMfd.of (n := n) O
    let D := contactMarkedKept K u H O
    let S' := MarkedIdeal.pullback (M' := A) (Subtype.val : O → Y) (geoTransformAlong S H)
    HasCosupportGap (X := A) S' →
    (∀ F ∈ D.E, ∀ z ∈ D.cosupp, z ∈ F →
      S'.d * divExpAlong n D.N D.ideal F z = D.d * divExpAlong n S'.N S'.ideal F z) ∧
    ∀ {Z : CMfd.{0} n} (T : BlowupTower A Z),
      IsCanonical D ((invFamily hn l).inv D) T ↔ IsCanonical S' ((invFamily hn l).inv S') T := by
  intro A D S' hGapS
  obtain ⟨_, hD, hSO, hN, _, _, hDS, hGapD⟩ :=
    advancing_kept_contact_supported_stage K S hK hS u hu hTrace hClass H hH O
  have hDim := SameCarrierDim.of_N_eq (X := A) (A := D) (B := S') hN
  have hExp := normalized_exponents_of_gap_sameCarrierDim hn D S' hD hSO hDS hDim hGapD hGapS
  exact ⟨hExp, fun T => invFamily_isCanonical_iff_of_local hn D S' hD hSO hDS hDim hExp T⟩


open HironakaG1LocalizedBornWindowRestriction ContactRepresentative ContactEquivalenceAlong

set_option maxHeartbeats 2000000 in
/-- On the actual advancing zero branch, the supported selected record
advances along the same literal tested head. Its restriction has the
same carrier, entire stage boundary, recursive domain and surviving
endpoint as the actual prescribed contact. A gap on the advanced
supported record suffices to transfer exact recursive CAN. -/
theorem actual_zero_head_advances_supported_born {n k : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k + 1) K) (hR : IsInvDomain k R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {z | u z = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {z | u z = 0})) R)
    (hEq : companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X)) :
    let C := ordMask (geoTransformAlong K (.refl : BlowupTower X X)) K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let Rc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) R
    let v : C → ℂ := u ∘ Subtype.val
    ∀ {Y : CMfd.{0} n} (T : BlowupTower A Y),
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T →
      ∀ y ∈ (geoTransformAlong J T).cosupp,
      level J T y = 0 → (¬ IsSpecial J T y) →
      let r := regimeRun (stepRegime J 0) T y
      let H := head T r
      let S := tail T r
      let p := S.proj y
      let O := maskB J H p
      let Y₀ := (split T r).1
      let B := CMfd.of (n := n) O
      let D := contactMarkedKept Kc v H O
      let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → Y₀) (geoTransformAlong Rc H)
      ∃ hp : p ∈ O,
        IsGeoTestTower Rc H ∧ IsInvDomain k D ∧ IsInvDomain k R' ∧
        D.N = R'.N ∧ D.E = R'.E ∧ R'.d = R.d ∧ LocWPEquiv (X := B) D R' ∧
        IsCanonical D ((invFamily hn k).inv D) (restrict O S) ∧
        IsGeoTestTower R' (restrict O S) ∧
        (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong R' (restrict O S)).cosupp ∧
        (HasCosupportGap (X := B) R' → IsCanonical R' ((invFamily hn k).inv R') (restrict O S)) := by
  intro C A J Kc Rc v Y T hCan y hy hl hNS r H S p O Y₀ B D R'
  obtain ⟨hp, _, hDCan, hDCos, _, _, _, _, _, _⟩ :=
    order_companion_actual_zero_head_contact hn K hK u hu hEq T hCan y hy hl hNS
  have hJ : IsInvDomain (k + 1) J := isInvDomain_compAt hn hK.one_le_d (.refl : BlowupTower X X) hK
  have hMax := isMaximalOrderAlong_compAt hn K.d (.refl : BlowupTower X X) hK
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn k)
    J hJ hMax hn T hCan).1
  have hH := ((isGeoTestTower_iff_head_tail (barMarked J) T r).mp hT).1
  have hKc : IsInvDomain (k + 1) Kc := isInvDomain_pullback_val C hK
  have hRc : IsInvDomain k Rc := isInvDomain_pullback_val C hR
  let F := companionOf n K K.d
  have hF : F.IsWellFormed := HironakaG8E4cCompanion.companion_wf hK hn hK.one_le_d
  have hFJ : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hK.isWellFormed hK.isNonzeroAlongAt C K.d
  have hFRE : RestrictEquiv F K := by
    unfold F
    rw [hEq]
    exact ⟨rfl, rfl, rfl, restrictLe_restrictOn, restrictLe_self_restrictOn hK.isWellFormed.isCoherent⟩
  have hJK : RestrictEquiv J Kc := by
    rw [← hFJ]
    exact restrictEquiv_pullback_val C hFRE hF.isCoherent hK.isWellFormed.isCoherent
  have hBar := restrictEquiv_barMarked hJK hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hKc.isWellFormed.isCoherent
  have hJB := isInvDomain_barMarked (X := A) J hJ
  have hKB := isInvDomain_barMarked (X := A) Kc hKc
  have hHK := ((RestrictEquiv.wEquiv hBar hJB.isWellFormed.isClosedSubmanifold_N.1
    hJB.isWellFormed.isCoherent hKB.isWellFormed.isCoherent).2 H).1.mp hH
  have hv : IsTangentDirectionAlong Kc.N Kc.ideal Kc.d univ v :=
    isTangentDirectionAlong_pullback_val C
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf)
      ⟨C.isOpen, fun x _ => hu.mem x (mem_univ x), fun x _ => hu.multiplicity_one x (mem_univ x)⟩
  have hTraceC : Kc.N ∩ {z | v z = 0} = Rc.N := by
    change (Subtype.val : C → X) ⁻¹' (K.N ∩ {z | u z = 0}) = (Subtype.val : C → X) ⁻¹' R.N
    rw [hTrace]
  have hClassC := hClass.restrict C
  rw [selected_bare_contact_pullback_val K hK.isWellFormed hK.one_le_d u C] at hClassC
  obtain ⟨hRH, hD, hR', hN, hE, hd, hL, _⟩ :=
    advancing_kept_contact_supported_stage Kc Rc hKc hRc v hv hTraceC hClassC H hHK O
  have hDT := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hD (restrict O S) hDCan
  have hBoth := hL.wEquiv.2 (restrict O S)
  refine ⟨hp, hRH, hD, hR', hN, hE, hd, hL, hDCan, hBoth.1.mp hDT, hBoth.2 hDT ▸ hDCos, ?_⟩
  intro hGap
  have hCanIff := (advancing_kept_contact_supported_canonical hn Kc Rc hKc hRc v hv hTraceC
    hClassC H hHK O hGap).2 (restrict O S)
  exact hCanIff.mp hDCan

end
end Hironaka.HironakaG1AdvancingSupportedBornContact
