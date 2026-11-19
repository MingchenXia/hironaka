import Hironaka.Resolution.HironakaG1ChronologicalTrueMarkZero
import Hironaka.Resolution.HironakaG1ChronologicalSupportDomainObstruction
import Hironaka.Resolution.HironakaG1AdvancingSupportedContactExponents

/-! Local numerical control on the literal advancing zero branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1LocalBornOrderContinuation

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres MarkedIdealBiholomorphism
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime TangentDirectionAlong
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci InvDomainTowerAlong
  HironakaCoherentTransformExtension HironakaG1RecursiveMemberValueTransport
  HironakaG1ChronologicalCompanionSuffix HironakaG1ChronologicalTrueMarkZero
  HironakaG1ChronologicalSupportDomainObstruction HironakaG1AdvancingSupportPowerGap
  CoefficientIdealRestriction ContactEquivalenceAlong InvDomainMemberRestriction
  BoundaryCount DivisorExponentAlong AnalyticDimensionBasics RelativePrincipalizationSpan
  HironakaG3RRawRegimeLocality HironakaG1LocalizedBornWindowRestriction DerivativeIdealAlongEtale

open Filter Classical HironakaG1AdvancingSupportedContactExponents
open scoped Topology

open HironakaG1ChronologicalSupportDimensionSplit RestrictedIdealExtension ContactStageKept CompanionRebase GeneralValue GeneralCompare
  NonmonomialOrderTail HironakaG1AdvancingSupportedBornContact
  HironakaG8LocalRestrictEquiv HironakaG1SupportedGapEmptyEpoch
  MarkedIdealOperationsAlong.MarkedIdeal HironakaActualPowerBoundaryExponents RestrictLeCalculus
  HironakaG1InitialPositiveGeneralRead ContactRepresentative HironakaG8GapNormalizedExponent
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 2000000 in
/-- At the literal advancing zero head, only newly born slots whose
supported exponent is positive and whose contact exponent vanishes need
a local numerical lower bound. The inherited slots use the source gap. -/
theorem selected_suffix_finite_zero_of_local_born_order {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k+1) K) (hR : IsInvDomain k R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {x | u x = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})) R)
    (hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k+1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    let C := ordMask K K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let Rc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) R
    let v : C → ℂ := u ∘ Subtype.val
    let V := restrict C T
    J.d = K.d ∧ J.E = K.E.map ((Subtype.val : C → X) ⁻¹' ·) ∧
    ∃ hp : T.proj y ∈ C,
      let z : openPreimage T C := ⟨y, hp⟩
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
      z ∈ (geoTransformAlong J V).cosupp ∧
      ((∀ F ∈ J.E, z ∉ strictAlong V F) →
        HasCosupportGap (X := A) Rc →
        let r := regimeRun (stepRegime J 0) V z
        let H := head V r
        let S := tail V r
        let p := S.proj z
        let O := maskB J H p
        let B := CMfd.of (n := n) O
        let D := contactMarkedKept Kc v H O
        let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → _) (geoTransformAlong Rc H)
        (∀ F ∈ D.E, ∀ x ∈ D.cosupp, x ∈ F →
          (¬ ∃ i : Fin Rc.E.length, F = (Subtype.val : O → _) ⁻¹' strictAlong H (Rc.E.get i)) →
          divExpAlong n D.N D.ideal F x = 0 → 0 < divExpAlong n R'.N R'.ideal F x →
          R'.d ≤ divExpAlong n R'.N R'.ideal F x) →
        ∃ hq : p ∈ O,
          let w : openPreimage S O := ⟨z, hq⟩
          let G := restrict O S
          IsGeoTestTower Rc H ∧ IsInvDomain k D ∧ IsInvDomain k R' ∧
          D.N = R'.N ∧ D.E = R'.E ∧ R'.d = R.d ∧ LocWPEquiv D R' ∧
          D.N = (Subtype.val : O → _) ⁻¹' strictAlong H Rc.N ∧
          D.E = (J.E.map (strictAlong H) ++
            (geoTransformAlong (barMarked J) H).E.drop J.E.length).map
              ((Subtype.val : O → _) ⁻¹' ·) ∧
          IsCanonical D ((invFamily hn k).inv D) G ∧ IsGeoTestTower R' G ∧
          w ∈ (geoTransformAlong D G).cosupp ∧ w ∈ (geoTransformAlong R' G).cosupp ∧
          IsCanonical R' ((invFamily hn k).inv R') G ∧
          (invFamily hn (k+1)).inv K T y = positiveSuccessorRead K.d
            (toLex (0, ((invFamily hn k).inv D G w : WithTop (ValTy k))))) := by
  intro C A J Kc Rc v V
  obtain ⟨_, hEq⟩ := true_mark_of_retained_boundary_zero K hK hu hExp
  have hBase := supported_contact_local_class K R hK u hu hTrace
    hR.isWellFormed.isClosedSubmanifold_N hClass
  let F := companionOf n K K.d
  have hF : IsInvDomain (k+1) F :=
    InvDomainCompanion.isInvDomain_companionAlong (X := X) (𝔪 := K) hn hK hK.one_le_d
  have hFJ : MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) F = J :=
    pullback_val_companionOf hn hK.isWellFormed hK.isNonzeroAlongAt C K.d
  have hRE : RestrictEquiv K F := by
    rw [show F = _ from hEq]
    exact ⟨rfl,rfl,rfl,restrictLe_self_restrictOn hK.isWellFormed.isCoherent,restrictLe_restrictOn⟩
  have hKcRE : RestrictEquiv Kc J := by
    rw [← hFJ]
    exact restrictEquiv_pullback_val C hRE hK.isWellFormed.isCoherent hF.isWellFormed.isCoherent
  have hKc := isInvDomain_pullback_val C hK
  have hRc := isInvDomain_pullback_val C hR
  have hDomJ : IsInvDomain (k+1) J := isInvDomain_compAt hn hK.one_le_d (.refl : BlowupTower X X) hK
  have hMaxJ := isMaximalOrderAlong_compAt hn K.d (.refl : BlowupTower X X) hK
  have hJR : LocWPEquiv (X := A) J Rc :=
    (locWPEquiv_of_restrictEquiv hKc hDomJ hKcRE).symm.trans (hBase.restrict C)
  have hTanF : IsTangentDirectionAlong F.N F.ideal F.d univ u := by
    rw [show F = _ from hEq]
    exact ⟨hu.isOpen, fun x hx => HomogenizedGlueingLiftAlong.iterDerivIdealAlong_mono
      (N := K.N) (le_restrictOn hK.isWellFormed.isCoherent) (K.d-1) x u (hu.mem x hx),
      hu.multiplicity_one⟩
  have hV : IsTangentDirectionAlong J.N J.ideal J.d univ v := by
    rw [← hFJ]
    exact isTangentDirectionAlong_pullback_val C
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hF.isWellFormed.isCoherent hf)
      ⟨C.isOpen, fun x _ => hTanF.mem x (mem_univ _), fun x _ => hTanF.multiplicity_one x (mem_univ _)⟩
  have hTraceC : J.N ∩ {x | v x = 0} = Rc.N := by
    rw [← hKcRE.N_eq]
    change (Subtype.val : C → X) ⁻¹' (K.N ∩ {x | u x = 0}) = _
    rw [hTrace]
    rfl
  obtain ⟨hd,hE,hp,hCanJ,hCosJ,hZero⟩ :=
    selected_suffix_true_mark_zero_contact hn K R hK hR u hu hTrace hClass hExp T hCan y hy
  let z : openPreimage T C := ⟨y,hp⟩
  refine ⟨hd,hE,hp,hCanJ,hCosJ,?_⟩
  intro hOff hGap r H S p O B D R' hBorn
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn k)
    J hDomJ hMaxJ hn V hCanJ).2.1
  have hReg := (finite_zero_iff_off_retained_strict_boundary J Rc hDomJ hRc hJR
    v hV hTraceC V hT z).mpr hOff
  obtain ⟨hq,hRH,hD,hR',hN,hEqE,hRd,hLoc,hStrict,hChron,hCanD,hTestR,hw,hwR,hCanR,hRead⟩ :=
    hZero hReg.1 hReg.2
  have hBarTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn k)
    J hDomJ hMaxJ hn V hCanJ).1
  have hJH := ((isGeoTestTower_iff_head_tail (barMarked J) V r).mp hBarTest).1
  have hJK : RestrictEquiv J Kc := ⟨hKcRE.N_eq.symm,hKcRE.E_eq.symm,hKcRE.d_eq.symm,hKcRE.N_eq ▸ hKcRE.ge,hKcRE.N_eq ▸ hKcRE.le⟩
  have hBar := restrictEquiv_barMarked hJK hDomJ.isWellFormed.isClosedSubmanifold_N
    hDomJ.isWellFormed.isCoherent hKc.isWellFormed.isCoherent
  have hJB := isInvDomain_barMarked J hDomJ
  have hKB := isInvDomain_barMarked Kc hKc
  have hKH := ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hBar
    hJB.isWellFormed.isClosedSubmanifold_N.1 hJB.isWellFormed.isCoherent
      hKB.isWellFormed.isCoherent).2 H).1.mp hJH
  have hvK : IsTangentDirectionAlong Kc.N Kc.ideal Kc.d univ v :=
    isTangentDirectionAlong_pullback_val C
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf)
      ⟨C.isOpen, fun x _ => hu.mem x (mem_univ _), fun x _ => hu.multiplicity_one x (mem_univ _)⟩
  have hTraceK : Kc.N ∩ {x | v x = 0} = Rc.N := by
    rw [hKcRE.N_eq]
    exact hTraceC
  have hClassC := hClass.restrict C
  rw [selected_bare_contact_pullback_val K hK.isWellFormed hK.one_le_d u C] at hClassC
  have hComp := advancing_supported_canonical_of_new_trace hn Kc Rc hKc hRc v hvK
    hTraceK hClassC hGap H hKH O
  have hTraceBorn : ∀ F ∈ D.E, ∀ x ∈ D.cosupp, x ∈ F →
      (¬ ∃ i : Fin Rc.E.length, F = (Subtype.val : O → _) ⁻¹' strictAlong H (Rc.E.get i)) →
      divExpAlong n D.N D.ideal F x = 0 → 0 < divExpAlong n R'.N R'.ideal F x →
      ∀ᶠ w in 𝓝 x, w ∈ D.N → w ∈ F → w ∈ D.cosupp := by
    intro F hF x hx hxF hNew hD0 hPos
    have hxR : x ∈ R'.N := hN ▸ D.cosupp_subset_N hx
    have hFR : F ∈ R'.E := hEqE ▸ hF
    obtain ⟨j,rfl⟩ := List.get_of_mem hFR
    have hDiv := (isDivNearAlong_get_iff_le hR'.isWellFormed.isClosedSubmanifold_N
      hR'.isWellFormed.isCoherent j hxR hxF (hR'.isNonzeroAlongAt x hxR)).mpr
        (hBorn _ hF x hx hxF hNew hD0 hPos)
    filter_upwards [hDiv] with w hw hwD hwF
    exact hLoc.cosupp_eq_base.symm ▸ hw (hN ▸ hwD) hwF
  have hCan' := ((hComp hTraceBorn).2 (restrict O S)).mp hCanD
  exact ⟨hq,hRH,hD,hR',hN,hEqE,hRd,hLoc,hStrict,hChron,hCanD,hTestR,hw,hwR,hCan',hRead⟩

open HironakaG1DifferentCarrierMemberClassData

/-- At any actual supported tested head, the selected coefficient member
has the ordinary gap, including when the test has genuine centers.
Further open restrictions preserve the same selected gap and mark. -/
theorem chronological_supported_source_gap {n l : ℕ}
    {X Y : CMfd.{0} n} (R : MarkedIdeal n X) (hR : IsInvDomain l R)
    (H : BlowupTower X Y) (hH : IsGeoTestTower R H) (p : Y)
    (O : Opens Y) :
    HasCosupportGap (positiveMemberOn R H p O) := by
  let B := geoTransformAlong (barMarked R) H
  have hTest := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hH
  have hB := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hTest
  exact member_open_hasCosupportGap B hB (membersThrough B.E (origMembers R H) p) O

/-- An exact current coefficient presentation on the actual carrier is
a second way of certifying the gap. No whole power presentation is needed. -/
theorem cosupport_gap_of_current_coefficient_presentation {n l : ℕ}
    {X : CMfd.{0} n} (B : MarkedIdeal n X) (hB : IsInvDomain l B)
    (I : Finset (Fin B.E.length)) (O : Opens X)
    (R : MarkedIdeal n (CMfd.of (n := n) O))
    (hExact : RestrictEquiv R
      (MarkedIdeal.pullback (Subtype.val : O → X) (memberRestrict B I))) :
    HasCosupportGap R :=
  cosupport_gap_of_restrictEquiv hExact (member_open_hasCosupportGap B hB I O)

open HironakaG1ActualLaterOrderRun HironakaG1LocalizedBornNormalHistory NonmonomialOrderLocal
  MemberInterTowerAlong BoundaryCount

set_option maxHeartbeats 1400000 in
/-- A retained divisor that survives at the true-mark companion endpoint
forces positive level. The actual inner positive letter is either special
top or the value of the tested canonical suffix at its own chronological
positive head. The original general invariant keeps the true mark. -/
theorem true_mark_positive_continuation_of_surviving_slot {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : IsInvDomain (k+1) K)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k+1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    let C := ordMask K K.d
    let _A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let U := restrict C T
    J.E = K.E.map ((Subtype.val : C → X) ⁻¹' ·) ∧
    ∃ hp : T.proj y ∈ C,
      let z : openPreimage T C := ⟨y,hp⟩
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) U ∧
      z ∈ (geoTransformAlong J U).cosupp ∧
      ((∃ F ∈ J.E, z ∈ strictAlong U F) →
      ∃ b : ℕ, level J U z = b+1 ∧
        ((IsSpecial J U z ∧
            (invFamily hn (k+1)).inv K T y =
              positiveSuccessorRead K.d (toLex (b+1, (⊤ : WithTop (ValTy k))))) ∨
          (¬ IsSpecial J U z ∧
            let r := regimeRun (stepRegime J (b+1)) U z
            let H := head U r
            let S := tail U r
            let p := S.proj z
            let O := maskA J H p
            let B := geoTransformAlong (barMarked J) H
            let P := positiveMemberOn J H p O
            IsGeoTestTower (barMarked J) H ∧
            P.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
              ((Subtype.val : O → _) ⁻¹' ·) ∧
            ∃ hO : p ∈ O,
              let w : openPreimage S O := ⟨z,hO⟩
              let V := restrict O S
              IsInvDomain k P ∧ IsCanonical P ((invFamily hn k).inv P) V ∧
              IsGeoTestTower P V ∧ w ∈ (geoTransformAlong P V).cosupp ∧
              (invFamily hn (k+1)).inv K T y =
                positiveSuccessorRead K.d (toLex (b+1,
                  ((invFamily hn k).inv P V w : WithTop (ValTy k))))))) := by
  classical
  intro C A J U
  obtain ⟨hOrder, hEq⟩ := true_mark_of_retained_boundary_zero K hK hu hExp
  have hTest := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hOrders {Z : CMfd.{0} n} (V : BlowupTower X Z) (hV : IsGeoTestTower K V) :
      ∀ z ∈ (geoTransformAlong K V).cosupp, nmOrd (geoTransformAlong K V) z = K.d :=
    (same_mark_test_order_and_strict_contact hn K hK u hu hOrder hEq V hV).1
  have hRun := order_run_of_all_test_orders K hK K.d (fun V => hOrders V) T hTest y hy
  obtain ⟨hE,hp,hJ,hMax,hCanJ,hz,hRead⟩ :=
    original_positive_initial_order_companion hn K hK T hCan y hy K.d
      (hOrders T hTest y hy) hK.one_le_d hRun
  let z : openPreimage T C := ⟨y,hp⟩
  refine ⟨hE,hp,hCanJ,hz,?_⟩
  rintro ⟨F,hF,hzF⟩
  have hOrig : origMembers J U = J.E.map (strictAlong U) :=
    take_E_geoTransformAlong (barMarked J) U
  have hZero : level J U z ≠ 0 := by
    intro hZero
    change boundaryCount (origMembers J U) z = 0 at hZero
    rw [hOrig, boundaryCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_map.mpr ⟨F,hF,rfl⟩ :
      strictAlong U F ∈ J.E.map (strictAlong U))
    exact hZero (Finset.mem_univ i) (hi.symm ▸ hzF)
  let b := level J U z - 1
  have hl : level J U z = b+1 := by dsimp [b]; omega
  refine ⟨b,hl,?_⟩
  by_cases hSp : IsSpecial J U z
  · have hTop := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn k) J
      (lowerMarkedM J) U hSp
    rw [hl] at hTop
    exact Or.inl ⟨hSp,hRead.trans (congrArg (positiveSuccessorRead K.d) hTop)⟩
  · obtain ⟨hHead,_,_,_,_,hSlots,hpO,hP,hCanP,hTestP,hw,hVal⟩ :=
      positive_companion_chronological_suffix hn J hJ hMax U hCanJ z hz hl hSp
    exact Or.inr ⟨hSp,hHead,hSlots,hpO,hP,hCanP,hTestP,hw,
      hRead.trans (congrArg (positiveSuccessorRead K.d) hVal)⟩

#print axioms selected_suffix_finite_zero_of_local_born_order
#print axioms chronological_supported_source_gap
#print axioms cosupport_gap_of_current_coefficient_presentation
#print axioms true_mark_positive_continuation_of_surviving_slot

end Hironaka.HironakaG1LocalBornOrderContinuation
