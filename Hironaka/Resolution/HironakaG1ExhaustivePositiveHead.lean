import Hironaka.Resolution.HironakaG1ChronologicalTrueMarkZero
import Hironaka.Resolution.HironakaG1ChronologicalSupportDomainObstruction

/-! The finite and special branches on the same actual chronological head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1ExhaustivePositiveHead

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

set_option maxHeartbeats 2000000 in
/-- Regularity on the actual selected supported head suffices after a
common shrinking. The calculation uses the selected suffix's true
mark and ordered boundary inherited from the original history. -/
theorem regular_chronological_head_true_mark {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y)
    (u : X → ℂ)
    (hu : IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d
      (⊤ : Opens X) u)
    (hTrace : (barMarked J).N ∩ {x | u x = 0} = R.N) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    ¬ IsSpecial R H p →
    ∃ (D F : CMfd.{0} n) (M P : MarkedIdeal n D) (w : D → ℂ) (U : BlowupTower D F) (z : F),
      IsInvDomain (k+1) M ∧ IsInvDomain k P ∧
      IsTangentDirectionAlong M.N M.ideal M.d univ w ∧ M.N ∩ {x | w x = 0} = P.N ∧
      LocWPEquiv (withN (coeffMarkedAlong M) (M.N ∩ {x | w x = 0})) P ∧
      (∀ G ∈ M.E, ∀ a, divExpAlong n M.N M.ideal G a = 0) ∧
      IsCanonical M ((invFamily hn (k+1)).inv M) U ∧ z ∈ (geoTransformAlong M U).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y =
        toLex (b+1, ((invFamily hn (k+1)).inv M U z : WithTop (ValTy (k+1)))) := by
  intro r H S p hNSR
  obtain ⟨O, hpO, _, _, hDom⟩ :=
    chronological_supported_domain_of_nonspecial_anchor hn J R hJ hR hClass
      hMax T hCan y hy hLevel hNS hNSR
  obtain ⟨hHead, _, hB, _, _, _, _, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  obtain ⟨V, v, _, _, hBarTan, hTan, _, hContactN, _, _, _, hContactClass,
      hpV, hK, hCanK, _, hyK, hRead⟩ :=
    positive_companion_chronological_tangent (k := k+1) hn J R hJ hR hClass hMax
      T hCan y hy hLevel hNS u hu hTrace
  let A := CMfd.of (n := n) V
  let K : MarkedIdeal n A := positiveMemberOn J H p V
  let K' : MarkedIdeal n A := positiveMemberOn R H p V
  let S₀ := restrict V S
  let z₀ : openPreimage S V := ⟨y,hpV⟩
  let O' : Opens (split T r).1 := V ⊓ O
  have hOV : O' ≤ V := inf_le_left
  let W := MaxLocusLocal.nestedOpens V O'
  let B := CMfd.of (n := n) W
  let L : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) K
  let P : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) K'
  let w : B → ℂ := fun x => v x.val.val
  let U := restrict W S₀
  have hpW : S₀.proj z₀ ∈ W := by
    change (S₀.proj z₀).val ∈ O'
    rw [show (S₀.proj z₀).val = p from proj_restrict V S z₀]
    exact ⟨hpV,hpO⟩
  let z : openPreimage S₀ W := ⟨z₀,hpW⟩
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hHead
  have hRH := (hClass.wEquiv.2 H).1.mp hJH
  have hDH := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRH
  let D := geoTransformAlong (barMarked R) H
  let P₀ := memberRestrict D (membersThrough D.E (origMembers R H) p)
  have hD := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hDH
  have hP₀ := isWellFormed_memberRestrict hn hD.isWellFormed (membersThrough D.E (origMembers R H) p)
  have hP : IsInvDomain k P := by
    have hEq := MaxLocusLocal.pullback_val_pullback_val (𝔪 := P₀) hP₀.isCoherent hOV
    change IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → A)
      (MarkedIdeal.pullback (Subtype.val : V → _) P₀))
    rw [hEq]
    exact isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hOV)
      ((hDom O' inf_le_right).2)
  have hL : IsInvDomain (k+1) L := isInvDomain_pullback_val W hK
  have hHol : ∀ x g, K.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hg
  have hTanL : IsTangentDirectionAlong L.N L.ideal L.d univ w :=
    isTangentDirectionAlong_pullback_val W hHol
      ⟨W.isOpen, fun x _ => hTan.mem x (mem_univ _), fun x _ => hTan.multiplicity_one x (mem_univ _)⟩
  have hTraceL : L.N ∩ {x | w x = 0} = P.N := by
    change (Subtype.val : W → A) ⁻¹' (K.N ∩ {x : V | v x.val = 0}) = _
    exact congrArg (fun C : Set A => (Subtype.val : W → A) ⁻¹' C) hContactN
  have hWPL : LocWPEquiv (withN (coeffMarkedAlong L) (L.N ∩ {x | w x = 0})) P := by
    have h0 := selected_bare_contact_pullback_val K hK.isWellFormed hK.one_le_d (v ∘ Subtype.val) W
    exact Eq.mp (congrArg (fun C : MarkedIdeal n B => LocWPEquiv C P) h0)
      (hContactClass.restrict W)
  let I := invFamily hn (k+1)
  have hCanL := Seq.ResolutionInvariantExt.isCanonical_restrict I hK W S₀ hCanK
  have hz : z ∈ (geoTransformAlong L U).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → A) K) (restrict W S₀)).cosupp
    rw [cosupp_restrict_raw K hHol W S₀]
    exact hyK
  have hPowK := historical_selected_full_normal_power J H p V v hB.isWellFormed hB.one_le_d hBarTan
  have hPowL (x : B) : L.ideal.mem x (fun a => w a ^ L.d) := by
    exact comp_mem_pullback (isLocalInverseAt_val (n := n) W x).mdiff (hPowK x.val)
      (hHol x.val _ (hPowK x.val))
  obtain ⟨G, hpG, hM, hR', hTanM, hTraceM, hWPM, hExp, _, _, hCanM, hEnd, hVal⟩ :=
    exists_selected_true_mark_canonical_window hn L P hL hP w hTanL hTraceL hWPL hPowL
      U hCanL z hz
  have hValL := I.isInvValue.restrictOpen K hK W S₀ hCanK z hyK
  refine ⟨_, _, _, _, _, _, _, hM, hR', hTanM, hTraceM, hWPM, hExp, hCanM, hEnd, ?_⟩
  exact hRead.trans (congrArg (fun q : ValTy (k+1) => toLex (b+1, (q : WithTop (ValTy (k+1)))))
    (hVal.trans hValL).symm)

open HironakaG1ChronologicalSupportDimensionSplit RestrictedIdealExtension ContactStageKept CompanionRebase GeneralValue GeneralCompare
  NonmonomialOrderTail HironakaG1AdvancingSupportedBornContact
  HironakaG8LocalRestrictEquiv HironakaG1SupportedGapEmptyEpoch
  MarkedIdealOperationsAlong.MarkedIdeal HironakaActualPowerBoundaryExponents RestrictLeCalculus
  HironakaG1InitialPositiveGeneralRead ContactRepresentative HironakaG8GapNormalizedExponent
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 2000000 in
/-- The regular selected suffix reaches finite zero precisely on the
retained-slot avoidance test. At that actual zero head a whole power of
a mark-one supported record supplies supported canonicality. -/
theorem selected_suffix_finite_zero_of_strict_avoidance_and_power {n k : ℕ} (hn : 0 < n)
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
        (∃ (m e : ℕ) (Q : MarkedIdeal n A),
          IsInvDomain m Q ∧ Q.d = 1 ∧ 1 ≤ e ∧ RestrictEquiv Rc (powerMarked Q e)) →
        let r := regimeRun (stepRegime J 0) V z
        let H := head V r
        let S := tail V r
        let p := S.proj z
        let O := maskB J H p
        let B := CMfd.of (n := n) O
        let D := contactMarkedKept Kc v H O
        let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → _) (geoTransformAlong Rc H)
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
  intro hOff hPow r H S p O B D R'
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn k)
    J hDomJ hMaxJ hn V hCanJ).2.1
  have hReg := (finite_zero_iff_off_retained_strict_boundary J Rc hDomJ hRc hJR
    v hV hTraceC V hT z).mpr hOff
  obtain ⟨hq,hRH,hD,hR',hN,hEqE,hRd,hLoc,hStrict,hChron,hCanD,hTestR,hw,hwR,hCanR,hRead⟩ :=
    hZero hReg.1 hReg.2
  obtain ⟨m,e,Q,hQ,hQd,he,hPower⟩ := hPow
  have hGap := cosupport_gap_geoTransformAlong_of_mark_one_power Q Rc hQ hRc hQd e he hPower H hRH
  have hGapO : HasCosupportGap (X := B) R' :=
    cosupport_gap_pullback_val _ (isInvDomain_geoTransformAlong hRc H hRH).isWellFormed.isCoherent hGap O
  exact ⟨hq,hRH,hD,hR',hN,hEqE,hRd,hLoc,hStrict,hChron,hCanD,hTestR,hw,hwR,hCanR hGapO,hRead⟩

set_option maxHeartbeats 2200000 in
/-- The actual positive canonical head has two exhaustive supported
branches. Full-dimensional saturation gives the literal top letter
and precludes any finite supported domain. Strict dimension drop
produces the true-mark canonical suffix and its genuine zero
continuation whenever the retained-slot and power tests hold. -/
theorem exhaustive_actual_positive_head {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y)
    (u : X → ℂ)
    (hu : IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d
      (⊤ : Opens X) u)
    (hTrace : (barMarked J).N ∩ {x | u x = 0} = R.N) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let p := (tail T r).proj y
    let A := geoTransformAlong (barMarked J) H
    let B := geoTransformAlong (barMarked R) H
    let Q := memberRestrict B (membersThrough B.E (origMembers R H) p)
    ∃ d, RegularAtDim (n := n) Q.N p d ∧
      ((LocDimGE (n := n) (Q.N ∩ A.cosupp) p d ∧
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) R H p =
            toLex (b+1, (⊤ : WithTop (ValTy k))) ∧
          ∀ (W : Opens (split T r).1), p ∈ W → ∀ q, ¬ IsInvDomain q (positiveMemberOn R H p W)) ∨
        (¬ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d ∧
          ∃ (D Z : CMfd.{0} n) (M P : MarkedIdeal n D)
            (U : BlowupTower D Z) (z : Z),
            IsInvDomain (k+1) M ∧ IsInvDomain k P ∧
            IsCanonical M ((invFamily hn (k+1)).inv M) U ∧ z ∈ (geoTransformAlong M U).cosupp ∧
            Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y =
              toLex (b+1, ((invFamily hn (k+1)).inv M U z : WithTop (ValTy (k+1)))) ∧
            let C := ordMask M M.d
            let E := CMfd.of (n := n) C
            let F := compAt M M.d (.refl : BlowupTower D D)
            let Pc := MarkedIdeal.pullback (M' := E) (Subtype.val : C → D) P
            let V := restrict C U
            ∃ hp : U.proj z ∈ C,
              let a : openPreimage U C := ⟨z,hp⟩
              IsCanonical F (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) F) V ∧
              a ∈ (geoTransformAlong F V).cosupp ∧
              ((∀ G ∈ F.E, a ∉ strictAlong V G) →
                (∃ (m e : ℕ) (L : MarkedIdeal n E),
                  IsInvDomain m L ∧ L.d = 1 ∧ 1 ≤ e ∧ RestrictEquiv Pc (powerMarked L e)) →
                ∃ (X' Y' : CMfd.{0} n) (D' P' : MarkedIdeal n X') (S' : BlowupTower X' Y') (c : Y'),
                  D'.N = P'.N ∧ D'.E = P'.E ∧
                  IsCanonical D' ((invFamily hn k).inv D') S' ∧
                  IsCanonical P' ((invFamily hn k).inv P') S' ∧
                  c ∈ (geoTransformAlong D' S').cosupp ∧ c ∈ (geoTransformAlong P' S').cosupp ∧
                  Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y =
                    toLex (b+1, (positiveSuccessorRead M.d
                      (toLex (0, ((invFamily hn k).inv D' S' c : WithTop (ValTy k)))) :
                        WithTop (ValTy (k+1))))))) := by
  classical
  intro r H p A B Q
  have hCar : R.N ⊆ J.N := fun _ hx => (hTrace ▸ hx).1
  obtain ⟨d,hd,hSpecial,_⟩ := chronological_support_dimension_domain_split hn J R hJ hR
    hClass hCar hMax T hCan y hy hLevel hNS
  obtain ⟨d',hd',_,hNo⟩ := chronological_support_domain_iff_dim_drop hn J R hJ hR
    hClass hCar hMax T hCan y hy hLevel hNS
  have heq : d' = d := RegularPointDimension.eq_of_regularAtDim hd' hd
  refine ⟨d,hd,?_⟩
  by_cases hFull : LocDimGE (n := n) (Q.N ∩ A.cosupp) p d
  · have hSp := hSpecial.mpr hFull
    have hNo' := hNo (heq.symm ▸ hFull)
    obtain ⟨hT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn (k+1))
      J hJ hMax hn T hCan
    have hyBar : y ∈ (geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hy
    have hReg := StepOneValueMasked.stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hyBar hNS
    rw [hLevel] at hReg
    have hlR : level R H p = b+1 := (level_eq_of_E_eq hClass.wEquiv.1 H p).symm.trans hReg.1.1
    have hTop := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn k) R
      (lowerMarkedM R) H hSp
    rw [hlR] at hTop
    exact Or.inl ⟨hFull,hTop,hNo'⟩
  · obtain ⟨D,Z,M,P,w,U,z,hM,hP,hTan,hTrace',hWP,hExp,hCanM,hz,hRead⟩ :=
        regular_chronological_head_true_mark hn J R hJ hR hClass hMax T hCan y hy hLevel hNS
          u hu hTrace (fun h => hFull (hSpecial.mp h))
    obtain ⟨_,_,hp,hCanF,ha,hZero⟩ :=
      selected_suffix_finite_zero_of_strict_avoidance_and_power hn M P hM hP w hTan
        hTrace' hWP hExp U hCanM z hz
    refine Or.inr ⟨hFull,D,Z,M,P,U,z,hM,hP,hCanM,hz,hRead,hp,hCanF,ha,?_⟩
    intro hOff hPow
    obtain ⟨hq,_,_,_,hN,hE,_,_,_,_,hCD,_,hcD,hcP,hCP,hValue⟩ := hZero hOff hPow
    exact ⟨_,_,_,_,_,_,hN,hE,hCD,hCP,hcD,hcP,
      hRead.trans (congrArg (fun q : ValTy (k+1) =>
        toLex (b+1, (q : WithTop (ValTy (k+1))))) hValue)⟩

#print axioms regular_chronological_head_true_mark
#print axioms selected_suffix_finite_zero_of_strict_avoidance_and_power
#print axioms exhaustive_actual_positive_head

end Hironaka.HironakaG1ExhaustivePositiveHead
