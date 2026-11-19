import Hironaka.Resolution.HironakaG1ActualCompanionWindowRead
import Hironaka.Resolution.HironakaG1LaterContactFieldExistence
import Hironaka.Resolution.HironakaG1LaterSelectedNormalTangent

/-! The next positive suffix on the literal historical companion head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Manifold ContDiff Topology

namespace Hironaka.HironakaG1ChronologicalCompanionSuffix

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres ResolutionInvariantExt
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong BoundaryCount
  InvDomainRebase InvDomainMemberRestriction InvDomainTowerAlong MemberInterTowerAlong
  HironakaG1RecursiveMemberValueTransport HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1LaterContactFieldExistence HironakaG1LaterSelectedNormalTangent
  HironakaCoherentTransformExtension TangentDirectionAlong ContactEquivalenceAlong
  RelativePrincipalizationSpan GiraudAlong
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1300000 in
/-- The next positive run is cut at its actual head. The suffix is tested
and canonical for the selected record on the literal mask. The boundary
filter uses the original prefix at that head and keeps the new suffix in
chronological list order. -/
theorem positive_companion_chronological_suffix {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA J H p
    let B := geoTransformAlong (barMarked J) H
    let K := positiveMemberOn J H p O
    IsGeoTestTower (barMarked J) H ∧ p ∈ B.cosupp ∧
      IsInvDomain (k+1) B ∧
      B.E = J.E.map (strictAlong H) ++ B.E.drop J.E.length ∧
      origMembers J H = J.E.map (strictAlong H) ∧
      K.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
        ((Subtype.val : O → _) ⁻¹' ·) ∧
      ∃ hp : p ∈ O,
        let z : openPreimage S O := ⟨y, hp⟩
        let V := restrict O S
        IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) V ∧
        IsGeoTestTower K V ∧ z ∈ (geoTransformAlong K V).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
          toLex (b+1, ((invFamily hn k).inv K V z : WithTop (ValTy k))) := by
  intro r H S p O B K
  let I := invFamily hn k
  obtain ⟨hT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical I J hJ hMax hn T hCan
  have hCanonBar := (Seq.StepOneBridge.isCanonical_iff I J hJ hMax hn T).mp hCan
  have hyBar : y ∈ (geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hy
  have hHead : IsGeoTestTower (barMarked J) H :=
    ((isGeoTestTower_iff_head_tail (barMarked J) T r).mp hT).1
  have hpBar : p ∈ B.cosupp :=
    StepOneCanonicalTail.mem_cosupp_head J hJ.isWellFormed T hT hyBar r
  have hB : IsInvDomain (k+1) B :=
    isInvDomain_geoTransformAlong (isInvDomain_barMarked J hJ) H hHead
  have hOrig : origMembers J H = J.E.map (strictAlong H) :=
    take_E_geoTransformAlong (barMarked J) H
  have hChron : B.E = J.E.map (strictAlong H) ++ B.E.drop J.E.length := by
    rw [← hOrig]
    exact (List.take_append_drop J.E.length B.E).symm
  have hRetained : K.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
      ((Subtype.val : O → _) ⁻¹' ·) := by
    change (memberRestrict B (membersThrough B.E (origMembers J H) p)).E.map _ = _
    rw [memberRestrict_membersThrough_E]
  have hLower := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k+1) J I
    hJ.isWellFormed hJ.one_le_d hn hMax hJ.dimLE T hT hCanonBar y hyBar hNS
  rw [hLevel] at hLower
  obtain ⟨hp, hK, hCanK, hz⟩ := hLower
  have hRead : Seq.StepOneValueMasked.stepOneInvM I J T y =
      toLex (b+1, ((I.inv K (restrict O S) ⟨y, hp⟩ : ValTy k) : WithTop (ValTy k))) := by
    change Seq.StepOneValueMasked.stepOneInvL I J (lowerMarkedM J) T y = _
    unfold Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hNS, hLevel]
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos hp]
    rfl
  have hK' : IsInvDomain k K := hK
  exact ⟨hHead, hpBar, hB, hChron, hOrig, hRetained, hp, hK', hCanK,
    I.isInvValue.isGeoTestTower_of_isCanonical hK' (restrict O S) hCanK, hz, hRead⟩

open NormalCrossings HironakaG1SeparateCarrierMemberCut HironakaG8MemberLoci
  CoefficientIdealRestriction HironakaG3RRawRegimeLocality HironakaG8ContactMax
  HironakaG1ClassReferenceContact

set_option maxHeartbeats 2000000 in
/-- A source bar tangent for the inherited supported carrier yields a
genuine tangent on the selected member record of the actual next positive
head. The support is the strict carrier there, intersected with the same
original members, and the whole retained boundary and local class agree. -/
theorem positive_companion_chronological_tangent {n k l b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+1) J)
    (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
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
    let O := maskA J H p
    let B := geoTransformAlong (barMarked J) H
    ∃ (V : Opens (split T r).1) (v : (split T r).1 → ℂ),
      p ∈ V ∧ V ≤ O ∧
      let K := positiveMemberOn J H p V
      let K' := positiveMemberOn R H p V
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : V | v z.val = 0})
      IsTangentDirectionAlong B.N B.ideal B.d V v ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (v ∘ (Subtype.val : V → _)) ∧
      C.N = K.N ∩ (Subtype.val : V → _) ⁻¹' strictAlong H R.N ∧
      C.N = K'.N ∧ C.E = K'.E ∧
      C.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
        ((Subtype.val : V → _) ⁻¹' ·) ∧
      LocWPEquiv K K' ∧ LocWPEquiv C K' ∧
      ∃ hpV : p ∈ V,
        let z : openPreimage S V := ⟨y, hpV⟩
        let G := restrict V S
        IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) G ∧
        IsGeoTestTower K G ∧ z ∈ (geoTransformAlong K G).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
          toLex (b+1, ((invFamily hn k).inv K G z : WithTop (ValTy k))) := by
  intro r H S p O B
  let Z := (split T r).1
  let D := geoTransformAlong (barMarked R) H
  let I := membersThrough B.E (origMembers J H) p
  let K₀ := memberRestrict B I
  obtain ⟨hHead, hpB, hB, _, _, _, hpO, hKO, hCanO, _, hzO, hRead⟩ :=
    positive_companion_chronological_suffix hn J hJ hMax T hCan y hy hLevel hNS
  have hJHead := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hHead
  have hRHead := (hClass.wEquiv.2 H).1.mp hJHead
  have hDHead := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRHead
  have hD : IsInvDomain l D :=
    isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hDHead
  have hCos : B.cosupp = D.cosupp :=
    (((bar_local_any_boundary J hJ).wEquiv.2 H).2 hJHead).symm.trans
      (((hClass.wEquiv.2 H).2 hJHead).trans
        (((bar_local_any_boundary R hR).wEquiv.2 H).2 hRHead))
  have hpD : p ∈ D.N := D.cosupp_subset_N (hCos ▸ hpB)
  have hpBN : p ∈ B.N := B.cosupp_subset_N hpB
  have hDN : D.N = strictAlong H R.N := HomogenizedGlueingTower.N_geoTransformAlong _ _
  have hDB : D.N ⊆ B.N := by
    rw [hDN, HomogenizedGlueingTower.N_geoTransformAlong]
    exact strictAlong_mono H (fun _ hx => (hTrace ▸ hx).1)
  have hBarE : (barMarked R).E = (barMarked J).E := hClass.wEquiv.1.symm
  have hE : D.E = B.E := geoTransformAlong_E_eq_of_E_eq hBarE H
  have hTD : IsTransverse n D.N B.E := hE ▸ hD.isWellFormed.isTransverse
  have hJbar := isInvDomain_barMarked J hJ
  obtain ⟨U, hpU, _, v, hv, hZero⟩ :=
    ContactEquivalenceStage.exists_isTangentDirectionAlong_stage (barMarked J)
      hJbar.isWellFormed.isClosedSubmanifold_N hJbar.isWellFormed.isCoherent hJbar.one_le_d
      (⊤ : Opens X) hu H hHead hpBN (mem_univ _)
  rw [hTrace, ← hDN] at hZero
  have hpv : v p = 0 := ((Set.ext_iff.mp hZero p).mpr ⟨hpD, hpU⟩).1.2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hv.multiplicity_one p hpU hpv
  have hvD : (vanishingIdeal (n := n) D.N).mem p v := by
    refine ⟨holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hf)
      (B.d-1) p v (hv.mem p hpU), ?_⟩
    filter_upwards [U.isOpen.mem_nhds hpU] with x hx hxD
    exact ((Set.ext_iff.mp hZero x).mpr ⟨hxD, hx⟩).1.2
  have hFields := exists_normalized_tangent_field_of_transverse_boundary hn B.E I
    hB.isWellFormed.isSNCDivisor hB.isWellFormed.isTransverse hTD
    (fun i hi => (mem_membersThrough.mp hi).2) hpD hDB hvD hξ hDetect
  have hUNear : ∀ᶠ z in 𝓝 p, z ∈ U := U.isOpen.mem_nhds hpU
  have hONear : ∀ᶠ z in 𝓝 p, z ∈ O := O.isOpen.mem_nhds hpO
  obtain ⟨M, hM, hOpen, hpM⟩ := mem_nhds_iff.mp (hFields.and (hUNear.and hONear))
  let V : Opens Z := ⟨M, hOpen⟩
  have hVU : V ≤ U := fun _ hx => (hM hx).2.1
  have hVO : V ≤ O := fun _ hx => (hM hx).2.2
  have hvV : IsTangentDirectionAlong B.N B.ideal B.d V v :=
    ⟨V.isOpen, fun x hx => hv.mem x (hVU hx), fun x hx => hv.multiplicity_one x (hVU hx)⟩
  have hSel := selected_tangent_of_current_contact B hB.isWellFormed hB.one_le_d I V v hvV
    (fun x hx => (hM hx).1)
  have hK₀ : K₀.IsWellFormed := isWellFormed_memberRestrict hn hB.isWellFormed I
  let A := CMfd.of (n := n) V
  let K : MarkedIdeal n A := positiveMemberOn J H p V
  let K' : MarkedIdeal n A := positiveMemberOn R H p V
  have hClass' : LocWPEquiv K K' :=
    member_stage_local_of_local hn J R hJ hR hClass H hJHead V p
  have hTan : IsTangentDirectionAlong K.N K.ideal K.d univ (v ∘ (Subtype.val : V → Z)) :=
    isTangentDirectionAlong_pullback_val V
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hg) hSel
  have hNZ : K.N ∩ {z : V | v z.val = 0} = K.N ∩ (Subtype.val : V → Z) ⁻¹' D.N := by
    ext z
    have hzU := hVU z.property
    constructor
    · rintro ⟨hz, hvz⟩
      exact ⟨hz, ((Set.ext_iff.mp hZero z.val).mp ⟨⟨hz.1, hvz⟩, hzU⟩).1⟩
    · rintro ⟨hz, hzD⟩
      exact ⟨hz, ((Set.ext_iff.mp hZero z.val).mpr ⟨hzD, hzU⟩).1.2⟩
  have hOrig : origMembers R H = origMembers J H := origMembers_eq_of_E_eq hClass.wEquiv.1.symm H
  have hNK : K.N ∩ (Subtype.val : V → Z) ⁻¹' D.N = K'.N := by
    have hI₁ : ∀ F ∈ origMembers J H, F ∈ B.E := fun _ h => List.mem_of_mem_take h
    have hI₂ : ∀ F ∈ origMembers R H, F ∈ D.E := fun _ h => List.mem_of_mem_take h
    change ((Subtype.val : V → Z) ⁻¹' (B.N ∩ memberInter B.E I)) ∩
      (Subtype.val : V → Z) ⁻¹' D.N =
        (Subtype.val : V → Z) ⁻¹' (D.N ∩ memberInter D.E (membersThrough D.E (origMembers R H) p))
    unfold I
    rw [memberInter_membersThrough hI₁ p, memberInter_membersThrough hI₂ p, hOrig]
    ext z
    exact ⟨fun hz => ⟨hz.2, hz.1.2⟩, fun hz => ⟨⟨hDB hz.1, hz.2⟩, hz.1⟩⟩
  have hSlots : K.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
      ((Subtype.val : V → Z) ⁻¹' ·) := by
    change (memberRestrict B I).E.map _ = _
    rw [memberRestrict_membersThrough_E]
  let G := restrict V S
  let C := withN (coeffMarkedAlong K) (K.N ∩ {z : V | v z.val = 0})
  let z : openPreimage S V := ⟨y, hpM⟩
  have hHol : ∀ x f, K₀.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf
  obtain ⟨hK, hCanK, hVal⟩ := Seq.MaxLocusLocal.restrict_nestedOpens (invFamily hn k)
    (𝔫 := K₀) hK₀.isCoherent hVO hKO S hCanO
  have hz : z ∈ (geoTransformAlong K G).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Z) K₀) G).cosupp
    rw [cosupp_restrict_raw K₀ hHol V S]
    change y ∈ (geoTransformAlong K₀ S).cosupp
    rw [cosupp_restrict_raw K₀ hHol O S] at hzO
    exact hzO
  have hReadV : Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
      toLex (b+1, ((invFamily hn k).inv K G z : WithTop (ValTy k))) := by
    rw [hRead, hVal z hz]
  have hCN : IsClosedSubmanifold (X := A) n C.N := by
    change IsClosedSubmanifold (X := A) n (K.N ∩ {z : V | v z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using isClosedSubmanifold_contact_along
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hTan
  have hContact : MaxContact K C.N := by
    change MaxContact K (K.N ∩ {z : V | v z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using
      maxContact_base K hK.isWellFormed.isCoherent hTan
  have hKC : LocWPEquiv (X := A) K C :=
    locWPEquiv_of_reference_maxContact K K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      rfl (LocEquiv.refl _ K) C.N hCN (fun _ hz => hz.1) hContact
  exact ⟨V, v, hpM, hVO, hvV, hTan, hNZ.trans (congrArg (fun F : Set Z =>
      K.N ∩ (Subtype.val : V → Z) ⁻¹' F) hDN),
    hNZ.trans hNK, hClass'.wEquiv.1, hSlots, hClass', hKC.symm.trans hClass',
    hpM, hK, hCanK, (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hK G hCanK,
    hz, hReadV⟩

open DerivativeIdealAlong HomogenizedGlueingLiftAlong ContactStageKept

private theorem tangent_bar_of_normalized_fields {n k : ℕ} {X : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J) (V : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d V u)
    (hFields : ∀ x ∈ V, ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField J.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) :
    IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d V u := by
  let A := homMarkedAlong J
  have hA : A.IsWellFormed := ⟨hJ.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N,
    hJ.isWellFormed.isSNCDivisor, hJ.isWellFormed.isTransverse⟩
  have hAu : IsTangentDirectionAlong A.N A.ideal A.d V u := by
    refine ⟨V.isOpen, fun x hx => ?_, hu.multiplicity_one⟩
    exact iterDerivIdealAlong_mono (N := J.N)
      (le_homogenizedIdealAlong (fun _ _ hf =>
        GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf) hJ.one_le_d)
      (J.d - 1) x u (hu.mem x hx)
  have hEmpty : (memberRestrict A ∅).N = J.N := by
    rw [memberRestrict_N]
    change J.N ∩ memberInter A.E ∅ = J.N
    simp [memberInter]
  have hB := selected_tangent_of_current_contact A hA hJ.one_le_d ∅ V u hAu
    (fun x hx => by rw [hEmpty]; exact hFields x hx)
  change IsTangentDirectionAlong (memberRestrict A ∅).N (barMarked J).ideal (barMarked J).d V u at hB
  rw [hEmpty] at hB
  exact hB

/-- The ordinary inherited companion tangent suffices locally on the
actual bar record, by transversality of its supported zero trace. -/
theorem exists_companion_source_bar_tangent_window {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain k J)
    (hR : IsInvDomain l R) (hE : J.E = R.E) (a : X) (ha : a ∈ R.N)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (hTrace : J.N ∩ {z | u z = 0} = R.N) :
    ∃ W : Opens X, a ∈ W ∧
      let A := CMfd.of (n := n) W
      let Jw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) J
      let Rw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) R
      IsTangentDirectionAlong (barMarked Jw).N (barMarked Jw).ideal (barMarked Jw).d
        (⊤ : Opens A) (u ∘ (Subtype.val : W → X)) ∧
      (barMarked Jw).N ∩ {z : W | (u ∘ (Subtype.val : W → X)) z = 0} = Rw.N := by
  have hRJ : R.N ⊆ J.N := fun _ hx => (hTrace ▸ hx).1
  have hau : u a = 0 := (hTrace ▸ ha).2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hu.multiplicity_one a (mem_univ a) hau
  have huR : (vanishingIdeal (n := n) R.N).mem a u :=
    ⟨holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf)
      (J.d-1) a u (hu.mem a (mem_univ _)),
      Eventually.of_forall (fun x hx => (show x ∈ J.N ∩ {z | u z = 0} from hTrace ▸ hx).2)⟩
  have hTR : IsTransverse n R.N J.E := hE.symm ▸ hR.isWellFormed.isTransverse
  have hFields := exists_normalized_tangent_field_of_transverse_boundary hn J.E ∅
    hJ.isWellFormed.isSNCDivisor hJ.isWellFormed.isTransverse hTR
    (by simp) ha hRJ huR hξ hDetect
  have hEmpty : J.N ∩ memberInter J.E ∅ = J.N := by simp [memberInter]
  rw [hEmpty] at hFields
  obtain ⟨M, hM, hOpen, haM⟩ := mem_nhds_iff.mp hFields
  let W : Opens X := ⟨M, hOpen⟩
  have huW : IsTangentDirectionAlong J.N J.ideal J.d W u :=
    ⟨W.isOpen, fun x _ => hu.mem x (mem_univ _), fun x _ => hu.multiplicity_one x (mem_univ _)⟩
  have hBar := tangent_bar_of_normalized_fields J hJ W u huW hM
  have hJbar := isInvDomain_barMarked J hJ
  have hPull := isTangentDirectionAlong_pullback_val W
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJbar.isWellFormed.isCoherent hg) hBar
  let A := CMfd.of (n := n) W
  let j : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) J
  have hBarEq : barMarked (X := A) j =
      MarkedIdeal.pullback (M' := A) (Subtype.val : W → X) (barMarked J) :=
    barMarked_pullback_val (𝔍 := J) W hJ.isWellFormed.isCoherent
      hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  refine ⟨W, haM, ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun q : MarkedIdeal n A =>
      IsTangentDirectionAlong q.N q.ideal q.d (⊤ : Opens A) (u ∘ (Subtype.val : W → X))) hBarEq)
      hPull
  · change (Subtype.val : W → X) ⁻¹' J.N ∩ {z : W | u z.val = 0} =
      (Subtype.val : W → X) ⁻¹' R.N
    rw [← hTrace]
    rfl

#print axioms positive_companion_chronological_suffix
#print axioms positive_companion_chronological_tangent
#print axioms exists_companion_source_bar_tangent_window

end Hironaka.HironakaG1ChronologicalCompanionSuffix
