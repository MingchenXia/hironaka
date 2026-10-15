/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.NonmonomialOrderTailExact
import Hironaka.Resolution.HironakaOriginalUntestedMemberCurveSpecial
/-! Actual original member GENERAL values from independently proved curve
geometry; no TEST of the lower reference or its run companion is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedMemberCurveFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  RelativePrincipalizationSpan GermIdealOrder NormalCrossings MonomialPartAlong
  StepOneValue StepOneLowerDomain StepOneValueMasked CanonicalCentres HomogenizedIdealAlong
  HomogenizedIdealAlongTower NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  StepOneRegime GeneralValue GeneralCompare GeneralCanonicalTail CompanionRebase CompanionReductionAlong
  InvDomainCompanion MarkedIdealRestrictOpen MarkedIdealBiholomorphism HironakaCoherentTransformExtension
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaOriginalUntestedMemberCurveSpecial HironakaOriginalCurvePositiveEmptyWindow
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Explicit genuine reference-geometry transport; the final original-only
consumer independently supplies the entire reference-domain family. -/
theorem modeled_curve_candidate_domains (m K B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R)) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong B R)
  | _,.refl,_ => hB
  | _,.step R C π hπ,hR => by
    have hPrev := modeled_curve_candidate_domains m K B hB hN hE hModel R hR.1
    have hNext := hModel (.step R C π hπ) hR
    have hN' := geoTransformAlong_N_eq_of_N_eq hN (.step R C π hπ)
    have hE' := geoTransformAlong_E_eq_of_E_eq hE (.step R C π hπ)
    have hSM : IsClosedSubmanifold n ((geoTransformAlong B R).geoTransform C π).N := by
      change IsClosedSubmanifold n (geoTransformAlong B (.step R C π hπ)).N
      rw [hN'];exact hNext.isWellFormed.isClosedSubmanifold_N
    refine ⟨⟨hSM,isCoherent_geoTransform_ideal_of_smooth_strict _ hPrev.isWellFormed.isCoherent hπ hSM,?_,?_⟩,?_,?_,?_⟩
    · rw [hE'];exact hNext.isWellFormed.isSNCDivisor
    · rw [hN',hE'];exact hNext.isWellFormed.isTransverse
    · rw [hN'];exact hNext.dimLE
    · rw [d_geoTransformAlong];exact hB.one_le_d
    · exact isNonzeroAlongAt_geoTransform_of_smooth_strict _ hPrev.isWellFormed.isClosedSubmanifold_N
        hPrev.isWellFormed.isCoherent hπ hSM hPrev.isNonzeroAlongAt

private theorem modeled_restrict_identity (m K B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R))
    (U : Opens X) : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) B) (restrict U R)=
        MarkedIdeal.pullback (Subtype.val : openPreimage R U → V) (geoTransformAlong B R)
  | _,.refl,_ => rfl
  | _,.step R C π hπ,hR => by
    have hPrev := modeled_curve_candidate_domains m K B hB hN hE hModel R hR.1
    have hNext := modeled_curve_candidate_domains m K B hB hN hE hModel (.step R C π hπ) hR
    have ih := modeled_restrict_identity m K B hB hN hE hModel U R hR.1
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) B) (restrict U R)).geoTransform
      ((Subtype.val : openPreimage R U → _) ⁻¹' C) _=_
    rw [ih]
    exact geoTransform_pullback_val hPrev.isWellFormed.isCoherent hπ hNext.isWellFormed.isCoherent (openPreimage R U) _

private theorem modeled_cosupport_off_boundary_iff (m K B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R)) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → ∀ y : V,
      y ∉ ⋃ F ∈ (geoTransformAlong B R).E,F →
      (y ∈ (geoTransformAlong B R).cosupp ↔ R.proj y ∈ B.cosupp)
  | _,.refl,_,_,_ => Iff.rfl
  | _,.step R C π hπ,hR,y,hy => by
    have hOff := HironakaStageCenters.notMem_boundary_geoTransform (geoTransformAlong B R) hy
    have hd := modeled_curve_candidate_domains m K B hB hN hE hModel R hR.1
    exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong B R)
      hd.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg) hπ hOff.1).trans
      (modeled_cosupport_off_boundary_iff m K B hB hN hE hModel R hR.1 (π y) hOff.2)

/-- The ACTUAL run, head, order mask and companion coefficient cosupport are
constructed before evaluating ORIGINAL StepOne. No lower TEST is supplied. -/
theorem modeled_curve_actual_run_companion_step_one_value (hn : 0<n) (k : ℕ)
    (m K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R))
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (y : Y)
    (hy : y ∈ (geoTransformAlong K T).cosupp) (hpos : 0<nmOrd (geoTransformAlong K T) y) :
    let q := nmOrd (geoTransformAlong K T) y
    let r := regimeRun (OrdRegime K q) T y
    let W := ordMask (geoTransformAlong K (head T r)) q
    ∃ hp : (tail T r).proj y ∈ W,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (compAt K q (head T r))
        (restrict W (tail T r)) (⟨y,hp⟩ : openPreimage (tail T r) W)=toLex (0,⊤) := by
  let q := nmOrd (geoTransformAlong K T) y
  let r := regimeRun (OrdRegime K q) T y
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong K H
  let W := ordMask A q
  let C := companionOf n A q
  let B := barMarked C
  let J := compAt K q H
  let mH := geoTransformAlong m H
  have hq : 1≤q := hpos
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail m T r).mp hT
  have hA : IsInvDomain 1 A := hModel H hH
  have hReg := regime_start (OrdRegime K q) T (y := y) ⟨hy,rfl⟩
  change S.proj y ∈ A.cosupp ∧ nmOrd A (S.proj y)=q at hReg
  have hMask : S.proj y ∈ W := by
    apply (mem_ordMask_iff hn hA.isWellFormed hA.isNonzeroAlongAt q _).mpr
    intro hh
    have he := (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hReg.1.1 (q+1)).mp hh
    rw [hReg.2] at he
    omega
  let p : openPreimage S W := ⟨y,hMask⟩
  have hC : IsInvDomain 1 C := isInvDomain_companionAlong hn hA hq
  have hB : IsInvDomain 1 B := isInvDomain_barMarked C hC
  have hCN : C.N=A.N := by simp only [C,companionOf,companionAlong_N]
  have hCE : C.E=A.E := by simp only [C,companionOf,companionAlong_E]
  have hBN : B.N=A.N := by simpa only [B,barMarked_N] using hCN
  have hBE : B.E=A.E := by simpa only [B,barMarked_E] using hCE
  have hTailModel : ∀ {V : CMfd.{u} n} (R : BlowupTower (split T r).1 V),
      IsGeoTestTower mH R → IsInvDomain 1 (geoTransformAlong A R) := by
    intro V R hR
    have hd := hModel (H.append R) ((isGeoTestTower_append_iff m H R).mpr ⟨hH,hR⟩)
    rwa [geoTransformAlong_append] at hd
  have hBS := modeled_curve_candidate_domains mH A B hB hBN hBE hTailModel S hS
  have hJ : IsInvDomain 1 J := isInvDomain_compAt hn hq H hA
  have hInitJ : (⟨S.proj y,hMask⟩ : W) ∈ J.cosupp := by
    have hi := (mem_cosupp_compAt_iff hn hA hq .refl .refl trivial trivial trivial
      (⟨S.proj y,hMask⟩ : openPreimage (.refl : BlowupTower _ _) W)).mpr hReg
    exact hi
  have hJC : J=MarkedIdeal.pullback (Subtype.val : W → _) C := compAt_eq_pullback hn q H hA
  have hInitC : S.proj y ∈ C.cosupp := by
    rw [hJC,cosupp_pullback_val C (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hC.isWellFormed.isCoherent hg)] at hInitJ
    exact hInitJ
  have hInitB : S.proj y ∈ B.cosupp := by
    have he := coeff_homAlong_wEquiv C hC.isWellFormed.isClosedSubmanifold_N hC.isWellFormed.isCoherent hC.one_le_d
    change S.proj y ∈ (geoTransformAlong (barMarked C) (.refl : BlowupTower _ _)).cosupp
    rw [(he.2 .refl).2 trivial]
    exact hInitC
  have hyNoE : y ∉ ⋃ F ∈ (geoTransformAlong K T).E,F := by
    intro hh
    have hz := (curve_domain_nonmonomial_unit_on_boundary hn (geoTransformAlong K T) (hModel T hT) y hy.1 hh).2
    omega
  have hBSE : (geoTransformAlong B S).E=(geoTransformAlong K T).E :=
    (geoTransformAlong_E_eq_of_E_eq hBE S).trans (congrArg MarkedIdeal.E (geoTransformAlong_head_tail K T r).symm)
  have hyBNoE : y ∉ ⋃ F ∈ (geoTransformAlong B S).E,F := by rw [hBSE];exact hyNoE
  have hyB : y ∈ (geoTransformAlong B S).cosupp :=
    (modeled_cosupport_off_boundary_iff mH A B hB hBN hBE hTailModel S hS y hyBNoE).mpr hInitB
  have hBarJ : barMarked J=MarkedIdeal.pullback (Subtype.val : W → _) B := by
    rw [hJC]
    exact ContactStageKept.barMarked_pullback_val W hC.isWellFormed.isCoherent hC.isWellFormed.isClosedSubmanifold_N hC.one_le_d
  have hWhole : geoTransformAlong (barMarked J) (restrict W S)=
      MarkedIdeal.pullback (Subtype.val : openPreimage S W → _) (geoTransformAlong B S) := by
    rw [hBarJ]
    exact modeled_restrict_identity mH A B hB hBN hBE hTailModel W S hS
  have hBarCurrent : IsInvDomain 1 (geoTransformAlong (barMarked J) (restrict W S)) := by
    rw [hWhole]
    exact InvDomainTowerAlong.isInvDomain_pullback_val (openPreimage S W) hBS
  have hpBar : p ∈ (geoTransformAlong (barMarked J) (restrict W S)).cosupp := by
    rw [hWhole,cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hBS.isWellFormed.isCoherent hg)]
    exact hyB
  have hs := isSpecial_of_current_bar_curve_domain hn J (restrict W S) hBarCurrent p hpBar
  have hpNoE : p ∉ ⋃ F ∈ (geoTransformAlong (barMarked J) (restrict W S)).E,F := by
    rw [hWhole]
    intro hpF
    obtain ⟨F,hF,hpF⟩ := mem_iUnion₂.mp hpF
    change F ∈ (geoTransformAlong B S).E.map ((Subtype.val : openPreimage S W → _) ⁻¹' ·) at hF
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hF
    exact hyBNoE (mem_iUnion₂.mpr ⟨D,hD,hpF⟩)
  have hl : level J (restrict W S) p=0 := by
    unfold level BoundaryCount.boundaryCount
    apply Finset.card_eq_zero.mpr
    ext i
    constructor
    · intro hi
      have hPass := (Finset.mem_filter.mp hi).2
      have hMember : (origMembers J (restrict W S)).get i ∈ (geoTransformAlong (barMarked J) (restrict W S)).E :=
        List.mem_of_mem_take (List.get_mem _ i)
      exact (hpNoE (mem_iUnion₂.mpr ⟨_,hMember,hPass⟩)).elim
    · intro hi
      simp at hi
  refine ⟨hMask,?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hs,hl]

/-- The WHOLE unchanged original GENERAL value, on genuine curve reference
geometry, even when the actual original tower is not a TEST of that reference. -/
theorem modeled_curve_full_value_formula (hn : 0<n) (k : ℕ) (m K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R))
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (y : Y)
    (hy : y ∈ (geoTransformAlong K T).cosupp) :
    (invFamily hn (k+1)).inv K T y=
      if nmOrd (geoTransformAlong K T) y=0 then
        toLex (0,toLex (Sum.inl (MonomialCaseAlong.gammaAlong n (geoTransformAlong K T).N
          (geoTransformAlong K T).ideal (geoTransformAlong K T).E (geoTransformAlong K T).d y)))
      else toLex (nmOrd (geoTransformAlong K T) y,toLex (Sum.inr
        ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  by_cases hz : nmOrd (geoTransformAlong K T) y=0
  · rw [if_pos hz]
    exact genInv_of_nmOrd_eq_zero _ K T hz
  · rw [if_neg hz]
    have hp : 0<nmOrd (geoTransformAlong K T) y := Nat.pos_of_ne_zero hz
    obtain ⟨hMask,hValue⟩ := modeled_curve_actual_run_companion_step_one_value hn k m K hModel T hT y hy hp
    change genInv (fun {A} J {B} S p => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J S p) K T y=_
    rw [genInv_of_nmOrd_ne_zero _ K T rfl hz,genLowerValue_eq_of_mem _ K hMask,hValue]

/-- ONLY actual original bound-two geometry and original TEST supply the true
member reference-domain family before whole untested GENERAL values. -/
theorem original_member_curve_untested_full_value_formula (hn : 0<n) (k : ℕ) (m : MarkedIdeal n X)
    (hm : IsInvDomain 2 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (y : Y)
    (hy : y ∈ (geoTransformAlong (memberRemainderMarked m S) T).cosupp) :
    let K := memberRemainderMarked m S
    (invFamily hn (k+1)).inv K T y=
      if nmOrd (geoTransformAlong K T) y=0 then
        toLex (0,toLex (Sum.inl (MonomialCaseAlong.gammaAlong n (geoTransformAlong K T).N
          (geoTransformAlong K T).ideal (geoTransformAlong K T).E (geoTransformAlong K T).d y)))
      else toLex (nmOrd (geoTransformAlong K T) y,toLex (Sum.inr
        ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  exact modeled_curve_full_value_formula hn k m (memberRemainderMarked m S)
    (fun R hR => isInvDomain_geoTransformAlong_memberRemainder hn m hm.isWellFormed hm.one_le_d hm.dimLE S hS R hR)
    T hT y hy

end
end Hironaka.HironakaOriginalUntestedMemberCurveFullValues
