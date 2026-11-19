/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSameCarrierCandidateDomains
/-! Genuine independent masked companion histories and actual SPECIAL leaves,
without inferring a candidate TEST from a reference TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalRunCompanionSpecialSmooth
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen StepOneValue StepOneValueMasked
  GeneralValue GeneralCanonicalTail GeneralCompare HironakaGeneralThreeNonspecialAnalyticLoci
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  StepOneRegime CompanionRebase CompanionReductionAlong InvDomainCompanion InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower HironakaCoherentTransformExtension
  HironakaOriginalSameCarrierCandidateDomains HironakaOriginalUntestedCurveSmoothValues
  HironakaOriginalUntestedMemberCurveSpecial HironakaOriginalUntestedSpecialSmoothPullback
  HironakaOriginalUntestedCompanionSmoothPullback HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaSmoothSubmersionHistoricalControlledTail HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativePartsCompanion
  BoundaryCount CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n m b : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

private theorem actual_base_submersion (h : IsActualTowerPullback f Q T g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f := by
  induction h with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

theorem exists_modeled_masked_cartesian (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {Z : CMfd.{u} n} (R : BlowupTower X Z),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (j q : ℕ) :
    let U := ordMask (geoTransformAlong K (head T j)) q
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q j)) q
    ∃ (a : (split Q j).1 → (split T j).1) (p : V → U)
      (η : openPreimage (tail Q j) V → openPreimage (tail T j) U),
      IsActualTowerPullback f (head Q j) (head T j) a ∧
      IsActualTowerPullback a (tail Q j) (tail T j) g ∧
      (∀ v,(p v : (split T j).1)=a (v : (split Q j).1)) ∧
      (∀ z,(η z : D)=g (z : D')) ∧
      IsActualTowerPullback p (restrict V (tail Q j)) (restrict U (tail T j)) η ∧
      markedPullback (m := m) p (compAt K q (head T j))=
        compAt (markedPullback (m := m) f K) q (head Q j) := by
  let U := ordMask (geoTransformAlong K (head T j)) q
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q j)) q
  obtain ⟨a,hH,hS⟩ := IsActualTowerPullback.simultaneous_split h j
  have hTH := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hMask : (V : Set (split Q j).1)=a ⁻¹' (U : Set (split T j).1) :=
    IsActualTowerPullback.modeled_order_mask_dictionary hn hH M K hModel hTH q
  obtain ⟨p,η,hp,hη,hCart⟩ := IsActualTowerPullback.exists_actual_open_restriction hS U V hMask
  obtain ⟨p',_hpSmooth,hp',hInit⟩ :=
    IsActualTowerPullback.exists_modeled_masked_companion hn hH M K hModel hTH q
  have hpp : p'=p := by funext v;exact Subtype.ext ((hp' v).trans (hp v).symm)
  subst p'
  exact ⟨a,p,η,hH,hS,hp,hη,hCart,hInit⟩

theorem modeled_masked_companion_special_level (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {Z : CMfd.{u} n} (R : BlowupTower X Z),IsGeoTestTower M R →
      IsInvDomain b (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (j q : ℕ) (hq : 1≤q) (z : D') :
    let U := ordMask (geoTransformAlong K (head T j)) q
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q j)) q
    ∀ hp : (tail T j).proj (g z) ∈ U,∃ hp' : (tail Q j).proj z ∈ V,
      (IsSpecial (compAt (markedPullback (m := m) f K) q (head Q j)) (restrict V (tail Q j)) ⟨z,hp'⟩ ↔
        IsSpecial (compAt K q (head T j)) (restrict U (tail T j)) ⟨g z,hp⟩) ∧
      level (compAt (markedPullback (m := m) f K) q (head Q j)) (restrict V (tail Q j)) ⟨z,hp'⟩=
        level (compAt K q (head T j)) (restrict U (tail T j)) ⟨g z,hp⟩ := by
  dsimp only
  let H := head T j
  let S := tail T j
  let H' := head Q j
  let S' := tail Q j
  let A := geoTransformAlong K H
  let C := companionOf n A q
  let B := barMarked C
  let U := ordMask A q
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) H') q
  let J := compAt K q H
  let J' := compAt (markedPullback (m := m) f K) q H'
  let mH := geoTransformAlong M H
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T j).mp hT
  have hA : IsInvDomain b A := hModel H hH
  have hC : IsInvDomain b C := isInvDomain_companionAlong hn hA hq
  have hB : IsInvDomain b B := isInvDomain_barMarked C hC
  have hBN : B.N=A.N := by simp only [B,C,barMarked_N,companionOf,companionAlong_N]
  have hBE : B.E=A.E := by simp only [B,C,barMarked_E,companionOf,companionAlong_E]
  have hTailModel : ∀ {Z : CMfd.{u} n} (R : BlowupTower (split T j).1 Z),
      IsGeoTestTower mH R → IsInvDomain b (geoTransformAlong A R) := by
    intro Z R hR
    have hh := hModel (H.append R) ((isGeoTestTower_append_iff M H R).mpr ⟨hH,hR⟩)
    rwa [geoTransformAlong_append] at hh
  have hBarModel : ∀ {Z : CMfd.{u} n} (R : BlowupTower (split T j).1 Z),
      IsGeoTestTower mH R → (geoTransformAlong B R).IsWellFormed := fun R hR =>
    (same_carrier_candidate_domains mH A B hB hBN hBE hTailModel R hR).isWellFormed
  obtain ⟨a,p,η,hHead,hTail,hpcoord,_hηcoord,_hMasked,hComp⟩ :=
    exists_modeled_masked_cartesian hn h M K hModel hT j q
  have hV : (V : Set (split Q j).1)=a ⁻¹' (U : Set (split T j).1) :=
    IsActualTowerPullback.modeled_order_mask_dictionary hn hHead M K hModel hH q
  intro hp
  have hp' : S'.proj z ∈ V := by
    change S'.proj z ∈ (V : Set (split Q j).1)
    rw [hV]
    change a (S'.proj z) ∈ U
    rw [←hTail.proj_comm z]
    exact hp
  have hJC : J=markedPullback (m := n) (Subtype.val : U → (split T j).1) C :=
    compAt_eq_pullback hn q H hA
  have hInit : markedPullback (m := m) (a ∘ (Subtype.val : V → (split Q j).1)) C=J' := by
    change markedPullback (m := m) p J=J' at hComp
    rw [hJC] at hComp
    change markedPullback (m := m) p
      (markedPullback (m := n) (Subtype.val : U → (split T j).1) C)=J' at hComp
    rw [←whole_parameter_markedPullback_comp (X := (split T j).1) (Y := CMfd.of (n := n) U)
      (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → (split T j).1)) (g := p)
      contMDiff_subtype_val (actual_base_submersion _hMasked).contMDiff C hC.isWellFormed.isCoherent] at hComp
    have hBase : (Subtype.val : U → (split T j).1) ∘ p=a ∘ (Subtype.val : V → (split Q j).1) := by
      funext v;exact hpcoord v
    rwa [hBase] at hComp
  have hOpenSource := IsActualTowerPullback.restrict_source_open hTail V
  have hOpenTarget := open_inclusion_actual_tower U S
  have hSourceSpecial := IsActualTowerPullback.modeled_isSpecial_dictionary hOpenSource mH C hC.isWellFormed hBarModel hS (⟨z,hp'⟩ : openPreimage S' V)
  have hSourceLevel := IsActualTowerPullback.modeled_level_dictionary hOpenSource mH C hC.isWellFormed hBarModel hS (⟨z,hp'⟩ : openPreimage S' V)
  have hTargetSpecial := IsActualTowerPullback.modeled_isSpecial_dictionary hOpenTarget mH C hC.isWellFormed hBarModel hS (⟨g z,hp⟩ : openPreimage S U)
  have hTargetLevel := IsActualTowerPullback.modeled_level_dictionary hOpenTarget mH C hC.isWellFormed hBarModel hS (⟨g z,hp⟩ : openPreimage S U)
  rw [hInit] at hSourceSpecial hSourceLevel
  rw [←hJC] at hTargetSpecial hTargetLevel
  exact ⟨hp',hSourceSpecial.trans hTargetSpecial.symm,hSourceLevel.trans hTargetLevel.symm⟩


theorem original_run_companion_special_level (hn : 0<n)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (hT : IsGeoTestTower M T) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hpos : 0<nmOrd (geoTransformAlong M T) (g z)) :
    let q := nmOrd (geoTransformAlong M T) (g z)
    let r := regimeRun (OrdRegime M q) T (g z)
    let U := ordMask (geoTransformAlong M (head T r)) q
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) q
    ∃ (hp : (tail T r).proj (g z) ∈ U) (hp' : (tail Q r).proj z ∈ V),
      (IsSpecial (compAt (markedPullback (m := m) f M) q (head Q r)) (restrict V (tail Q r)) ⟨z,hp'⟩ ↔
        IsSpecial (compAt M q (head T r)) (restrict U (tail T r)) ⟨g z,hp⟩) ∧
      level (compAt (markedPullback (m := m) f M) q (head Q r)) (restrict V (tail Q r)) ⟨z,hp'⟩=
        level (compAt M q (head T r)) (restrict U (tail T r)) ⟨g z,hp⟩ := by
  let q := nmOrd (geoTransformAlong M T) (g z)
  let r := regimeRun (OrdRegime M q) T (g z)
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong M H
  have hH := ((isGeoTestTower_iff_head_tail M T r).mp hT).1
  have hA := isInvDomain_geoTransformAlong hM H hH
  have hReg := regime_start (OrdRegime M q) T (y := g z) ⟨hy,rfl⟩
  change S.proj (g z) ∈ A.cosupp ∧ nmOrd A (S.proj (g z))=q at hReg
  have hp : S.proj (g z) ∈ ordMask A q := by
    apply (mem_ordMask_iff hn hA.isWellFormed hA.isNonzeroAlongAt q _).mpr
    intro hh
    have hle := (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hReg.1.1 (q+1)).mp hh
    rw [hReg.2] at hle
    omega
  obtain ⟨hp',hs,hl⟩ := modeled_masked_companion_special_level hn h M M
    (fun R hR => isInvDomain_geoTransformAlong hM R hR) hT r q hpos z hp
  exact ⟨hp,hp',hs,hl⟩

theorem original_curve_smooth_run_special (hn : 0<n) (hm : 0<m)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (hT : IsGeoTestTower M T) (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hpos : 0<nmOrd (geoTransformAlong M T) (g z)) :
    let q := nmOrd (geoTransformAlong M T) (g z)
    let r := regimeRun (OrdRegime M q) T (g z)
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f M) (head Q r)) q
    let J' := compAt (markedPullback (m := m) f M) q (head Q r)
    ∃ hp' : (tail Q r).proj z ∈ V,
      IsSpecial J' (restrict V (tail Q r)) ⟨z,hp'⟩ ∧
      level J' (restrict V (tail Q r)) ⟨z,hp'⟩=0 ∧ ∀ k : ℕ,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hm k) J' (restrict V (tail Q r)) ⟨z,hp'⟩=toLex (0,⊤) := by
  let q := nmOrd (geoTransformAlong M T) (g z)
  let r := regimeRun (OrdRegime M q) T (g z)
  let S := tail T r
  let U := ordMask (geoTransformAlong M (head T r)) q
  let J := compAt M q (head T r)
  obtain ⟨hp,hp',hSpecial,hLevel⟩ := original_run_companion_special_level hn h M hM hT z hy hpos
  obtain ⟨_hMask,_hBModel,_hBS,_hyB,hyNoE,_hBarJ,hWholeJ,hCurrentJ,hpJ⟩ :=
    modeled_curve_run_companion_current_bar_data hn M M
      (fun R hR => isInvDomain_geoTransformAlong hM R hR) T hT (g z) hy hpos
  have hTargetSpecial : IsSpecial J (restrict U S) ⟨g z,hp⟩ :=
    isSpecial_of_current_bar_curve_domain hn J (restrict U S) hCurrentJ ⟨g z,hp⟩ hpJ
  have hNoE : (⟨g z,hp⟩ : openPreimage S U) ∉
      ⋃ F ∈ (geoTransformAlong (barMarked J) (restrict U S)).E,F := by
    rw [hWholeJ]
    intro hzF
    obtain ⟨F,hF,hzF⟩ := mem_iUnion₂.mp hzF
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hF
    exact hyNoE (mem_iUnion₂.mpr ⟨D,hD,hzF⟩)
  have hTargetLevel : level J (restrict U S) ⟨g z,hp⟩=0 := by
    unfold level BoundaryCount.boundaryCount
    apply Finset.card_eq_zero.mpr
    ext i
    constructor
    · intro hi
      have hPass := (Finset.mem_filter.mp hi).2
      have hMember : (origMembers J (restrict U S)).get i ∈
          (geoTransformAlong (barMarked J) (restrict U S)).E :=
        List.mem_of_mem_take (List.get_mem _ i)
      exact (hNoE (mem_iUnion₂.mpr ⟨_,hMember,hPass⟩)).elim
    · intro hi;simp at hi
  have hs := hSpecial.mpr hTargetSpecial
  have hl := hLevel.trans hTargetLevel
  refine ⟨hp',hs,hl,fun k => ?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hs,hl]

end
end Hironaka.HironakaOriginalRunCompanionSpecialSmooth
