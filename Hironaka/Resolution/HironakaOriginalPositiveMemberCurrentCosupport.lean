/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalControlledReferenceRestriction
import Hironaka.Resolution.HironakaOriginalUntestedControlledSmoothPullback

/-! Actual retained-positive member endpoint membership, with no lower TEST
or supplied current lower-cosupport certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveMemberCurrentCosupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaOriginalControlledReferenceRestriction
  InvDomainMemberRestriction InvDomainRebase BoundaryCount MemberInterAlong MemberInterTowerAlong
  CoefficientIdealRestriction NormalCrossings HomogenizedIdealAlong HomogenizedIdealAlongTower
  CanonicalCentres StepOneValue StepOneLowerDomain StepOneValueMasked
  GlobalComponents HomogenizedGlueingTower MarkedIdealOperationsAlong RestrictedIdealWeight
  RestrictLeCalculus GermIdealOrder StepOneRegime NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual retained indexed level and the original mask construct membership
in the remaining strict carrier before any lower-cosupport assertion. -/
theorem original_positive_member_endpoint_mem_carrier (hn : 0<n)
    (M : MarkedIdeal n X) (hw : M.IsWellFormed) (hd : 1≤M.d)
    (H : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked M) (H.append R)) (y : Z) (s : ℕ)
    (hreg : stepRegime M (s+1) H (R.proj y))
    (hlevel : level M (H.append R) y=s+1)
    (hy : y ∈ (geoTransformAlong (barMarked M) (H.append R)).cosupp) :
    y ∈ (geoTransformAlong (memberLowerExtension M H (R.proj y)) R).N := by
  obtain ⟨hH,hR⟩ := (isGeoTestTower_append_iff (barMarked M) H R).mp hT
  let m := geoTransformAlong (barMarked M) H
  let E₀ := origMembers M H
  let y₀ := R.proj y
  let S := membersThrough m.E E₀ y₀
  let F := m.N ∩ memberInter m.E S
  let K := memberLowerExtension M H y₀
  have hm := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked M hw) H hH
  have hy' : y ∈ (geoTransformAlong m R).cosupp := by
    simpa only [geoTransformAlong_append] using hy
  have hy₀ := proj_mem_cosupp_of_mem_cosupp hm.isClosedSubmanifold_N hm.isCoherent R hR hy'
  have hMask : y₀ ∈ maskA M H y₀ :=
    mem_maskA M hw hd hn H hH (by rw [hreg.1];omega) hreg.2
  have hE₀ : ∀ A ∈ E₀,A ∈ m.E := fun _ hA => List.mem_of_mem_take hA
  have hy₀F : y₀ ∈ F := by
    refine ⟨hy₀.1,?_⟩
    change y₀ ∈ memberInter m.E (membersThrough m.E E₀ y₀)
    rw [memberInter_membersThrough hE₀ y₀]
    exact fun _ _ h => h
  have hEq := pullback_memberLowerExtension_eq_lowerMarked_succ hn M hw H hH y₀ hreg.1
  have hy₀K : y₀ ∈ K.N := by
    let p₀ : maskA M H y₀ := ⟨y₀,hMask⟩
    have hp₀ : p₀ ∈ (lowerMarked M (s+1) H y₀).N := hy₀F
    have hp₀K : p₀ ∈ (MarkedIdeal.pullback (Subtype.val : maskA M H y₀ → Y)
        (memberLowerExtension M H y₀)).N := by
      rw [hEq]
      exact hp₀
    exact hp₀K
  have hMembers := (StepOneCompare.level_eq_iff_of_mem_maskA M
    (fun A hA => hw.isSNCDivisor.1 A hA) H R hMask).mp (hlevel.trans hreg.1.symm)
  have hyF : y ∈ strictAlong R F := by
    rw [strictAlong_inter_memberInter m hm S R hR]
    refine ⟨hy'.1,fun i hi => ?_⟩
    obtain ⟨hi₀,hyi⟩ := mem_membersThrough.mp hi
    exact hMembers _ hi₀ hyi
  have hF : IsClosedSubmanifold n F := isClosedSubmanifold_inter_memberInter hn
    hm.isClosedSubmanifold_N.1 hm.isSNCDivisor hm.isTransverse S
  have hSel : selectedComponents (n := n) F m.cosupp ⊆ F := by
    rintro x ⟨A,⟨hA,_⟩,hx⟩
    exact subset_of_mem_globalComponents (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hF) hA hx
  have hPart : F=K.N ∪ selectedComponents (n := n) F m.cosupp := by
    change F=remainingComponents (n := n) F m.cosupp ∪ selectedComponents (n := n) F m.cosupp
    rw [remainingComponents_eq_diff_selected hF]
    exact (sdiff_union_of_subset hSel).symm
  have hDis : Disjoint K.N (selectedComponents (n := n) F m.cosupp) := by
    change Disjoint (remainingComponents (n := n) F m.cosupp) _
    rw [remainingComponents_eq_diff_selected hF]
    exact disjoint_sdiff_left
  change y ∈ (geoTransformAlong K R).N
  rw [N_geoTransformAlong,strictAlong_eq_inter_preimage_of_closed_partition (A := K.N)
    (isClosedSubmanifold_remainingComponents hF m.cosupp).1
    (isClosedSubmanifold_selectedComponents hF m.cosupp).1 hDis hPart R]
  exact ⟨hyF,hy₀K⟩

/-- ONLY the actual original upper TEST/current point and retained positive
head regime internally supply the actual computed lower current membership. -/
theorem original_computed_positive_member_current_cosupport (hn : 0<n)
    (M : MarkedIdeal n X) {b : ℕ} (hM : IsInvDomain b M)
    (H : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower M (H.append R)) (y : Z) (s : ℕ)
    (hreg : stepRegime M (s+1) H (R.proj y))
    (hlevel : level M (H.append R) y=s+1)
    (hy : y ∈ (geoTransformAlong M (H.append R)).cosupp) :
    ∃ hp : R.proj y ∈ maskA M H (R.proj y),
      (⟨y,hp⟩ : openPreimage R (maskA M H (R.proj y))) ∈
        (geoTransformAlong (lowerMarked M (s+1) H (R.proj y))
          (restrict (maskA M H (R.proj y)) R)).cosupp := by
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 (H.append R)).1.mpr hT
  have hyBar : y ∈ (geoTransformAlong (barMarked M) (H.append R)).cosupp := by
    rw [(he.2 (H.append R)).2 hBar]
    exact hy
  obtain ⟨hH,hR⟩ := (isGeoTestTower_append_iff (barMarked M) H R).mp hBar
  let m := geoTransformAlong (barMarked M) H
  let S := membersThrough m.E (origMembers M H) (R.proj y)
  let K := memberLowerExtension M H (R.proj y)
  let B := coeffMarkedAlong m
  have hm := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked M hM.isWellFormed) H hH
  have hd : 1≤m.d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hF : IsClosedSubmanifold n (m.N ∩ memberInter m.E S) := isClosedSubmanifold_inter_memberInter hn
    hm.isClosedSubmanifold_N.1 hm.isSNCDivisor hm.isTransverse S
  have hKclosed : IsClosed K.N := (isClosedSubmanifold_remainingComponents hF m.cosupp).1
  have hKsub : K.N ⊆ B.N := by
    change remainingComponents (n := n) (m.N ∩ memberInter m.E S) m.cosupp ⊆ m.N
    rw [remainingComponents_eq_diff_selected hF]
    exact fun _ hx => hx.1.1
  have hB : B.IsWellFormed :=
    ⟨hm.isClosedSubmanifold_N,isCoherent_coeffMarkedAlong hm.isCoherent hm.isClosedSubmanifold_N,
      hm.isSNCDivisor,hm.isTransverse⟩
  have hRef := coeffAlong_tower m hm.isClosedSubmanifold_N hm.isCoherent hd R
  have hTB : IsGeoTestTower B R := hRef.1.mpr hR
  have hyRef : y ∈ (geoTransformAlong B R).cosupp := by
    rw [hRef.2 hR]
    simpa only [geoTransformAlong_append] using hyBar
  have hyK : y ∈ (geoTransformAlong K R).N :=
    original_positive_member_endpoint_mem_carrier hn M hM.isWellFormed hM.one_le_d H R hBar y s hreg hlevel hyBar
  have hInitial : RestrictLe K.N K.ideal B.ideal := restrictLe_refl hB.isCoherent
  have hPoint := reference_cosupp_inter_carrier_subset B K hB hKclosed hKsub rfl hInitial R hTB ⟨hyRef,hyK⟩
  have hMask : R.proj y ∈ maskA M H (R.proj y) :=
    mem_maskA M hM.isWellFormed hM.one_le_d hn H hH (by rw [hreg.1];omega) hreg.2
  obtain ⟨hCurrent,hWhole⟩ := memberLowerExtension_tail_domain_and_mask_identity hn M hM H hH (R.proj y) hreg.1 R hR
  refine ⟨hMask,?_⟩
  rw [hWhole,cosupp_pullback_val _
    (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent hf)]
  exact hPoint

/-- The UNCHANGED original run internally produces its retained positive head,
actual endpoint mask and lower current-cosupport membership. -/
theorem original_run_positive_member_current_cosupport (hn : 0<n)
    (M : MarkedIdeal n X) {b : ℕ} (hM : IsInvDomain b M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) (hsp : ¬ IsSpecial M T y)
    {s : ℕ} (hlevel : level M T y=s+1) :
    let r := regimeRun (stepRegime M (level M T y)) T y
    let H := head T r
    let R := tail T r
    ∃ hp : R.proj y ∈ maskA M H (R.proj y),
      (⟨y,hp⟩ : openPreimage R (maskA M H (R.proj y))) ∈
        (geoTransformAlong (lowerMarked M (s+1) H (R.proj y))
          (restrict (maskA M H (R.proj y)) R)).cosupp := by
  let r := regimeRun (stepRegime M (level M T y)) T y
  let H := head T r
  let R := tail T r
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 T).1.mpr hT
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar]
    exact hy
  have hh : stepRegime M (level M T y) H (R.proj y) :=
    (stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hsp).1
  have hreg : stepRegime M (s+1) H (R.proj y) := by simpa only [hlevel] using hh
  have hApp : H.append R=T := head_append_tail T r
  have hTa : IsGeoTestTower M (H.append R) := by rwa [hApp]
  have hyA : y ∈ (geoTransformAlong M (H.append R)).cosupp := by rwa [hApp]
  have hlA : level M (H.append R) y=s+1 := by rwa [hApp]
  exact original_computed_positive_member_current_cosupport hn M hM H R hTa y s hreg hlA hyA

/-- Actual run membership supplies the formerly explicit hp of the exact
original computed-member GENERAL formula at EVERY depth, without lower TEST. -/
theorem original_run_positive_member_lower_full_value_formula (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) (hsp : ¬ IsSpecial M T y)
    {s : ℕ} (hlevel : level M T y=s+1) :
    let r := regimeRun (stepRegime M (level M T y)) T y
    let H := head T r
    let R := tail T r
    ∃ hp : R.proj y ∈ maskA M H (R.proj y),
      let K := lowerMarked M (s+1) H (R.proj y)
      let Q := restrict (maskA M H (R.proj y)) R
      let p : openPreimage R (maskA M H (R.proj y)) := ⟨y,hp⟩
      (invFamily hn (k+1)).inv K Q p=
        if nmOrd (geoTransformAlong K Q) p=0 then
          toLex (0,toLex (Sum.inl (MonomialCaseAlong.gammaAlong n (geoTransformAlong K Q).N
            (geoTransformAlong K Q).ideal (geoTransformAlong K Q).E (geoTransformAlong K Q).d p)))
        else toLex (nmOrd (geoTransformAlong K Q) p,toLex (Sum.inr
          ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  let r := regimeRun (stepRegime M (level M T y)) T y
  let H := head T r
  let R := tail T r
  obtain ⟨hp,hPoint⟩ := original_run_positive_member_current_cosupport hn M hM T hT y hy hsp hlevel
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 T).1.mpr hT
  have hyBar : y ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar]
    exact hy
  have hh : stepRegime M (level M T y) H (R.proj y) :=
    (stepRegime_and_mem_cosupp_head M hM.isWellFormed T hBar hyBar hsp).1
  have hHeadLevel : level M H (R.proj y)=s+1 := hh.1.trans hlevel
  have hApp : H.append R=T := head_append_tail T r
  have hTa : IsGeoTestTower M (H.append R) := by rwa [hApp]
  refine ⟨hp,?_⟩
  exact HironakaOriginalUntestedMemberOpenFullValues.original_computed_positive_member_lower_full_value_formula
    hn k M hM H R hTa (R.proj y) s hHeadLevel hp ⟨y,hp⟩ hPoint
end
end Hironaka.HironakaOriginalPositiveMemberCurrentCosupport
