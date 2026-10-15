/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalZeroStepOneEtaleValues
import Hironaka.Resolution.HironakaStepOneMemberTailExtension
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
/-! Actual CURRENT curve coefficient geometry proves original special leaves
without assuming the lower member history is a TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedMemberCurveSpecial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  RelativePrincipalizationSpan GermIdealOrder NormalCrossings MonomialPartAlong
  StepOneValue StepOneLowerDomain StepOneValueMasked CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  MemberInterAlong MemberInterLocusAlong InvDomainMemberRestriction BoundaryCount
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension HironakaCoherentTransformExtension
  HironakaOneDimensionalCanonicalSuperlevels CodimOneSupportAlong RegularPointDimension
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Real positive cosupport excludes dimension-zero carrier germs by genuine
nonzero-along witnesses, before actual zero-dimensional cosupport geometry. -/
theorem actual_curve_cosupport_regular_dimensions (B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (x : X) (hx : x ∈ B.cosupp) :
    RegularAtDim (n := n) B.N x 1 ∧ RegularAtDim (n := n) B.cosupp x 0 := by
  have hAnalytic := isComplexAnalyticSubset_cosupport_along hB.isWellFormed.isCoherent
    hB.isWellFormed.isClosedSubmanifold_N hB.one_le_d
  have hZero := regularAtDim_zero_of_analytic_dimLE_zero hAnalytic (dimLE_cosupport_of_isInvDomain hB) hx
  obtain ⟨j,hj,hReg⟩ := hB.dimLE x hx.1
  by_cases hj0 : j=0
  · rw [hj0] at hReg
    obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hReg
    obtain ⟨g,hg,hfreq⟩ := hB.isNonzeroAlongAt x hx.1
    obtain ⟨y,⟨hyN,hyG⟩,hyU⟩ := (hfreq.and_eventually (hU.mem_nhds hxU)).exists
    have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyN,hyU⟩)
    have hxOne := cosupport_anti hB.one_le_d hx
    rw [cosupport_one (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hf)] at hxOne
    exact False.elim ((hyx ▸ hyG) (hxOne.2 g hg))
  · have hj1 : j=1 := by omega
    rw [hj1] at hReg
    exact ⟨hReg,hZero⟩

/-- Pure CURRENT geometry: no TEST of the original or coefficient record,
no original maximal-order or desired SPECIAL certificate is assumed. -/
theorem isSpecial_of_current_bar_curve_domain (hn : 0<n) (A : MarkedIdeal n X)
    (T : BlowupTower X Y) (hB : IsInvDomain 1 (geoTransformAlong (barMarked A) T))
    (x : Y) (hx : x ∈ (geoTransformAlong (barMarked A) T).cosupp) : IsSpecial A T x := by
  let B := geoTransformAlong (barMarked A) T
  obtain ⟨hN,hS⟩ := actual_curve_cosupport_regular_dimensions B hB x hx
  by_cases hl : level A T x=0
  · exact Or.inl ⟨hl,0,hN,hS⟩
  · have hpos : 1≤level A T x := by omega
    let E₀ := origMembers A T
    have hE₀ : ∀ H ∈ E₀,H ∈ B.E := fun H hH => List.mem_of_mem_take hH
    let I := membersThrough B.E E₀ x
    have hI : I.Nonempty := membersThrough_nonempty hE₀ hpos
    have hxI : x ∈ B.N ∩ memberInter B.E I := by
      refine ⟨hx.1,?_⟩
      rw [memberInter_membersThrough hE₀ x]
      exact fun _ _ hh => hh
    obtain ⟨j,hj,hReg⟩ := exists_regularAtDim_inter_memberInter_lt hn hB.isWellFormed.isSNCDivisor
      hB.isWellFormed.isTransverse hI hxI hN
    have hj0 : j=0 := by omega
    rw [hj0] at hReg
    obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hReg
    refine Or.inr ⟨hpos,?_⟩
    rw [mem_memberInterLocus_iff]
    refine ⟨hx,?_⟩
    filter_upwards [hU.mem_nhds hxU] with y hy hyN hyE
    have hyI : y ∈ B.N ∩ memberInter B.E I := by
      refine ⟨hyN,?_⟩
      rw [memberInter_membersThrough hE₀ x]
      exact hyE
    have hyx : y=x := mem_singleton_iff.mp (hsub ⟨hyI,hy⟩)
    exact hyx ▸ hx

private theorem same_member_geometry_domains (m K B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (hN : B.N=K.N) (hE : B.E=K.E)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong K R)) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower m R → IsInvDomain 1 (geoTransformAlong B R)
  | _,.refl,_ => hB
  | _,.step R C π hπ,hR => by
    have hPrev := same_member_geometry_domains m K B hB hN hE hModel R hR.1
    have hNext := hModel (.step R C π hπ) hR
    have hN' := geoTransformAlong_N_eq_of_N_eq hN (.step R C π hπ)
    have hE' := geoTransformAlong_E_eq_of_E_eq hE (.step R C π hπ)
    have hSM : IsClosedSubmanifold n ((geoTransformAlong B R).geoTransform C π).N := by
      change IsClosedSubmanifold n (geoTransformAlong B (.step R C π hπ)).N
      rw [hN']
      exact hNext.isWellFormed.isClosedSubmanifold_N
    refine ⟨⟨hSM,isCoherent_geoTransform_ideal_of_smooth_strict _ hPrev.isWellFormed.isCoherent hπ hSM,?_,?_⟩,?_,?_,?_⟩
    · rw [hE'];exact hNext.isWellFormed.isSNCDivisor
    · rw [hN',hE'];exact hNext.isWellFormed.isTransverse
    · rw [hN'];exact hNext.dimLE
    · rw [d_geoTransformAlong];exact hB.one_le_d
    · exact isNonzeroAlongAt_geoTransform_of_smooth_strict _ hPrev.isWellFormed.isClosedSubmanifold_N
        hPrev.isWellFormed.isCoherent hπ hSM hPrev.isNonzeroAlongAt

/-- Genuine original member geometry supplies ANY actual same-geometry ideal's
entire current domain, with no TEST or admissibility for that candidate. -/
theorem actual_member_same_geometry_curve_domains (hn : 0<n) (m : MarkedIdeal n X)
    (hm : IsInvDomain 2 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (B : MarkedIdeal n X) (hB : IsInvDomain 1 B)
    (hN : B.N=(memberRemainderMarked m S).N) (hE : B.E=(memberRemainderMarked m S).E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) : IsInvDomain 1 (geoTransformAlong B T) := by
  apply same_member_geometry_domains m (memberRemainderMarked m S) B hB hN hE _ T hT
  intro V R hR
  exact isInvDomain_geoTransformAlong_memberRemainder hn m hm.isWellFormed hm.one_le_d hm.dimLE S hS R hR

/-- ONLY genuine original positive-head data internally select the actual
member lower and ALL prefix coefficient domains BEFORE untested special leaves. -/
theorem original_positive_member_curve_step_one_values (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 2 M) (H : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower M (H.append R)) (y₀ : Y) (hl : 1≤level M H y₀) :
    let A := memberLowerExtension M H y₀
    ∀ i : ℕ,IsInvDomain 1 (geoTransformAlong A (head R i)) ∧
      IsInvDomain 1 (geoTransformAlong (barMarked A) (head R i)) ∧
      ∀ x : (split R i).1,x ∈ (geoTransformAlong (barMarked A) (head R i)).cosupp →
        IsSpecial A (head R i) x ∧ ∀ k : ℕ,
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) A (head R i) x=toLex (level A (head R i) x,⊤) := by
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBarT : IsGeoTestTower (barMarked M) (H.append R) := (he.2 _).1.mpr hT
  obtain ⟨hH,hR⟩ := (isGeoTestTower_append_iff (barMarked M) H R).mp hBarT
  let m := geoTransformAlong (barMarked M) H
  have hm : IsInvDomain 2 m := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked M hM) H hH
  let S := membersThrough m.E (origMembers M H) y₀
  have hE₀ : ∀ F ∈ origMembers M H,F ∈ m.E := fun F hF => List.mem_of_mem_take hF
  have hS : S.Nonempty := membersThrough_nonempty hE₀ hl
  let A := memberLowerExtension M H y₀
  have hA : IsInvDomain 1 A := isInvDomain_memberRemainderMarked hn m hm.isWellFormed hm.one_le_d hm.dimLE S hS
  have hBA := isInvDomain_barMarked A hA
  dsimp only
  intro i
  have hi := ((isGeoTestTower_iff_head_tail m R i).mp hR).1
  have hAI : IsInvDomain 1 (geoTransformAlong A (head R i)) :=
    isInvDomain_geoTransformAlong_memberRemainder hn m hm.isWellFormed hm.one_le_d hm.dimLE S hS _ hi
  have hBI := actual_member_same_geometry_curve_domains hn m hm S hS (barMarked A) hBA rfl rfl (head R i) hi
  refine ⟨hAI,hBI,fun x hx => ?_⟩
  have hs := isSpecial_of_current_bar_curve_domain hn A (head R i) hBI x hx
  refine ⟨hs,fun k => ?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hs]

end
end Hironaka.HironakaOriginalUntestedMemberCurveSpecial
