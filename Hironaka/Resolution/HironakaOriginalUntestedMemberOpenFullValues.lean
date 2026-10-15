/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedMemberCurveFullValues
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing
/-! Exact ORIGINAL computed positive-member open masks, including actual
remaining components, before their whole untested GENERAL values. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedMemberOpenFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  HironakaOriginalUntestedMemberCurveFullValues HironakaCoherentTransformExtension HironakaStepOneMemberLowerExtension
  HironakaStepOneMemberTailExtension HironakaStepOneZeroContactRemainderExtension
  HironakaStepOneZeroContactRemainderGlueing HironakaDimensionTwoStepOneAnalyticSuperlevels
  GlobalComponents InvDomainMemberRestriction InvDomainRebase BoundaryCount MemberInterAlong
  CoefficientIdealRestriction NormalCrossings HomogenizedIdealAlong HomogenizedIdealAlongTower
  CanonicalCentres StepOneValue StepOneValueMasked StepOneLowerDomain NonmonomialOrderLocal
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual global components lie in the real smooth member carrier BEFORE
both original cosupports select precisely the SAME remaining components. -/
theorem memberRemainderMarked_eq_contactRemainder_zero (hn : 0<n) (m : MarkedIdeal n X)
    (hm : m.IsWellFormed) (hd : 1≤m.d) (S : Finset (Fin m.E.length)) :
    memberRemainderMarked m S=contactRemainderMarked (memberRestrict m S) 0 := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change remainingComponents (n := n) (m.N ∩ memberInter m.E S) m.cosupp=
      remainingComponents (n := n) (m.N ∩ memberInter m.E S) (memberRestrict m S).cosupp
    rw [cosupp_memberRestrict hm hd]
    have hH := isClosedSubmanifold_inter_memberInter hn hm.isClosedSubmanifold_N.1 hm.isSNCDivisor hm.isTransverse S
    unfold remainingComponents
    congr 1
    ext B
    apply and_congr_right
    intro hB
    apply not_congr
    constructor
    · intro h x hx
      exact ⟨h hx,(subset_of_mem_globalComponents (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH) hB hx).2⟩
    · exact fun h x hx => (h hx).1
  · change (memberRestrict m S).E=List.replicate 0 ∅ ++ (memberRestrict m S).E.drop 0
    simp
  · rfl
  · rfl

/-- Genuine whole coefficient/member open restriction precedes actual
remaining-component naturality; ALL FOUR marked fields remain literal. -/
theorem pullback_val_memberRemainder_membersThrough (hn : 0<n) (m : MarkedIdeal n X)
    (hm : m.IsWellFormed) (hd : 1≤m.d) (E₀ : List (Set X)) (hE₀ : ∀ F ∈ E₀,F ∈ m.E)
    (U : Opens X) (p : U) :
    MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m (membersThrough m.E E₀ p))=
      memberRemainderMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) m)
        (membersThrough (MarkedIdeal.pullback (Subtype.val : U → X) m).E
          (E₀.map ((Subtype.val : U → X) ⁻¹' ·)) p) := by
  let S := membersThrough m.E E₀ p
  have hR := isWellFormed_memberRestrict hn hm S
  rw [memberRemainderMarked_eq_contactRemainder_zero hn m hm hd S,
    ←contactRemainderMarked_pullback_val (memberRestrict m S) 0 hR.isClosedSubmanifold_N hR.isCoherent
      (one_le_memberRestrict_d m S) U]
  rw [pullback_val_memberRestrict_membersThrough hm hd hE₀ U p]
  exact (memberRemainderMarked_eq_contactRemainder_zero (X := CMfd.of (n := n) U) hn
    (MarkedIdeal.pullback (Subtype.val : U → X) m) (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hm U) hd _).symm

/-- ONLY original open geometry internally supplies the true open member
model; no TEST of the lower reference is inferred. -/
theorem original_open_member_untested_full_value_formula (hn : 0<n) (k : ℕ)
    (m : MarkedIdeal n X) (hm : IsInvDomain 2 m) (E₀ : List (Set X))
    (hE₀ : ∀ F ∈ E₀,F ∈ m.E) (U : Opens X) (p₀ : U) (hPos : 1≤boundaryCount E₀ (p₀ : X))
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (p : openPreimage T U)
    (hp : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (memberRemainderMarked m (membersThrough m.E E₀ p₀))) (restrict U T)).cosupp) :
    let K := MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m (membersThrough m.E E₀ p₀))
    (invFamily hn (k+1)).inv K (restrict U T) p=
      if nmOrd (geoTransformAlong K (restrict U T)) p=0 then
        toLex (0,toLex (Sum.inl (MonomialCaseAlong.gammaAlong n (geoTransformAlong K (restrict U T)).N
          (geoTransformAlong K (restrict U T)).ideal (geoTransformAlong K (restrict U T)).E
          (geoTransformAlong K (restrict U T)).d p)))
      else toLex (nmOrd (geoTransformAlong K (restrict U T)) p,toLex (Sum.inr
        ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  let mU := MarkedIdeal.pullback (Subtype.val : U → X) m
  let F₀ := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let S := membersThrough mU.E F₀ p₀
  have hmU : IsInvDomain 2 mU := InvDomainTowerAlong.isInvDomain_pullback_val U hm
  have hF₀ : ∀ F ∈ F₀,F ∈ mU.E := by
    intro F hF
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hF
    exact List.mem_map_of_mem (hE₀ D hD)
  have hCount : boundaryCount F₀ p₀=boundaryCount E₀ (p₀ : X) :=
    CodimOnePartCanonical.boundaryCount_map_preimage _ _ p₀
  have hS : S.Nonempty := membersThrough_nonempty hF₀ (by rw [hCount];exact hPos)
  have hEq := pullback_val_memberRemainder_membersThrough hn m hm.isWellFormed hm.one_le_d E₀ hE₀ U p₀
  have hTest := isGeoTestTower_restrict U hm.isWellFormed.isClosedSubmanifold_N hm.isWellFormed.isCoherent T hT
  rw [hEq] at hp ⊢
  exact original_member_curve_untested_full_value_formula (X := CMfd.of (n := n) U)
    hn k mU hmU S hS (restrict U T) hTest p hp

/-- ONLY original positive-head history identifies the ACTUAL computed mask
and ALL FOUR literal lowerMarked fields BEFORE whole original GENERAL values. -/
theorem original_computed_positive_member_lower_full_value_formula (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (H : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower M (H.append R)) (y₀ : Y) (s : ℕ) (hl : level M H y₀=s+1)
    (hy₀ : y₀ ∈ maskA M H y₀) (p : openPreimage R (maskA M H y₀))
    (hp : p ∈ (geoTransformAlong (lowerMarked M (s+1) H y₀) (restrict (maskA M H y₀) R)).cosupp) :
    let K := lowerMarked M (s+1) H y₀
    let T := restrict (maskA M H y₀) R
    (invFamily hn (k+1)).inv K T p=
      if nmOrd (geoTransformAlong K T) p=0 then
        toLex (0,toLex (Sum.inl (MonomialCaseAlong.gammaAlong n (geoTransformAlong K T).N
          (geoTransformAlong K T).ideal (geoTransformAlong K T).E (geoTransformAlong K T).d p)))
      else toLex (nmOrd (geoTransformAlong K T) p,toLex (Sum.inr
        ((toLex (0,(⊤ : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar := (he.2 (H.append R)).1.mpr hT
  obtain ⟨hH,hR⟩ := (isGeoTestTower_append_iff (barMarked M) H R).mp hBar
  let m := geoTransformAlong (barMarked M) H
  have hm : IsInvDomain 2 m := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked M hM) H hH
  have hE₀ : ∀ F ∈ origMembers M H,F ∈ m.E := fun F hF => List.mem_of_mem_take hF
  have hPos : 1≤boundaryCount (origMembers M H) y₀ := by change 1≤level M H y₀;rw [hl];omega
  have hEq := pullback_memberLowerExtension_eq_lowerMarked_succ hn M hM.isWellFormed H hH y₀ hl
  change MarkedIdeal.pullback (Subtype.val : maskA M H y₀ → Y)
    (memberRemainderMarked m (membersThrough m.E (origMembers M H) y₀))=lowerMarked M (s+1) H y₀ at hEq
  have hp' : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : maskA M H y₀ → Y)
      (memberRemainderMarked m (membersThrough m.E (origMembers M H) y₀))) (restrict (maskA M H y₀) R)).cosupp := by
    rw [hEq];exact hp
  have hv := original_open_member_untested_full_value_formula hn k m hm (origMembers M H) hE₀
    (maskA M H y₀) (⟨y₀,hy₀⟩ : maskA M H y₀) hPos R hR p hp'
  dsimp only at hv ⊢
  simpa only [hEq] using hv

end
end Hironaka.HironakaOriginalUntestedMemberOpenFullValues
