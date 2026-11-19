/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutEmptyPrefixContact
import Hironaka.Invariant.StepOneEmptyPrefix
/-! Actual positive member masks and full relative ideal equivalence preserve
ALL original lower values across a true empty prefix, without lower CAN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveEmptyPrefixHeadValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactRepresentative ContactEmptyPrefix
  InvDomainMemberRestriction StepOneValue StepOneValueMasked StepOneLowerDomain
  StepOneRegime StepOneMaskTower StepOneEmptyPrefix CanonicalCentres
  HironakaOriginalFullCutEmptyPrefixContact
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- Genuine equal opens compare the literal finite/top original masked values
on all actual histories and at every depth, without canonical lower data. -/
theorem masked_full_values_congr (hn : 0<n) (q : ℕ)
    (M N : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : N.IsWellFormed)
    (hEq : RestrictEquiv M N) {U V : Opens B} (hUV : U=V)
    (T : BlowupTower B Y) (z : Y) :
    (if h : T.proj z∈U then
      (((invFamily hn q).inv (MarkedIdeal.pullback (Subtype.val : U → B) M)
        (restrict U T) ⟨z,h⟩ : ValTy q) : WithTop (ValTy q)) else ⊤)=
    (if h : T.proj z∈V then
      (((invFamily hn q).inv (MarkedIdeal.pullback (Subtype.val : V → B) N)
        (restrict V T) ⟨z,h⟩ : ValTy q) : WithTop (ValTy q)) else ⊤) := by
  subst V
  by_cases hz : T.proj z∈U
  · simp only [dif_pos hz]
    have hEqU := restrictEquiv_pullback_val U hEq hM.isCoherent hN.isCoherent
    have hMU := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM U
    have hNU := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U
    exact congrArg (fun v : ValTy q => (v : WithTop (ValTy q)))
      (full_values_of_restrictEquiv hn _ _ hMU hNU.isCoherent hEqU q (restrict U T) ⟨z,hz⟩)
  · simp only [dif_neg hz]

/-- True original mask/member geometry internally supplies positive-level
same-head empty-prefix equality on EVERY tail at ALL original depths. -/
theorem positive_lower_value_empty_prefix_head (hn : 0<n) (q : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (H : BlowupTower A B)
    (hHead : IsGeoTestTower (barMarked J) (P.append H)) (T : BlowupTower B Y)
    (s : ℕ) (z : Y) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn q) J (lowerMarkedM J) (s+1) (P.append H) T z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn q) (geoTransformAlong J P)
        (lowerMarkedM (geoTransformAlong J P)) (s+1) H T z := by
  have hW := maskA_emptyPrefix J hJ hd P hP H hHead (T.proj z)
  have hEqJ := restrictEquiv_barMarked_append J hJ hd P hP H hHead
  obtain ⟨L,hL,hE⟩ := origMembers_emptyPrefix J P hP H
  have hBar := isWellFormed_barMarked J hJ
  have hOldWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBar _ hHead
  have hPt : IsGeoTestTower J P := isGeoTestTower_of_isEmptyTower J P hP
  have hNewBar := isWellFormed_barMarked _
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ P hPt)
  have hHead' : IsGeoTestTower (barMarked (geoTransformAlong J P)) H :=
    (isGeoTestTower_barMarked_geoTransformAlong_iff J hJ.isClosedSubmanifold_N
      hJ.isCoherent hd P hP H).mpr hHead
  have hNewWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hNewBar H hHead'
  have hEqM : RestrictEquiv
      (memberRestrict (geoTransformAlong (barMarked (geoTransformAlong J P)) H)
        (membersThrough (geoTransformAlong (barMarked (geoTransformAlong J P)) H).E
          (origMembers (geoTransformAlong J P) H) (T.proj z)))
      (memberRestrict (geoTransformAlong (barMarked J) (P.append H))
        (membersThrough (geoTransformAlong (barMarked J) (P.append H)).E
          (origMembers J (P.append H)) (T.proj z))) := by
    rw [hE,membersThrough_append_of_forall_eq_empty _ _ _ hL]
    exact restrictEquiv_memberRestrict_membersThrough hEqJ hNewWF.isCoherent hOldWF.isCoherent _ _
  exact (masked_full_values_congr hn q _ _ (isWellFormed_memberRestrict hn hNewWF _)
    (isWellFormed_memberRestrict hn hOldWF _) hEqM hW T z).symm

end
end Hironaka.HironakaOriginalPositiveEmptyPrefixHeadValues
