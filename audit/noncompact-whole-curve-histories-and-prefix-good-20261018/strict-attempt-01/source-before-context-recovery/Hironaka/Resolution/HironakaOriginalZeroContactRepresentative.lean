/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalRelativeIdealLevelCut
import Hironaka.Resolution.HironakaOriginalCurveTangentChange
import Hironaka.Resolution.HironakaOriginalCurveLocalReferenceComparison
/-! Actual local curve geometry and genuine kept-contact relative equality
compare independent zero-contact choices without lower canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroContactRepresentative
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  MarkedIdealEquivalence.MarkedIdeal HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealRestriction ContactStageKept ContactRepresentative ContactLowerValue InvDomainRebase TangentDirectionAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime StepOneCompare StepOneRepresentative
  CanonicalCentres HironakaOriginalFullCutEmptyPrefixContact HironakaOriginalCurveTangentChange
  HironakaOriginalCurveLocalReferenceComparison
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X B Y : CMfd.{u} n}

/-- Genuine ordinary lower domains and TESTs remain explicit generic inputs;
no lower CAN or equality of the two chosen tangent functions is assumed. -/
theorem zero_lower_values_of_restrictEquiv (hn : 0<n) (k : ℕ)
    (J N : MarkedIdeal n X) (hJ : J.IsWellFormed) (hN : N.ideal.IsCoherent)
    (hd : 1≤J.d) (hEq : RestrictEquiv J N) (H : BlowupTower X B) (T : BlowupTower B Y)
    (hUpper : IsGeoTestTower (barMarked J) (H.append T)) (z : Y)
    (hz : z∈(geoTransformAlong (barMarked J) (H.append T)).cosupp)
    (hDom : IsInvDomain 1 (lowerMarkedB J H (T.proj z)))
    (hTest : IsGeoTestTower (lowerMarkedB J H (T.proj z)) (restrict (maskB J H (T.proj z)) T))
    (hDomN : IsInvDomain 1 (lowerMarkedB N H (T.proj z)))
    (hTestN : IsGeoTestTower (lowerMarkedB N H (T.proj z)) (restrict (maskB N H (T.proj z)) T))
    (hp : T.proj z∈maskB J H (T.proj z)) (hpN : T.proj z∈maskB N H (T.proj z)) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 H T z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) N (lowerMarkedM N) 0 H T z := by
  let W := maskB J H (T.proj z)
  let V := maskB N H (T.proj z)
  let w := (tangentChoice J (H.proj (T.proj z))).2
  let Uw := (tangentChoice J (H.proj (T.proj z))).1
  have hxUw : H.proj (T.proj z)∈Uw := (interior_subset hp).1
  have hw := tangentChoice_spec_of_mem J hxUw
  have hNWF : N.IsWellFormed := by
    refine ⟨hEq.N_eq ▸ hJ.isClosedSubmanifold_N,hN,hEq.E_eq ▸ hJ.isSNCDivisor,?_⟩
    rw [←hEq.N_eq,←hEq.E_eq];exact hJ.isTransverse
  have hdN : 1≤N.d := hEq.d_eq ▸ hd
  have hFacts := restrictEquiv_facts hJ hN hEq (H.append T)
  have hUpperN := hFacts.2.2.1.mp hUpper
  have hzN : z∈(geoTransformAlong (barMarked N) (H.append T)).cosupp := by
    rw [←hFacts.2.1];exact hz
  have hHead := ((isGeoTestTower_append_iff _ H T).mp hUpper).1
  have hHeadN := ((isGeoTestTower_append_iff _ H T).mp hUpperN).1
  have hx : H.proj (T.proj z)∈J.cosupp := by
    have hh := proj_mem_cosupp_of_mem_cosupp (isWellFormed_barMarked J hJ).isClosedSubmanifold_N
      (isWellFormed_barMarked J hJ).isCoherent _ hUpper hz
    rw [cosupp_barMarked J hJ hd,BlowupTower.proj_append] at hh
    exact hh
  have hxN : H.proj (T.proj z)∈N.cosupp := by
    have hh := proj_mem_cosupp_of_mem_cosupp (isWellFormed_barMarked N hNWF).isClosedSubmanifold_N
      (isWellFormed_barMarked N hNWF).isCoherent _ hUpperN hzN
    rw [cosupp_barMarked N hNWF hdN,BlowupTower.proj_append] at hh
    exact hh
  obtain ⟨O,hxO,hOU,v,hv,hvw⟩ := exists_isTangentDirectionAlong_of_restrictLe
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ.isCoherent hg)
      hN hJ.isClosedSubmanifold_N hEq.le hw hxUw (J.cosupp_subset_N hx)
  have hvN : IsTangentDirectionAlong N.N N.ideal N.d O v := by
    rw [←hEq.N_eq,←hEq.d_eq];exact hv
  let Wsmall : Opens B := W⊓openPreimage H O
  have hpSmall : T.proj z∈Wsmall := ⟨hp,hxO⟩
  have hSmallO : (Wsmall : Set B)⊆openPreimage H O := fun _ hy => hy.2
  have hSmallUw : (Wsmall : Set B)⊆H.proj ⁻¹' Uw :=
    fun _ hy => (interior_subset hy.1).1
  let K := withN (coeffMarkedAlong (geoTransformAlong (barMarked J) H))
    (strictAlong H (J.N∩{x | w x=0}))
  have hK : K.ideal.IsCoherent := isCoherent_restrictedCoeff J hJ.isCoherent hJ.isClosedSubmanifold_N w H hHead
  obtain ⟨hDsmall,hTsmall,_hCosSmallDict,hValSmall⟩ := local_curve_full_nested_open hn K hK
    (W := W) (V := Wsmall) inf_le_left hDom T hTest
  have hCosSmall : (⟨z,hpSmall⟩ : openPreimage T Wsmall)∈
      (geoTransformAlong (contactMarkedKept J w H Wsmall) (restrict Wsmall T)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J hJ.isClosedSubmanifold_N
      hJ.isCoherent hd ⟨Uw,hw.isOpen⟩ hw H T hUpper Wsmall hSmallUw).2]
    exact hz
  have hEqContact := restrictEquiv_contactMarkedKept hJ.isCoherent hN hJ.isClosedSubmanifold_N
    hEq O (fun y hy hyN => (hvw y hy hyN).symm) H hHead Wsmall hSmallO
  have hCN : (contactMarkedKept N v H Wsmall).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff N hN hNWF.isClosedSubmanifold_N v H hHeadN)
  have hDSmallN := isInvDomain_of_restrictEquiv hDsmall hEqContact hCN
  have hWEquiv := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv
    (X := CMfd.of (n := n) Wsmall) hEqContact hDsmall.isWellFormed.isClosedSubmanifold_N.1
      hDsmall.isWellFormed.isCoherent hCN
  have hTSmallN := ((hWEquiv.2 (restrict Wsmall T)).1).mp hTsmall
  have hxUn : H.proj (T.proj z)∈(tangentChoice N (H.proj (T.proj z))).1 := (interior_subset hpN).1
  have huN := tangentChoice_spec_of_mem N hxUn
  obtain ⟨O₂,hxO₂,hO₂⟩ := curve_full_contact_directions_on_opens hn N hN hNWF.isClosedSubmanifold_N
    hdN hxN hvN hxO huN hxUn
  have hVUn : (V : Set B)⊆H.proj ⁻¹' (tangentChoice N (H.proj (T.proj z))).1 :=
    fun _ hy => (interior_subset hy).1
  have hmSmall : ∀ A∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong N)) H).E.take N.E.length,
      ∀ y∈Wsmall,y∉A := by
    intro A hA y hy hyA
    change A∈origMembers N H at hA
    rw [origMembers_restrictEquiv hEq H] at hA
    exact (interior_subset hy.1).2.1 A hA hyA
  have hmN : ∀ A∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong N)) H).E.take N.E.length,
      ∀ y∈V,y∉A := fun A hA y hy hyA => (interior_subset hy).2.1 A hA hyA
  have hCompare := hO₂ H T hUpperN Wsmall V hSmallO hVUn hmSmall hmN
    hDSmallN hTSmallN hDomN hTestN ⟨z,hpSmall⟩ ⟨z,hpN⟩ rfl hxO₂ hzN k
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J (lowerMarkedM J)
      (s := 0) (T₀ := H) (T₁ := T) (y := z) hp,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) N (lowerMarkedM N)
      (s := 0) (T₀ := H) (T₁ := T) (y := z) hpN]
  exact congrArg (fun x : ValTy (k+1) => (x : WithTop (ValTy (k+1))))
    (((hValSmall ⟨z,hpSmall⟩ hCosSmall k).symm.trans
      (full_values_of_restrictEquiv hn _ _ hDsmall.isWellFormed hCN hEqContact (k+1)
        (restrict Wsmall T) ⟨z,hpSmall⟩)).trans hCompare)

end
end Hironaka.HironakaOriginalZeroContactRepresentative
