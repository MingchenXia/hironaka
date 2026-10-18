/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutEmptyPrefixContact
import Hironaka.Resolution.HironakaOriginalCurveTangentChange
import Hironaka.Invariant.StepOneEmptyPrefix
/-! Actual independent chosen-contact references compare at a genuine same
head after an empty prefix, without lower canonicality or value certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroEmptyPrefixHeadValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactStageKept ContactEmptyPrefix
  InvDomainRebase StepOneValue StepOneValueMasked StepOneLowerDomain StepOneCompare
  StepOneRegime StepOneMaskTower StepOneEmptyPrefix CanonicalCentres
  TangentDirectionAlong HironakaOriginalCurveTangentChange HironakaOriginalFullCutEmptyPrefixContact
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- The two independently chosen original contact references are compared
by true tangent gluing, with ordinary local geometry explicit and no lower CAN. -/
theorem zero_lower_value_empty_prefix_head (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (H : BlowupTower A B) (T : BlowupTower B Y)
    (hT : IsGeoTestTower (barMarked J) ((P.append H).append T)) (z : Y)
    (hz : z∈(geoTransformAlong (barMarked J) ((P.append H).append T)).cosupp)
    (hOld : IsInvDomain 1 (lowerMarkedB J (P.append H) (T.proj z)))
    (hOldTest : IsGeoTestTower (lowerMarkedB J (P.append H) (T.proj z))
      (restrict (maskB J (P.append H) (T.proj z)) T))
    (hNew : IsInvDomain 1 (lowerMarkedB (geoTransformAlong J P) H (T.proj z)))
    (hNewTest : IsGeoTestTower (lowerMarkedB (geoTransformAlong J P) H (T.proj z))
      (restrict (maskB (geoTransformAlong J P) H (T.proj z)) T))
    (hpOld : T.proj z∈maskB J (P.append H) (T.proj z))
    (hpNew : T.proj z∈maskB (geoTransformAlong J P) H (T.proj z)) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 (P.append H) T z=
      Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) (geoTransformAlong J P)
        (lowerMarkedM (geoTransformAlong J P)) 0 H T z := by
  let JP := geoTransformAlong J P
  let Wold := maskB J (P.append H) (T.proj z)
  let Wnew := maskB JP H (T.proj z)
  let w := (tangentChoice J ((P.append H).proj (T.proj z))).2
  let Uw := (tangentChoice J ((P.append H).proj (T.proj z))).1
  have hxUw : (P.append H).proj (T.proj z)∈Uw := (interior_subset hpOld).1
  have hw := tangentChoice_spec_of_mem J hxUw
  have hPt : IsGeoTestTower J P := isGeoTestTower_of_isEmptyTower J P hP
  have hJP : JP.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ P hPt
  have hdP : 1≤JP.d := by dsimp only [JP];rw [d_geoTransformAlong];exact hd
  have hHead := ((isGeoTestTower_append_iff _ (P.append H) T).mp hT).1
  have hSource : IsGeoTestTower (barMarked JP) (H.append T) := by
    apply (isGeoTestTower_barMarked_geoTransformAlong_iff J hJ.isClosedSubmanifold_N hJ.isCoherent
      hd P hP (H.append T)).mpr
    rw [←BlowupTower.append_assoc]
    exact hT
  have hH := ((isGeoTestTower_append_iff _ H T).mp hSource).1
  have hNewBar := isWellFormed_barMarked JP hJP
  have hBar := isWellFormed_barMarked J hJ
  have hJJ := restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower J hJ.isClosedSubmanifold_N hJ.isCoherent hd P hP
  have hcBarP := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hBar.isClosedSubmanifold_N
    hBar.isCoherent P (isGeoTestTower_of_isEmptyTower _ P hP)).2
  have hWhole := RestrictEquiv.wEquiv hJJ hNewBar.isClosedSubmanifold_N.1 hNewBar.isCoherent hcBarP
  have hzSource : z∈(geoTransformAlong (barMarked JP) (H.append T)).cosupp := by
    rw [(hWhole.2 _).2 hSource,←geoTransformAlong_append,←BlowupTower.append_assoc]
    exact hz
  have hx : H.proj (T.proj z)∈JP.cosupp := by
    have h := proj_mem_cosupp_of_mem_cosupp hNewBar.isClosedSubmanifold_N hNewBar.isCoherent _ hSource hzSource
    rw [cosupp_barMarked JP hJP hdP,BlowupTower.proj_append] at h
    exact h
  have hWU : (Wold : Set B)⊆openPreimage (P.append H) (⟨Uw,hw.isOpen⟩ : Opens X) :=
    fun y hy => (interior_subset hy).1
  have hEq := restrictEquiv_symm (restrictEquiv_contactMarkedKept_emptyPrefix J hJ.isClosedSubmanifold_N
    hJ.isCoherent hd ⟨Uw,hw.isOpen⟩ hw P hP H hHead Wold hWU)
  have hCoherent : (contactMarkedKept JP (w ∘ P.proj) H Wold).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff JP hJP.isCoherent hJP.isClosedSubmanifold_N (w ∘ P.proj) H hH)
  have hRDom := isInvDomain_of_restrictEquiv hOld hEq hCoherent
  have hR := RestrictEquiv.wEquiv (X := CMfd.of (n := n) Wold) hEq hOld.isWellFormed.isClosedSubmanifold_N.1
    hOld.isWellFormed.isCoherent hCoherent
  have hRTest := ((hR.2 (restrict Wold T)).1).mp hOldTest
  have hwP : IsTangentDirectionAlong JP.N JP.ideal JP.d (P.proj ⁻¹' Uw) (w ∘ P.proj) := by
    dsimp only [JP]
    rw [d_geoTransformAlong]
    exact (isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower J hJ.isClosedSubmanifold_N
      hJ.isCoherent hw P hP).1
  have hxP : H.proj (T.proj z)∈P.proj ⁻¹' Uw := by
    change P.proj (H.proj (T.proj z))∈Uw
    simpa only [BlowupTower.proj_append,Function.comp_apply] using hxUw
  have hxNew : H.proj (T.proj z)∈(tangentChoice JP (H.proj (T.proj z))).1 := (interior_subset hpNew).1
  have hv := tangentChoice_spec_of_mem JP hxNew
  obtain ⟨O,hxO,hO⟩ := curve_full_contact_directions_on_opens hn JP hJP.isCoherent
    hJP.isClosedSubmanifold_N hdP hx hwP hxP hv hxNew
  have hWUOld : (Wold : Set B)⊆H.proj ⁻¹' (P.proj ⁻¹' Uw) := by
    intro y hy
    change P.proj (H.proj y)∈Uw
    have hyU : (P.append H).proj y∈Uw := (interior_subset hy).1
    simpa only [BlowupTower.proj_append,Function.comp_apply] using hyU
  have hWUNew : (Wnew : Set B)⊆H.proj ⁻¹' (tangentChoice JP (H.proj (T.proj z))).1 :=
    fun y hy => (interior_subset hy).1
  have hmOld : ∀ V∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong JP)) H).E.take JP.E.length,
      ∀ y∈Wold,y∉V := by
    intro V hV y hy hyV
    change V∈origMembers (geoTransformAlong J P) H at hV
    obtain ⟨L,hL,hE⟩ := origMembers_emptyPrefix J P hP H
    rw [hE] at hV
    rcases List.mem_append.mp hV with hV | hV
    · exact (interior_subset hy).2.1 V hV hyV
    · rw [hL V hV] at hyV
      exact hyV
  have hmNew : ∀ V∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong JP)) H).E.take JP.E.length,
      ∀ y∈Wnew,y∉V := fun V hV y hy hyV => (interior_subset hy).2.1 V hV hyV
  have hCompare := hO H T hSource Wold Wnew hWUOld hWUNew hmOld hmNew
    hRDom hRTest hNew hNewTest ⟨z,hpOld⟩ ⟨z,hpNew⟩ rfl hxO hzSource k
  change Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 (P.append H) T z=
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) JP (lowerMarkedM JP) 0 H T z
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J (lowerMarkedM J)
      (s := 0) (T₀ := P.append H) (T₁ := T) (y := z) hpOld,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) JP (lowerMarkedM JP)
      (s := 0) (T₀ := H) (T₁ := T) (y := z) hpNew]
  exact congrArg (fun v : ValTy (k+1) => (v : WithTop (ValTy (k+1))))
    ((full_values_of_restrictEquiv hn _ _ hOld.isWellFormed hCoherent hEq (k+1) (restrict Wold T)
      ⟨z,hpOld⟩).trans hCompare)

end
end Hironaka.HironakaOriginalZeroEmptyPrefixHeadValues
