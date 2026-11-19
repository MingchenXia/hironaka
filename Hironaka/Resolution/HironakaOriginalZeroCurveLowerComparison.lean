/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveTangentChange
import Hironaka.Resolution.HironakaOriginalCurveLowerReferenceRebase
/-! Actual contact rebasing and genuine change of tangent direction compare
original zero-level curve lower values without canonical histories. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroCurveLowerComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower CoefficientIdealRestriction TangentDirectionAlong ContactIndependenceAlong
  StepOneValue StepOneValueMasked StepOneCompare StepOneMaskTower StepOneNearby StepOneRegime
  StepOneCanonicalTail StepOneLowerDomain RestrictEmptyTower CanonicalCentres
  HironakaOriginalCurveFullLocality HironakaOriginalCurveLowerReferenceRebase HironakaOriginalCurveTangentChange
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- Real current contact records and genuine same-endpoint gluing supply the
zero-level original numerical comparison; ordinary lower geometry is explicit. -/
theorem zero_curve_lower_value_rebase (hn : 0<n) (k : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (P : BlowupTower X A) (M : BlowupTower A B) (T : BlowupTower B Y)
    (hUpper : IsGeoTestTower (barMarked J) ((P.append M).append T))
    (y₀ : B) (hy₀ : y₀∈(geoTransformAlong (barMarked J) (P.append M)).cosupp)
    (hDom₀ : IsInvDomain 1 (lowerMarkedM J 0 (P.append M) y₀))
    (hTest₀ : IsGeoTestTower (lowerMarkedM J 0 (P.append M) y₀)
      (restrict (lowerMask J 0 (P.append M) y₀) T))
    (p : Y) (hpW : T.proj p∈lowerMask J 0 (P.append M) y₀)
    (hpcos : p∈(geoTransformAlong (barMarked J) ((P.append M).append T)).cosupp)
    (hp₁ : (M.append T).proj p∈lowerMask J 0 P ((M.append T).proj p))
    (hDom₁ : IsInvDomain 1 (lowerMarkedM J 0 P ((M.append T).proj p)))
    (hTest₁ : IsGeoTestTower (lowerMarkedM J 0 P ((M.append T).proj p))
      (restrict (lowerMask J 0 P ((M.append T).proj p)) (M.append T)))
    (hCos₁ : (⟨p,hp₁⟩ : openPreimage (M.append T) (lowerMask J 0 P ((M.append T).proj p)))∈
      (geoTransformAlong (lowerMarkedM J 0 P ((M.append T).proj p))
        (restrict (lowerMask J 0 P ((M.append T).proj p)) (M.append T))).cosupp)
    (hAvoid : CentresAvoid (lowerMask J 0 P ((M.append T).proj p)) M) :
    Seq.StepOneValueMasked.lowerValueL (invFamily hn (k+1)) J (lowerMarkedM J) 0 P (M.append T) p=
      (((invFamily hn (k+1)).inv (lowerMarkedM J 0 (P.append M) y₀)
        (restrict (lowerMask J 0 (P.append M) y₀) T) ⟨p,hpW⟩ : ValTy (k+1)) : WithTop (ValTy (k+1))) := by
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (k+1)) J _ hp₁]
  congr 1
  set W' := lowerMask J 0 P ((M.append T).proj p) with hW'
  set v := (tangentChoice J (P.proj ((M.append T).proj p))).2 with hvdef
  set Uv := (tangentChoice J (P.proj ((M.append T).proj p))).1 with hUvdef
  have hxUv : P.proj ((M.append T).proj p)∈Uv := (interior_subset hp₁).1
  have hv := tangentChoice_spec_of_mem J hxUv
  have hWU : (W' : Set A)⊆openPreimage P (⟨Uv,hv.isOpen⟩ : Opens X) :=
    fun q hq => (interior_subset hq).1
  have hPB := ((isGeoTestTower_append_iff _ _ T).mp hUpper).1
  obtain ⟨hTestB,hValB⟩ := curve_full_value_restrict_append hn W' _ hDom₁ M T hTest₁
  have hPoint : (M.append T).proj p=M.proj (T.proj p) := by rw [BlowupTower.proj_append];rfl
  have hq : p∈openPreimage T (openPreimage M W') := show M.proj (T.proj p)∈W' from hPoint ▸ hp₁
  obtain ⟨hCosB,hValB⟩ := hValB p hp₁ hq hCos₁
  rw [←hValB k]
  have e₁ : lowerMarkedM J 0 P ((M.append T).proj p)=contactKept J v P W' := rfl
  rw [e₁] at hDom₁ hTestB hCosB ⊢
  obtain ⟨hDomS,hTestS,_hCosS,hValS⟩ := contactKept_curve_full_rebase hn J hJ hd
    (⟨Uv,hv.isOpen⟩ : Opens X) hv P M hPB W' hWU hAvoid hDom₁ (restrict (openPreimage M W') T) hTestB
  rw [hValS ⟨p,hq⟩ hCosB k]
  obtain ⟨_hxU,hu⟩ := tangentChoice_spec J (exists_tangent_of_mem_cosupp J hJ hd hmax (P.append M) hPB hy₀)
  have hbase : (P.append M).proj (T.proj p)=P.proj ((M.append T).proj p) := by
    rw [BlowupTower.proj_append,BlowupTower.proj_append];rfl
  have hxU₁ : (P.append M).proj (T.proj p)∈(tangentChoice J ((P.append M).proj y₀)).1 :=
    (interior_subset hpW).1
  have hxU₂ : (P.append M).proj (T.proj p)∈Uv := hbase ▸ hxUv
  have hx : (P.append M).proj (T.proj p)∈J.cosupp := by
    have hBar := StepOneLowerDomain.isWellFormed_barMarked J hJ
    have hh := proj_mem_cosupp_of_mem_cosupp hBar.isClosedSubmanifold_N hBar.isCoherent _ hUpper hpcos
    rw [StepOneLowerDomain.cosupp_barMarked J hJ hd,BlowupTower.proj_append] at hh
    exact hh
  obtain ⟨O,hxO,hO⟩ := curve_full_contact_directions_on_opens hn J hJ.isCoherent
    hJ.isClosedSubmanifold_N hd hx hu hxU₁ hv hxU₂
  have hWU₁ : ((maskB J (P.append M) y₀ : Opens B) : Set B)⊆
      (P.append M).proj ⁻¹' (tangentChoice J ((P.append M).proj y₀)).1 :=
    fun q hq => (interior_subset hq).1
  have hWU₂ : ((openPreimage M W' : Opens B) : Set B)⊆(P.append M).proj ⁻¹' Uv := by
    intro q hq
    have hh := (interior_subset (show M.proj q∈W' from hq)).1
    show (P.append M).proj q∈Uv
    rw [BlowupTower.proj_append]
    exact hh
  have hmW : ∀ H∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) (P.append M)).E.take J.E.length,
      ∀ q∈maskB J (P.append M) y₀,q∉H := fun H hH q hq hqH => (interior_subset hq).2.1 H hH hqH
  have hmW' : ∀ H∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) (P.append M)).E.take J.E.length,
      ∀ q∈openPreimage M W',q∉H := by
    intro H hH q hq hqH
    have hH' : H∈origMembers J (P.append M) := hH
    rw [origMembers_append] at hH'
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH'
    have hh := MemberInterTowerAlong.strictAlong_subset_preimage M
      (isClosed_of_mem_origMembers J (fun H hH => hJ.isSNCDivisor.1 H hH) P H₀ hH₀) hqH
    exact (interior_subset (show M.proj q∈W' from hq)).2.1 H₀ hH₀ hh
  exact (hO (P.append M) T hUpper (maskB J (P.append M) y₀) (openPreimage M W')
    hWU₁ hWU₂ hmW hmW' hDom₀ hTest₀ hDomS hTestS ⟨p,hpW⟩ ⟨p,hq⟩ rfl hxO hpcos k).symm

end
end Hironaka.HironakaOriginalZeroCurveLowerComparison
