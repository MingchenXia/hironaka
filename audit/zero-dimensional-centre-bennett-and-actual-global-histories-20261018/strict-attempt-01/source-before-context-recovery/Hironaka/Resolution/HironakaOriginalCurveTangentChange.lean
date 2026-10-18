/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveLocalReferenceComparison
import Hironaka.Invariant.StepOneTangentChange
/-! Genuine contact-gluing lifts compare ORIGINAL curve FULL values on actual
TESTs, without canonicality or numerical-comparison certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurveTangentChange
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen CanonicalCentres
  BlowupTowerIsomorphism MaxLocusLocal StepOneTangentChange
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  CoefficientIdealRestriction TangentDirectionAlong ContactIndependenceAlong
  HironakaOriginalCurveFullLocality HironakaOriginalCurveLocalReferenceComparison
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual local domains and TESTs precede genuine tail-isomorphism comparison. -/
theorem local_curve_full_tail_iso (hn : 0<n) (k : ℕ)
    {Nu Nv : MarkedIdeal n Y} (hcu : Nu.ideal.IsCoherent) (hcv : Nv.ideal.IsCoherent)
    {W W' Vu Vv : Opens Y} (hVuW : Vu≤W) (hVvW' : Vv≤W') (T : BlowupTower Y Z)
    (hDu : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W → Y) Nu))
    (hTu : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y) Nu) (restrict W T))
    (hDv : IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : W' → Y) Nv))
    (hTv : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W' → Y) Nv) (restrict W' T))
    {ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) Vu}
    {ξ : CMfd.of (n := n) (openPreimage T Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T Vu)}
    (hI : IsTowerIso ψ (restrict Vv T) (restrict Vu T) ξ)
    (hRecord : MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → Y) Nu)=
      MarkedIdeal.pullback (Subtype.val : Vv → Y) Nv)
    (z : Z) (hzu : T.proj z∈Vu) (hzv : T.proj z∈Vv)
    (hξ : ξ ⟨z,hzv⟩=⟨z,hzu⟩)
    (hCosu : (⟨z,hzu⟩ : openPreimage T Vu)∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vu → Y) Nu) (restrict Vu T)).cosupp)
    (hCosv : (⟨z,hzv⟩ : openPreimage T Vv)∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Vv → Y) Nv) (restrict Vv T)).cosupp) :
    (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : W → Y) Nu) (restrict W T) ⟨z,hVuW hzu⟩=
      (invFamily hn (k+1)).inv (MarkedIdeal.pullback (Subtype.val : W' → Y) Nv) (restrict W' T) ⟨z,hVvW' hzv⟩ := by
  obtain ⟨hDVu,hTVu,_hCosU,hValU⟩ := local_curve_full_nested_open hn Nu hcu hVuW hDu T hTu
  obtain ⟨_hDVv,_hTVv,_hCosV,hValV⟩ := local_curve_full_nested_open hn Nv hcv hVvW' hDv T hTv
  have h₂ := curve_full_value_of_towerIso hn k _ hDVu _ hTVu hI ⟨z,hzv⟩ (by rw [hξ];exact hCosu)
  rw [hξ,hRecord] at h₂
  exact (hValU ⟨z,hzu⟩ hCosu k).symm.trans (h₂.symm.trans (hValV ⟨z,hzv⟩ hCosv k))

/-- Genuine original tangent gluing, including every kept ordered boundary
member, supplies numerical comparison on actual local curve TESTs. -/
theorem curve_full_contact_directions_on_opens (hn : 0<n) (J : MarkedIdeal n X)
    (hJ : J.ideal.IsCoherent) (hN : IsClosedSubmanifold n J.N) (hd : 1≤J.d)
    {x : X} (hx : x∈cosupport n J.N J.ideal J.d) {u v : X → ℂ} {U₁ U₂ : Set X}
    (hu : IsTangentDirectionAlong J.N J.ideal J.d U₁ u) (hxU₁ : x∈U₁)
    (hv : IsTangentDirectionAlong J.N J.ideal J.d U₂ v) (hxU₂ : x∈U₂) :
    ∃ O : Opens X,x∈O ∧ ∀ {Y Z : CMfd.{u} n} (P : BlowupTower X Y) (T : BlowupTower Y Z),
      IsGeoTestTower (coeffMarkedAlong (homMarkedAlong J)) (P.append T) →
      ∀ (W W' : Opens Y),(W : Set Y)⊆P.proj ⁻¹' U₁ → (W' : Set Y)⊆P.proj ⁻¹' U₂ →
      (∀ H∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) P).E.take J.E.length,
        ∀ y∈W,y∉H) →
      (∀ H∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) P).E.take J.E.length,
        ∀ y∈W',y∉H) →
      IsInvDomain 1 (StepOneCompare.contactKept J u P W) →
      IsGeoTestTower (StepOneCompare.contactKept J u P W) (restrict W T) →
      IsInvDomain 1 (StepOneCompare.contactKept J v P W') →
      IsGeoTestTower (StepOneCompare.contactKept J v P W') (restrict W' T) →
      ∀ (p : openPreimage T W) (q : openPreimage T W'),p.val=q.val →
        P.proj (T.proj p.val)∈O →
        p.val∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) (P.append T)).cosupp →
        ∀ k : ℕ,(invFamily hn (k+1)).inv (StepOneCompare.contactKept J u P W) (restrict W T) p=
          (invFamily hn (k+1)).inv (StepOneCompare.contactKept J v P W') (restrict W' T) q := by
  obtain ⟨O,hxO,hO⟩ := exists_tail_iso_opens (M := X) hJ hN hd hx hu hxU₁ hv hxU₂
  refine ⟨O,hxO,?_⟩
  intro Y Z P T hT W W' hWU hW'U hmW hmW' hDu hTu hDv hTv p q hpq hpO hpcos k
  have hT' : IsGeoTestTower (MaximalOrderStepOneB.stepOneMarked J.N J.ideal J.d) (P.append T) :=
    StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom J _ hT
  have hpcos' : p.val∈(geoTransformAlong (MaximalOrderStepOneB.stepOneMarked J.N J.ideal J.d)
      (P.append T)).cosupp := by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked]
    exact hpcos
  have hzW' : T.proj p.val∈W' := by rw [hpq];exact q.property
  obtain ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuW,hVvW',hI,hξ,hψS⟩ :=
    hO P T hT' W W' p.val p.property hzW' hpO hpcos'
  have hP := ((isGeoTestTower_append_iff _ P T).mp hT).1
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong J)).N := hN
  have hJC : (coeffMarkedAlong (homMarkedAlong J)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hJ hN) hN
  obtain ⟨hNT,hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJC P hP
  have hRecord : MarkedIdeal.pullback ψ (StepOneCompare.contactKept J u P Vu)=
      StepOneCompare.contactKept J v P Vv := by
    dsimp only [StepOneCompare.contactKept,StepOneValue.barMarked]
    rw [pullback_val_restrictedCoeffHom_eq J P u Vu (fun H hH y hy => hmW H hH y (hVuW hy)),
      pullback_val_restrictedCoeffHom_eq J P v Vv (fun H hH y hy => hmW' H hH y (hVvW' hy)),
      pullback_replicate_empty,hψS]
  have hCosu : (⟨p.val,hzu⟩ : openPreimage T Vu)∈
      (geoTransformAlong (StepOneCompare.contactKept J u P Vu) (restrict Vu T)).cosupp := by
    dsimp only [StepOneCompare.contactKept,StepOneValue.barMarked]
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J hN hJ hd ⟨U₁,hu.isOpen⟩ hu P T hT Vu
      (fun y hy => hWU (hVuW hy))).2]
    exact hpcos
  have hCosv : (⟨p.val,hzv⟩ : openPreimage T Vv)∈
      (geoTransformAlong (StepOneCompare.contactKept J v P Vv) (restrict Vv T)).cosupp := by
    dsimp only [StepOneCompare.contactKept,StepOneValue.barMarked]
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le J hN hJ hd ⟨U₂,hv.isOpen⟩ hv P T hT Vv
      (fun y hy => hW'U (hVvW' hy))).2]
    exact hpcos
  have key := local_curve_full_tail_iso hn k
    (Nu := withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) P))
      (strictAlong P (J.N∩{x | u x=0})))
    (Nv := withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) P))
      (strictAlong P (J.N∩{x | v x=0})))
    (isCoherent_coeffMarkedAlong hcT hNT) (isCoherent_coeffMarkedAlong hcT hNT)
    hVuW hVvW' T hDu hTu hDv hTv hI hRecord p.val hzu hzv hξ hCosu hCosv
  have hp : (⟨p.val,hVuW hzu⟩ : openPreimage T W)=p := rfl
  have hq : (⟨p.val,hVvW' hzv⟩ : openPreimage T W')=q := Subtype.ext hpq
  rw [hp,hq] at key
  exact key

end
end Hironaka.HironakaOriginalCurveTangentChange
