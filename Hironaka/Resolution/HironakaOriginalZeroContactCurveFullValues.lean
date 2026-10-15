/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveValueNaturality
import Hironaka.Resolution.HironakaOriginalZeroMaskChoiceTowers
/-! Genuine ANY-original-TEST full lower values for independent zero-contact
choices in upper carrier bound two. No lower canonicality or value certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroContactCurveFullValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain
  TangentDirectionAlong ContactStageKept ContactStageInvDomain HomogenizedGlueingTower
  HironakaOriginalZeroMaskChoiceTowers HironakaOriginalAnyTestCurveValueNaturality CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X D E : CMfd.{u} n}

/-- TRUE computed zero-mask containment supplies original-boundary and
codimension-one avoidance BEFORE the actual contact DOMAIN1 is constructed. -/
theorem actual_zero_mask_contact_curve_domain (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong M.N M.ideal M.d U u)
    (H : BlowupTower X D) (hH : IsGeoTestTower (barMarked M) H) (p : D)
    (W : Opens D) (hWU : (W : Set D) ⊆ openPreimage H U) (hWM : W≤maskB M H p) :
    IsInvDomain 1 (contactMarkedKept M u H W) := by
  have hD := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le M hM.isWellFormed
    hM.one_le_d hM.dimLE U hu H hH W hWU
    (fun y hy _ => (interior_subset (hWM hy)).2.2)
    (fun F hF y hy _ => (interior_subset (hWM hy)).2.1 F hF)
  exact hD

/-- ONLY original DOMAIN2/maxorder/two real tangent choices supply ONE
neighborhood before ANY original split history; real lower DOMAIN1/TESTs and
actual point-fixing history isomorphism precede ALL-depth genuine FULL values. -/
theorem exists_original_zero_contact_curve_full_values (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (x : X) (hx : x ∈ M.cosupp)
    (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong M.N M.ideal M.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong M.N M.ideal M.d V v) (hxV : x ∈ V) :
    ∃ O : Opens X,x ∈ O ∧
      ∀ {D E : CMfd.{u} n} (H : BlowupTower X D) (S : BlowupTower D E),
        IsGeoTestTower M (H.append S) → ∀ z : E,
          z ∈ (geoTransformAlong M (H.append S)).cosupp →
          ¬IsSpecial M H (S.proj z) → level M H (S.proj z)=0 → H.proj (S.proj z) ∈ O →
          ∃ (Vu Vv : Opens D) (hzu : S.proj z ∈ Vu) (hzv : S.proj z ∈ Vv)
            (ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) Vu)
            (ξ : CMfd.of (n := n) (openPreimage S Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage S Vu)),
            Vu≤maskB M H (S.proj z) ∧ Vv≤maskB M H (S.proj z) ∧
            IsTowerIso ψ (restrict Vv S) (restrict Vu S) ξ ∧ ξ ⟨z,hzv⟩=⟨z,hzu⟩ ∧
            let A := contactMarkedKept M u H Vu
            let B := contactMarkedKept M v H Vv
            IsInvDomain 1 A ∧ IsInvDomain 1 B ∧ MarkedIdeal.pullback ψ A=B ∧
            IsGeoTestTower A (restrict Vu S) ∧ IsGeoTestTower B (restrict Vv S) ∧
            ∀ k : ℕ,(invFamily hn (k+1)).inv B (restrict Vv S) ⟨z,hzv⟩=
              (invFamily hn (k+1)).inv A (restrict Vu S) ⟨z,hzu⟩ := by
  obtain ⟨G,hxG,hG⟩ := exists_original_zero_mask_choice_towers M hM.isWellFormed hM.one_le_d x hx U V hu hxU hv hxV
  let O := G ⊓ U ⊓ V
  refine ⟨O,⟨⟨hxG,hxU⟩,hxV⟩,?_⟩
  intro D E H S hT z hz hns hl hzO
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) (H.append S) := (he.2 _).1.mpr hT
  have hzBar : z ∈ (geoTransformAlong (barMarked M) (H.append S)).cosupp := by rw [(he.2 _).2 hBar];exact hz
  obtain ⟨hHead,hTail⟩ := (isGeoTestTower_append_iff (barMarked M) H S).mp hBar
  have hCurrent := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked M hM.isWellFormed) H hHead
  have hHeadCos : S.proj z ∈ (geoTransformAlong (barMarked M) H).cosupp := by
    apply proj_mem_cosupp_of_mem_cosupp hCurrent.isClosedSubmanifold_N hCurrent.isCoherent S hTail
    rw [←geoTransformAlong_append]
    exact hzBar
  have hpMask : S.proj z ∈ maskB M H (S.proj z) :=
    mem_maskB M hM.isWellFormed hM.one_le_d hmax H hHead hHeadCos hl (fun hZ => hns (Or.inl ⟨hl,hZ⟩))
  let W := maskB M H (S.proj z) ⊓ openPreimage H U
  let W' := maskB M H (S.proj z) ⊓ openPreimage H V
  have hzW : S.proj z ∈ W := ⟨hpMask,hzO.1.2⟩
  have hzW' : S.proj z ∈ W' := ⟨hpMask,hzO.2⟩
  have hWU : (W : Set D) ⊆ H.proj ⁻¹' (U : Set X) := fun _ hy => hy.2
  have hW'V : (W' : Set D) ⊆ H.proj ⁻¹' (V : Set X) := fun _ hy => hy.2
  have hWE : ∀ F ∈ origMembers M H,Disjoint (W : Set D) F := by
    intro F hF
    exact Set.disjoint_left.mpr fun y hy hyF => (interior_subset hy.1).2.1 F hF hyF
  have hW'E : ∀ F ∈ origMembers M H,Disjoint (W' : Set D) F := by
    intro F hF
    exact Set.disjoint_left.mpr fun y hy hyF => (interior_subset hy.1).2.1 F hF hyF
  obtain ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuW,hVvW',hIso,hξ,hModel,_hAN,_hAI,_hBN,_hBI,hAT,hBT,_hEndpoint,_hHeads⟩ :=
    hG H S hT W W' hWU hW'V hWE hW'E z hzW hzW' hzO.1.1 hz
  let A := contactMarkedKept M u H Vu
  let B := contactMarkedKept M v H Vv
  change MarkedIdeal.pullback ψ A=B at hModel
  have hVuMask : Vu≤maskB M H (S.proj z) := fun _ hy => (hVuW hy).1
  have hVvMask : Vv≤maskB M H (S.proj z) := fun _ hy => (hVvW' hy).1
  have hAU : (Vu : Set D) ⊆ openPreimage H U := fun _ hy => (hVuW hy).2
  have hBV : (Vv : Set D) ⊆ openPreimage H V := fun _ hy => (hVvW' hy).2
  have hAD : IsInvDomain 1 A := actual_zero_mask_contact_curve_domain M hM U hu H hHead (S.proj z) Vu hAU hVuMask
  have hBD : IsInvDomain 1 B := actual_zero_mask_contact_curve_domain M hM V hv H hHead (S.proj z) Vv hBV hVvMask
  have hzA : (⟨z,hzu⟩ : openPreimage S Vu) ∈ (geoTransformAlong A (restrict Vu S)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le M hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent hM.one_le_d U hu H S hBar Vu hAU).2]
    exact hzBar
  refine ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuMask,hVvMask,hIso,hξ,hAD,hBD,hModel,hAT,hBT,?_⟩
  intro k
  have hPoint : ξ (⟨z,hzv⟩ : openPreimage S Vv) ∈ (geoTransformAlong A (restrict Vu S)).cosupp := by
    rw [hξ]
    exact hzA
  have hValue := original_curve_any_test_full_value_isTowerIso hn k ψ A hAD hIso hAT ⟨z,hzv⟩ hPoint
  rw [hModel,hξ] at hValue
  exact hValue

end
end Hironaka.HironakaOriginalZeroContactCurveFullValues
