/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalIndependentSmoothLowerHistories
/-! Actual ORIGINAL member-avoiding zero contact masks have real lower TESTS
and WHOLE records along every original upper TEST, without lower canonicality. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroMaskChoiceTowers
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept ContactStageInvDomain
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain TangentDirectionAlong
  HomogenizedGlueingTower HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  StepOneTangentChange BlowupTowerIsomorphism BlowupTowerSplitIso ContactEquivalenceAlong
  HironakaStepOneZeroContactRemainderGlueing MaximalOrderStepOneB MarkedIdealTowerTransport
variable {n : ℕ} {X : CMfd.{u} n}

/-- Genuine original member avoidance supplies actual EMPTY positions before
true kept-parent transport, both lower TESTS and WHOLE endpoint/EVERY-head records. -/
theorem exists_original_zero_mask_choice_towers (K : MarkedIdeal n X)
    (hK : K.IsWellFormed) (hd : 1 ≤ K.d) (x : X) (hx : x ∈ K.cosupp)
    (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong K.N K.ideal K.d V v) (hxV : x ∈ V) :
    ∃ O : Opens X,x ∈ O ∧
      ∀ {D E : CMfd.{u} n} (T₀ : BlowupTower X D) (T₁ : BlowupTower D E),
        IsGeoTestTower K (T₀.append T₁) →
        ∀ (W W' : Opens D), (W : Set D) ⊆ T₀.proj ⁻¹' (U : Set X) →
          (W' : Set D) ⊆ T₀.proj ⁻¹' (V : Set X) →
          (∀ H ∈ origMembers K T₀,Disjoint (W : Set D) H) →
          (∀ H ∈ origMembers K T₀,Disjoint (W' : Set D) H) →
          ∀ (z : E),T₁.proj z ∈ W → T₁.proj z ∈ W' → T₀.proj (T₁.proj z) ∈ O →
            z ∈ (geoTransformAlong K (T₀.append T₁)).cosupp →
            ∃ (Vu Vv : Opens D) (hzu : T₁.proj z ∈ Vu) (hzv : T₁.proj z ∈ Vv)
              (ψ : CMfd.of (n := n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) Vu)
              (ξ : CMfd.of (n := n) (openPreimage T₁ Vv) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
                CMfd.of (n := n) (openPreimage T₁ Vu)),
              Vu ≤ W ∧ Vv ≤ W' ∧ IsTowerIso ψ (restrict Vv T₁) (restrict Vu T₁) ξ ∧
              ξ ⟨z,hzv⟩=⟨z,hzu⟩ ∧
              let A := contactMarkedKept K u T₀ Vu
              let B := contactMarkedKept K v T₀ Vv
              MarkedIdeal.pullback ψ A=B ∧
              IsClosedSubmanifold n A.N ∧ A.ideal.IsCoherent ∧
              IsClosedSubmanifold n B.N ∧ B.ideal.IsCoherent ∧
              IsGeoTestTower A (restrict Vu T₁) ∧ IsGeoTestTower B (restrict Vv T₁) ∧
              geoTransformAlong B (restrict Vv T₁)=MarkedIdeal.pullback ξ (geoTransformAlong A (restrict Vu T₁)) ∧
              ∀ j : ℕ,∃ ξj,
                IsTowerIso ψ (head (restrict Vv T₁) j) (head (restrict Vu T₁) j) ξj ∧
                IsTowerIso ξj (tail (restrict Vv T₁) j) (tail (restrict Vu T₁) j) ξ ∧
                geoTransformAlong B (head (restrict Vv T₁) j)=
                  MarkedIdeal.pullback ξj (geoTransformAlong A (head (restrict Vu T₁) j)) := by
  obtain ⟨O,hxO,hG⟩ := exists_tail_iso_opens (M := X) hK.isCoherent hK.isClosedSubmanifold_N
    hd hx hu hxU hv hxV
  have he := coeff_homAlong_wEquiv K hK.isClosedSubmanifold_N hK.isCoherent hd
  refine ⟨O,hxO,?_⟩
  intro D E T₀ T₁ hT W W' hWU hW'V hWE hW'E z hzW hzW' hzO hz
  have hBar : IsGeoTestTower (barMarked K) (T₀.append T₁) := (he.2 _).1.mpr hT
  have hEmpty := StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom K _ hBar
  have hzEmpty : z ∈ (geoTransformAlong (stepOneMarked K.N K.ideal K.d) (T₀.append T₁)).cosupp := by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked,(he.2 _).2 hBar]
    exact hz
  obtain ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuW,hVvW',hIso,hξ,hEmptyModel⟩ :=
    hG T₀ T₁ hEmpty W W' z hzW hzW' hzO hzEmpty
  have hModel : MarkedIdeal.pullback ψ (contactMarkedKept K u T₀ Vu)=contactMarkedKept K v T₀ Vv := by
    change MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → D) _)=
      MarkedIdeal.pullback (Subtype.val : Vv → D) _
    rw [pullback_val_restrictedCoeffHom_eq K T₀ u Vu
      (fun H hH y hy => Set.disjoint_left.mp (hWE H hH) (hVuW hy)),
      pullback_val_restrictedCoeffHom_eq K T₀ v Vv
        (fun H hH y hy => Set.disjoint_left.mp (hW'E H hH) (hVvW' hy)),
      pullback_replicate_empty,hEmptyModel]
  let A := contactMarkedKept K u T₀ Vu
  let B := contactMarkedKept K v T₀ Vv
  change MarkedIdeal.pullback ψ A=B at hModel
  have hHead := ((isGeoTestTower_append_iff K T₀ T₁).mp hT).1
  have hAN : IsClosedSubmanifold n A.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isClosedSubmanifold_N hK.isCoherent hd U hu T₀ hHead Vu (fun y hy => hWU (hVuW hy))
  have hBarHead := ((isGeoTestTower_append_iff (barMarked K) T₀ T₁).mp hBar).1
  have hAI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isCoherent hK.isClosedSubmanifold_N u T₀ hBarHead)
  have hBN : IsClosedSubmanifold n B.N := by
    rw [←hModel]
    exact (isClosedSubmanifold_preimage_iff ψ).mpr hAN
  have hBI : B.ideal.IsCoherent := by
    rw [←hModel]
    exact GermIdealPullbackCalculus.isCoherent_pullback ψ.contMDiff hAI
  have hAT : IsGeoTestTower A (restrict Vu T₁) :=
    (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K hK.isClosedSubmanifold_N
      hK.isCoherent hd U hu T₀ T₁ hBar Vu (fun y hy => hWU (hVuW hy))).1
  have hBT : IsGeoTestTower B (restrict Vv T₁) := by
    rw [←hModel]
    exact (IsTowerIso.isGeoTestTower_iff ψ hAN hAI hIso).mpr hAT
  have hEndpoint := IsTowerIso.geoTransformAlong_eq ψ hAN hAI hIso hAT
  rw [hModel] at hEndpoint
  refine ⟨Vu,Vv,hzu,hzv,ψ,ξ,hVuW,hVvW',hIso,hξ,hModel,hAN,hAI,hBN,hBI,hAT,hBT,hEndpoint,?_⟩
  intro j
  obtain ⟨ξj,hHeadIso,hTailIso⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso j
  have hHeadTest := ((isGeoTestTower_iff_head_tail A (restrict Vu T₁) j).mp hAT).1
  have hRecord := IsTowerIso.geoTransformAlong_eq ψ hAN hAI hHeadIso hHeadTest
  rw [hModel] at hRecord
  exact ⟨ξj,hHeadIso,hTailIso,hRecord⟩

end
end Hironaka.HironakaOriginalZeroMaskChoiceTowers
