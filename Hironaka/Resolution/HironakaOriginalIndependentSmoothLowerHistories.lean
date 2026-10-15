/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalContactChoiceLowerHistories
/-! Real contact-choice tower isomorphisms produce literal lower TESTS and
ENTIRE controlled records at EVERY head of EVERY ORIGINAL upper test. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalIndependentSmoothLowerHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaStepOneZeroContactRemainderGlueing HironakaStepOneZeroContactRemainderTailGlueing
  BlowupTowerIsomorphism StepOneTangentChange BlowupTowerSplitIso
  ContactStageInvDomain ContactStageKept ContactIndependenceAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  NormalCrossings NormalCrossingsComparison DropMembers
  CoefficientIdealRestriction TangentDirectionAlong ContactEquivalenceAlong MaximalOrderStepOneB
  StepOneValue StepOneLowerDomain CanonicalCentres StepOneRegime
open HironakaOriginalIndependentSmoothContactChoices HironakaOriginalContactChoiceLowerHistories
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}

/-- ONLY original smooth inputs construct independently chosen source lower
histories, genuine literal nested TESTS and ENTIRE endpoint/EVERY-head records. -/
theorem exists_original_smooth_independent_contact_lower_histories :
    ∀ {f : Y → X}
    (_hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (_hM : IsInvDomain k M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (x : Y) (_hx : f x ∈ M.cosupp),
    let K := markedPullback (m := m) f M
    let u := (tangentChoice M (f x)).2 ∘ f
    let v := (tangentChoice K x).2
    ∃ U : Opens X,(U : Set X)=(tangentChoice M (f x)).1 ∧ f x ∈ U ∧
      ∃ V : Opens Y,(V : Set Y)=(tangentChoice K x).1 ∧ x ∈ V ∧
        let W : Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage _hf.contMDiff.continuous⟩
        IsTangentDirectionAlong M.N M.ideal M.d U (tangentChoice M (f x)).2 ∧
        IsTangentDirectionAlong K.N K.ideal K.d W u ∧
        IsTangentDirectionAlong K.N K.ideal K.d V v ∧
        ∃ G : GlueingDataAlong K.N K.ideal K.d u v,
          x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set Y) ⊆ W ∩ V ∧ (G.cod : Set Y) ⊆ W ∩ V ∧
      ∀ {D E : CMfd.{u} m} (T₀ : BlowupTower Y D) (T₁ : BlowupTower D E),
        IsGeoTestTower K (T₀.append T₁) →
        ∃ Φ χ, IsGlueingLiftAlong G T₀ Φ ∧
        ∃ hχ : IsTowerIso Φ (restrict (openPreimage T₀ G.dom) T₁)
          (restrict (openPreimage T₀ G.cod) T₁) χ,
        let A0 := contactMarkedKept ({K with E := []} : MarkedIdeal m Y) u T₀ (openPreimage T₀ G.cod)
        let B0 := contactMarkedKept ({K with E := []} : MarkedIdeal m Y) v T₀ (openPreimage T₀ G.dom)
        MarkedIdeal.pullback Φ A0 = B0 ∧
        ∃ (hAN : IsClosedSubmanifold m A0.N) (hAI : A0.ideal.IsCoherent) (hdA : 1 ≤ A0.d),
        IsGeoTestTower A0 (restrict (openPreimage T₀ G.cod) T₁) ∧
        let A : MarkedIdeal m (openPreimage T₀ G.cod) :=
          {A0 with E := List.replicate K.E.length ∅ ++ A0.E}
        contactRemainderMarked (contactMarkedKept K u T₀ (openPreimage T₀ G.cod)) K.E.length =
          contactRemainderMarked A K.E.length ∧
        contactRemainderMarked (contactMarkedKept K v T₀ (openPreimage T₀ G.dom)) K.E.length =
          contactRemainderMarked (MarkedIdeal.pullback Φ A) K.E.length ∧
        let O := remainderOpen (X := CMfd.of (n := m) (openPreimage T₀ G.cod)) A hAN
        let O' := remainderOpen (X := CMfd.of (n := m) (openPreimage T₀ G.dom))
          (MarkedIdeal.pullback Φ A) ((isClosedSubmanifold_preimage_iff Φ).mpr hAN)
        let hO := mem_remainderOpen_pullback_diffeo_iff Φ A hAN hAI hdA
        let Ψ := diffeoOpens Φ O' O hO
        let T := restrict (openPreimage T₀ G.cod) T₁
        let T' := restrict (openPreimage T₀ G.dom) T₁
        let χO := diffeoOpens χ (openPreimage T' O') (openPreimage T O)
          (isTowerIso_mem_openPreimage_iff hχ hO)
        let R := MarkedIdeal.pullback (Subtype.val : O → openPreimage T₀ G.cod) (contactRemainderMarked A K.E.length)
        let R' := MarkedIdeal.pullback (Subtype.val : O' → openPreimage T₀ G.dom)
          (contactRemainderMarked (MarkedIdeal.pullback Φ A) K.E.length)
        IsTowerIso Ψ (restrict O' T') (restrict O T) χO ∧
        IsGeoTestTower R (restrict O T) ∧ IsGeoTestTower R' (restrict O' T') ∧
        geoTransformAlong R' (restrict O' T') = MarkedIdeal.pullback χO (geoTransformAlong R (restrict O T)) ∧
        (∀ j : ℕ, ∃ χj,
          IsTowerIso Ψ (head (restrict O' T') j) (head (restrict O T) j) χj ∧
          IsTowerIso χj (tail (restrict O' T') j) (tail (restrict O T) j) χO ∧
          geoTransformAlong R' (head (restrict O' T') j) =
            MarkedIdeal.pullback χj (geoTransformAlong R (head (restrict O T) j))) ∧
        ∀ p : openPreimage T₁ (openPreimage T₀ G.dom),
          (p : E) ∈ (geoTransformAlong K (T₀.append T₁)).cosupp →
            (χ p : E) = p := by
  intro f hf M hM hmax x hx
  obtain ⟨U,hU,hxU,V,hV,hxV,hu,hPull,hv,_hCurrent⟩ :=
    exists_original_smooth_independent_contact_glueing hf M hM hmax x hx
  let K := markedPullback (m := m) f M
  let W : Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩
  have hK := isInvDomain_markedPullback_submersion hf M hM
  have hxK : x ∈ K.cosupp := by
    change x ∈ cosupport m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal) M.d
    rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hf hM.isWellFormed.isCoherent]
    exact hx
  refine ⟨U,hU,hxU,V,hV,hxV,hu,hPull,hv,?_⟩
  exact exists_original_test_contact_choice_lower_histories K hK.isWellFormed hK.one_le_d
    x hxK W V hPull hxU hv hxV

end
end Hironaka.HironakaOriginalIndependentSmoothLowerHistories
