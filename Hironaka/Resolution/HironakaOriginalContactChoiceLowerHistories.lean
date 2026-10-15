/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalIndependentSmoothContactChoices
/-! Real contact-choice tower isomorphisms produce literal lower TESTS and
ENTIRE controlled records at EVERY head of EVERY ORIGINAL upper test. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalContactChoiceLowerHistories
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
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem actual_kept_contact_remainder_padded (K : MarkedIdeal n X) (w : X → ℂ)
    (T : BlowupTower X Y) (O : Opens Y) :
    let A := contactMarkedKept ({K with E := []} : MarkedIdeal n X) w T O
    contactRemainderMarked (contactMarkedKept K w T O) K.E.length =
      contactRemainderMarked ({A with E := List.replicate K.E.length ∅ ++ A.E} : MarkedIdeal n O) K.E.length := by
  dsimp only
  rw [contactRemainderMarked_contactMarkedKept_emptyE]
  let A : MarkedIdeal n O := contactMarkedKept ({K with E := []} : MarkedIdeal n X) w T O
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change List.replicate K.E.length ∅ ++ A.E =
      List.replicate K.E.length ∅ ++ (List.replicate K.E.length ∅ ++ A.E).drop K.E.length
    simp
  · rfl
  · rfl


/-- ONE actual gluing BEFORE EVERY original split test produces the LITERAL
lower tests, genuine tower isomorphisms and ENTIRE endpoint/EVERY-head records. -/
theorem exists_original_test_contact_choice_lower_histories (K : MarkedIdeal n X)
    (hK : K.IsWellFormed) (hd : 1 ≤ K.d) (x : X) (hx : x ∈ K.cosupp)
    (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong K.N K.ideal K.d V v) (hxV : x ∈ V) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d u v,
      x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set X) ⊆ U ∩ V ∧ (G.cod : Set X) ⊆ U ∩ V ∧
      ∀ {D E : CMfd.{u} n} (T₀ : BlowupTower X D) (T₁ : BlowupTower D E),
        IsGeoTestTower K (T₀.append T₁) →
        ∃ Φ χ, IsGlueingLiftAlong G T₀ Φ ∧
        ∃ hχ : IsTowerIso Φ (restrict (openPreimage T₀ G.dom) T₁)
          (restrict (openPreimage T₀ G.cod) T₁) χ,
        let A0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) u T₀ (openPreimage T₀ G.cod)
        let B0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) v T₀ (openPreimage T₀ G.dom)
        MarkedIdeal.pullback Φ A0 = B0 ∧
        ∃ (hAN : IsClosedSubmanifold n A0.N) (hAI : A0.ideal.IsCoherent) (hdA : 1 ≤ A0.d),
        IsGeoTestTower A0 (restrict (openPreimage T₀ G.cod) T₁) ∧
        let A : MarkedIdeal n (openPreimage T₀ G.cod) :=
          {A0 with E := List.replicate K.E.length ∅ ++ A0.E}
        contactRemainderMarked (contactMarkedKept K u T₀ (openPreimage T₀ G.cod)) K.E.length =
          contactRemainderMarked A K.E.length ∧
        contactRemainderMarked (contactMarkedKept K v T₀ (openPreimage T₀ G.dom)) K.E.length =
          contactRemainderMarked (MarkedIdeal.pullback Φ A) K.E.length ∧
        let O := remainderOpen (X := CMfd.of (n := n) (openPreimage T₀ G.cod)) A hAN
        let O' := remainderOpen (X := CMfd.of (n := n) (openPreimage T₀ G.dom))
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
  obtain ⟨G,hxd,hxc,hdom,hcod,hglue⟩ := exists_contact_remainder_tail_glueing K
    hK.isClosedSubmanifold_N hK.isCoherent hd x hx U V hu hxU hv hxV
  have he := coeff_homAlong_wEquiv K hK.isClosedSubmanifold_N hK.isCoherent hd
  refine ⟨G,hxd,hxc,hdom,hcod,fun T₀ T₁ hT => ?_⟩
  have hBar : IsGeoTestTower (barMarked K) (T₀.append T₁) := (he.2 _).1.mpr hT
  have hEmpty := isGeoTestTower_stepOneMarked_of_coeffHom K (T₀.append T₁) hBar
  obtain ⟨Φ,χ,hL,hχ,hmodel,hAN,hAI,hdA,hAT,hrest⟩ := hglue T₀ T₁ hEmpty
  let A0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) u T₀ (openPreimage T₀ G.cod)
  let B0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) v T₀ (openPreimage T₀ G.dom)
  let A : MarkedIdeal n (openPreimage T₀ G.cod) := {A0 with E := List.replicate K.E.length ∅ ++ A0.E}
  have hpad : MarkedIdeal.pullback Φ A =
      ({B0 with E := List.replicate K.E.length ∅ ++ B0.E} : MarkedIdeal n (openPreimage T₀ G.dom)) := by
    rw [pullback_replicate_empty, hmodel]
  have hi := actual_kept_contact_remainder_padded K u T₀ (openPreimage T₀ G.cod)
  have hi' : contactRemainderMarked (contactMarkedKept K v T₀ (openPreimage T₀ G.dom)) K.E.length =
      contactRemainderMarked (MarkedIdeal.pullback Φ A) K.E.length := by
    rw [hpad]
    exact actual_kept_contact_remainder_padded K v T₀ (openPreimage T₀ G.dom)
  have hk : K.E.length ≤ A.E.length := by
    change K.E.length ≤ (List.replicate K.E.length ∅ ++ A0.E).length
    simp only [List.length_append, List.length_replicate]
    exact Nat.le_add_right _ _
  have hAk := empty_pad_isGeoTestTower (X := CMfd.of (n := n) (openPreimage T₀ G.cod))
    A0 K.E.length (restrict (openPreimage T₀ G.cod) T₁) hAT
  have hcalc := remainderOpen_test_tower_transport Φ A K.E.length hk hAN hAI hdA
    (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ hχ hAk
  have hpref := remainderOpen_prefix_transport Φ A K.E.length hk hAN hAI hdA
    (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ hχ hAk
  refine ⟨Φ, χ, hL, hχ, hmodel, hAN, hAI, hdA, hAT, hi, hi', ?_⟩
  refine ⟨hcalc.1,hcalc.2.1,hcalc.2.2.1,hcalc.2.2.2,hpref,fun p hp => ?_⟩
  apply hrest.2.2.2.2.2 p
  rw [cosupp_geoTransformAlong_stepOneMarked K (T₀.append T₁),(he.2 (T₀.append T₁)).2 hBar]
  exact hp

end
end Hironaka.HironakaOriginalContactChoiceLowerHistories
