/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalActualSmoothLowerHistory
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderTailGlueing

/-! Actual transported and independently selected smooth source contacts compare
on EVERY ORIGINAL test, using ENTIRE kept-position remainders. Raw original
boundary members are not asserted to be preserved by the actual gluing. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalIndependentSmoothContactChoices
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain TangentDirectionAlong
  HomogenizedGlueingTower HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderGlueing
  HironakaSmoothSubmersionTangentContact HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeRestriction
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}

/-- A real gluing chosen BEFORE EVERY original test compares the whole actual
kept-position remainders and fixes the actual ORIGINAL transformed cosupport. -/
theorem exists_original_test_contact_choice_glueing (K : MarkedIdeal n X)
    (hK : K.IsWellFormed) (hd : 1 ≤ K.d) (x : X) (hx : x ∈ K.cosupp)
    (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong K.N K.ideal K.d V v) (hxV : x ∈ V) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d u v,
      x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set X) ⊆ U ∩ V ∧ (G.cod : Set X) ⊆ U ∩ V ∧
      ∀ {D : CMfd.{u} n} (T : BlowupTower X D), IsGeoTestTower K T →
        ∃ Φ, IsGlueingLiftAlong G T Φ ∧
          MarkedIdeal.pullback Φ
            (contactRemainderMarked (contactMarkedKept K u T (openPreimage T G.cod)) K.E.length) =
              contactRemainderMarked (contactMarkedKept K v T (openPreimage T G.dom)) K.E.length ∧
          ∀ p : openPreimage T G.dom,
            (p : D) ∈ (geoTransformAlong K T).cosupp → (Φ p : D) = p := by
  obtain ⟨G,hxd,hxc,hdom,hcod,hglue⟩ := exists_contact_remainder_glueing K
    hK.isClosedSubmanifold_N hK.isCoherent hd x hx U V hu hxU hv hxV
  have he := coeff_homAlong_wEquiv K hK.isClosedSubmanifold_N hK.isCoherent hd
  refine ⟨G,hxd,hxc,hdom,hcod,fun T hT => ?_⟩
  have hBar : IsGeoTestTower (barMarked K) T := (he.2 T).1.mpr hT
  have hEmpty := StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom K T hBar
  obtain ⟨Φ,hLift,⟨_hModel,hPad⟩,hFix⟩ := hglue T hEmpty
  refine ⟨Φ,hLift,?_,fun p hp => ?_⟩
  · rw [contactRemainderMarked_contactMarkedKept_emptyE,
      contactRemainderMarked_contactMarkedKept_emptyE]
    exact hPad K.E.length
  · apply hFix p
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked K T,(he.2 T).2 hBar]
    exact hp

/-- ONLY original target data and the actual smooth map internally construct
both independent genuine source directions before comparing EVERY source test. -/
theorem exists_original_smooth_independent_contact_glueing :
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
          ∀ {D : CMfd.{u} m} (T : BlowupTower Y D), IsGeoTestTower K T →
            ∃ Φ, IsGlueingLiftAlong G T Φ ∧
              MarkedIdeal.pullback Φ
                (contactRemainderMarked (contactMarkedKept K u T (openPreimage T G.cod)) K.E.length) =
                  contactRemainderMarked (contactMarkedKept K v T (openPreimage T G.dom)) K.E.length ∧
              ∀ p : openPreimage T G.dom,
                (p : D) ∈ (geoTransformAlong K T).cosupp → (Φ p : D) = p := by
  intro f hf M hM hmax x hx
  let K := markedPullback (m := m) f M
  have hK := isInvDomain_markedPullback_submersion hf M hM
  have hxK : x ∈ K.cosupp := by
    change x ∈ GermIdealOrder.cosupport m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal) M.d
    rw [HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hf hM.isWellFormed.isCoherent]
    exact hx
  have hmaxK : IsMaximalOrderAlong K.N K.ideal K.d :=
    isMaximalOrderAlong_preimage hf hM.isWellFormed.isCoherent M.N M.d hmax
  have heM := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hxBarM : f x ∈ (geoTransformAlong (barMarked M) .refl).cosupp := by
    rw [(heM.2 .refl).2 trivial]
    exact hx
  obtain ⟨hxU,hu⟩ := tangentChoice_spec M (exists_tangent_of_mem_cosupp M
    hM.isWellFormed hM.one_le_d hmax .refl trivial hxBarM)
  have heK := coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d
  have hxBarK : x ∈ (geoTransformAlong (barMarked K) .refl).cosupp := by
    rw [(heK.2 .refl).2 trivial]
    exact hxK
  obtain ⟨hxV,hv⟩ := tangentChoice_spec K (exists_tangent_of_mem_cosupp K
    hK.isWellFormed hK.one_le_d hmaxK .refl trivial hxBarK)
  let U : Opens X := ⟨_,hu.isOpen⟩
  let V : Opens Y := ⟨_,hv.isOpen⟩
  let W : Opens Y := ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩
  have hPull : IsTangentDirectionAlong K.N K.ideal K.d W ((tangentChoice M (f x)).2 ∘ f) :=
    isTangentDirectionAlong_preimage hf hM.isWellFormed.isCoherent
      hM.isWellFormed.isClosedSubmanifold_N hu
  refine ⟨U,rfl,hxU,V,rfl,hxV,hu,hPull,hv,?_⟩
  exact exists_original_test_contact_choice_glueing K hK.isWellFormed hK.one_le_d
    x hxK W V hPull hxU hv hxV

end
end Hironaka.HironakaOriginalIndependentSmoothContactChoices
