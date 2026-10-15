/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveEtaleValues
import Hironaka.Resolution.HironakaOriginalActualSmoothZeroMaskHistories
/-! Actual computed COMMON zero-contact full curve values on ANY original
TEST; the true global endpoint coordinate law is retained BEFORE values. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalZeroCommonCurveValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  RelativePrincipalizationSpan CanonicalCentres HomogenizedIdealAlong HomogenizedIdealAlongTower
  ContactStageKept StepOneValue StepOneLowerDomain StepOneValueMasked StepOneRegime TangentDirectionAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOriginalZeroContactLower HironakaOriginalActualSmoothZeroMaskHistories
  HironakaOriginalAnyTestCurveEtaleValues
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y D D' : CMfd.{u} n}

/-- ONLY original ANYTEST zero data supply the ACTUAL large target mask and
common contact, genuine endpoint SAME-g identity BEFORE ALL-depth full values. -/
theorem actual_original_zero_common_curve_full_values (hn : 0<n)
    {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (hT : IsGeoTestTower M T)
    (z : D') (hy : g z ∈ (geoTransformAlong M T).cosupp)
    (hns : ¬IsSpecial M T (g z)) (hl : level M T (g z)=0) :
    let r := regimeRun (stepRegime M 0) T (g z)
    let w := (tangentChoice M (T.proj (g z))).2
    let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
    let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
    let L := restrict U (tail T r)
    ∃ (hp : (tail T r).proj (g z) ∈ U)
      (a : (split Q r).1 → (split T r).1) (V : Opens (split Q r).1)
      (hp' : (tail Q r).proj z ∈ V)
      (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
      let J' := contactMarkedKept (markedPullback (m := n) f M) (w ∘ f) (head Q r) V
      let L' := restrict V (tail Q r)
      IsActualTowerPullback f (head Q r) (head T r) a ∧
      (V : Set (split Q r).1)=a ⁻¹' (U : Set (split T r).1) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ p ∧
      markedPullback (m := n) p J=J' ∧ IsActualTowerPullback p L' L q ∧
      q (⟨z,hp'⟩ : openPreimage (tail Q r) V)=(⟨g z,hp⟩ : openPreimage (tail T r) U) ∧
      IsInvDomain 1 J ∧ IsGeoTestTower J L ∧ (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J L).cosupp ∧
      IsInvDomain 1 J' ∧ IsGeoTestTower J' L' ∧
      (geoTransformAlong J' L').cosupp=q ⁻¹' (geoTransformAlong J L).cosupp ∧
      (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp ∧
      ∀ k : ℕ,(invFamily hn (k+1)).inv J' L' ⟨z,hp'⟩=(invFamily hn (k+1)).inv J L ⟨g z,hp⟩ := by
  obtain ⟨hp,hJ,hJT,_hCos,hyJ,_hNext⟩ :=
    actual_original_test_zero_mask_history (k := 0) hn M hM hmax T hT (g z) hy hns hl
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 T).1.mpr hT
  have hyBar : g z ∈ (geoTransformAlong (barMarked M) T).cosupp := by
    rw [(he.2 T).2 hBar]
    exact hy
  obtain ⟨_hRun,_hu,a,V,p,q,hh,_hs,hV,hp',hpSmooth,hqcoord,_hWU,_hWE,hRecord,hR⟩ :=
    original_zero_common_contact_mask_geometry h M hM.isWellFormed hM.one_le_d hmax hBar z hyBar hl hns
  let r := regimeRun (stepRegime M 0) T (g z)
  let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
  let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
  let L := restrict U (tail T r)
  let J' := contactMarkedKept (markedPullback (m := n) f M)
    ((tangentChoice M (T.proj (g z))).2 ∘ f) (head Q r) V
  let L' := restrict V (tail Q r)
  change markedPullback (m := n) p J=J' at hRecord
  change IsActualTowerPullback p L' L q at hR
  have hPoint : q (⟨z,hp'⟩ : openPreimage (tail Q r) V)=(⟨g z,hp⟩ : openPreimage (tail T r) U) :=
    Subtype.ext (hqcoord (⟨z,hp'⟩ : openPreimage (tail Q r) V))
  obtain ⟨hSource,hSourceT,hSourceCos,hValues⟩ :=
    actual_original_curve_full_values_etale hpSmooth hn J hJ hR hJT
  rw [hRecord] at hSource hSourceT hSourceCos hValues
  have hpTarget : q (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J L).cosupp := by
    rw [hPoint]
    exact hyJ
  have hpSource : (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp := by
    rw [hSourceCos]
    exact hpTarget
  refine ⟨hp,a,V,hp',p,q,hh,hV,hpSmooth,hRecord,hR,hPoint,hJ,hJT,hyJ,hSource,hSourceT,hSourceCos,hpSource,?_⟩
  intro k
  have hv := hValues (⟨z,hp'⟩ : openPreimage (tail Q r) V) hpTarget k
  rw [hPoint] at hv
  exact hv

/-- ONLY original inputs construct ONE actual source history before every
true computed target/common lower domain, TEST, endpoint law and full value. -/
theorem exists_original_zero_common_curve_values {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} n) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := n) f M) Q ∧
      ∀ z : D',g z ∈ (geoTransformAlong M T).cosupp → ¬IsSpecial M T (g z) → level M T (g z)=0 →
        let r := regimeRun (stepRegime M 0) T (g z)
        let w := (tangentChoice M (T.proj (g z))).2
        let U := lowerMask M 0 (head T r) ((tail T r).proj (g z))
        let J := lowerMarkedM M 0 (head T r) ((tail T r).proj (g z))
        let L := restrict U (tail T r)
        ∃ (hp : (tail T r).proj (g z) ∈ U)
          (a : (split Q r).1 → (split T r).1) (V : Opens (split Q r).1)
          (hp' : (tail Q r).proj z ∈ V)
          (p : V → U) (q : openPreimage (tail Q r) V → openPreimage (tail T r) U),
          let J' := contactMarkedKept (markedPullback (m := n) f M) (w ∘ f) (head Q r) V
          let L' := restrict V (tail Q r)
          IsActualTowerPullback f (head Q r) (head T r) a ∧
          (V : Set (split Q r).1)=a ⁻¹' (U : Set (split T r).1) ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ p ∧
          markedPullback (m := n) p J=J' ∧ IsActualTowerPullback p L' L q ∧
          q (⟨z,hp'⟩ : openPreimage (tail Q r) V)=(⟨g z,hp⟩ : openPreimage (tail T r) U) ∧
          IsInvDomain 1 J ∧ IsGeoTestTower J L ∧ (⟨g z,hp⟩ : openPreimage (tail T r) U) ∈ (geoTransformAlong J L).cosupp ∧
          IsInvDomain 1 J' ∧ IsGeoTestTower J' L' ∧
          (geoTransformAlong J' L').cosupp=q ⁻¹' (geoTransformAlong J L).cosupp ∧
          (⟨z,hp'⟩ : openPreimage (tail Q r) V) ∈ (geoTransformAlong J' L').cosupp ∧
          ∀ k : ℕ,(invFamily hn (k+1)).inv J' L' ⟨z,hp'⟩=(invFamily hn (k+1)).inv J L ⟨g z,hp⟩ := by
  obtain ⟨D',Q,g,h,_hg,_hLen,_hSquare,hQ,_hCurrent,_hWF,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  exact ⟨D',Q,g,h,hQ,fun z hy hns hl =>
    actual_original_zero_common_curve_full_values hn h M hM hmax hT z hy hns hl⟩

end
end Hironaka.HironakaOriginalZeroCommonCurveValues
