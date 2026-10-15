/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalActualSmoothLowerDiagram
/-! Literal nested restrictions of original smooth upper histories internally
supply genuine lower TESTS and WHOLE controlled-history dictionaries. Source
contact uses transported ORIGINAL choice, without frozen higher-history claims. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalActualSmoothLowerHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ContactStageKept
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneLowerDomain TangentDirectionAlong
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaOriginalNoncanonicalRemainderPresentation HironakaOriginalActualSmoothLowerDiagram
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionOriginalContactHistory
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionHistoricalControlledTail
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y : CMfd.{u} m}

/-- ONLY original inputs produce the SAME actual nested source and target
lower TESTS, their future domains, ENTIRE marked records and BOTH cosupports. -/
theorem exists_original_test_actual_smooth_lower_history :
    ∀ {f : Y → X}
    (_hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (_hM : IsInvDomain (k+2) M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T : BlowupTower X D) (_hT : IsGeoTestTower M T)
    (y : D) (_hy : y ∈ (geoTransformAlong M T).cosupp) (j : ℕ),
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧ IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      let w := (tangentChoice M ((head T j).proj ((tail T j).proj y))).2
      ∃ U : Opens X,(U : Set X)=(tangentChoice M ((head T j).proj ((tail T j).proj y))).1 ∧
        (head T j).proj ((tail T j).proj y) ∈ U ∧
        IsTangentDirectionAlong M.N M.ideal M.d U w ∧
        let V := openPreimage (head T j) U
        let L := contactMarkedKept M w (head T j) V
        ∃ hLN : IsClosedSubmanifold n L.N,L.ideal.IsCoherent ∧
          let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
          let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
          IsInvDomain (k+1) A ∧
          ∃ (a : (split Q j).1 → (split T j).1) (V' : Opens (split Q j).1) (p : V' → V),
            IsActualTowerPullback f (head Q j) (head T j) a ∧
            (V' : Set (split Q j).1)=a ⁻¹' (V : Set (split T j).1) ∧
            Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ p ∧
            let P := markedPullback (m := m) p L
            P=contactMarkedKept (markedPullback (m := m) f M) (w ∘ f) (head Q j) V' ∧
            ∃ hPN : IsClosedSubmanifold m P.N,
              let G' := remainderOpen (X := CMfd.of (n := m) V') P hPN
              let B := MarkedIdeal.pullback (Subtype.val : G' → V') (contactRemainderMarked P M.E.length)
              let R := restrict G (restrict V (tail T j))
              let S := restrict G' (restrict V' (tail Q j))
              ∃ (q : G' → G) (e : openPreimage (restrict V' (tail Q j)) G' → openPreimage (restrict V (tail T j)) G),
                (G' : Set V')=p ⁻¹' (G : Set V) ∧
                Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ q ∧
                (∀ z,(q z : V)=p (z : V')) ∧ markedPullback (m := m) q A=B ∧
                IsInvDomain (k+1+(m-n)) B ∧ IsActualTowerPullback q S R e ∧
                Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ e ∧
                IsGeoTestTower A R ∧ IsGeoTestTower B S ∧
                IsInvDomain (k+1) (geoTransformAlong A R) ∧
                IsInvDomain (k+1+(m-n)) (geoTransformAlong B S) ∧
                geoTransformAlong B S=markedPullback (m := m) e (geoTransformAlong A R) ∧
                (geoTransformAlong B S).cosupp=e ⁻¹' (geoTransformAlong A R).cosupp := by
  intro f hf M hM hmax T hT y hy j
  obtain ⟨D',Q,g,hCart,_hg,_hLen,_hSquare,hQ,_hCurrent,_hw,_hCos,_hHeads⟩ :=
    exists_actual_relative_marked_tower hf M hM.isWellFormed T hT
  have hs := (isGeoTestTower_iff_head_tail M T j).mp hT
  have hHead := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head T j) hs.1
  have hyTail : y ∈ (geoTransformAlong (geoTransformAlong M (head T j)) (tail T j)).cosupp := by
    rw [←geoTransformAlong_append,head_append_tail]
    exact hy
  have hyHead := proj_mem_cosupp_of_mem_cosupp hHead.isWellFormed.isClosedSubmanifold_N
    hHead.isWellFormed.isCoherent (tail T j) hs.2 hyTail
  obtain ⟨U,hU,hyU,hw,hLN,hI,hA,_hPoint,hFuture⟩ :=
    exists_original_test_uniform_nonzero_contact_presentation M hM hmax (head T j) hs.1
      ((tail T j).proj y) hyHead
  refine ⟨D',Q,g,hCart,hQ,U,hU,hyU,hw,hLN,hI,hA,?_⟩
  let w := (tangentChoice M ((head T j).proj ((tail T j).proj y))).2
  let V := openPreimage (head T j) U
  let L := contactMarkedKept M w (head T j) V
  let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
  let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
  have hFull : IsGeoTestTower M ((head T j).append (tail T j)) := by rw [head_append_tail]; exact hT
  have hF := hFuture (tail T j) hFull
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hBar : IsGeoTestTower (barMarked M) T := (he.2 _).1.mpr hT
  obtain ⟨a,V',p,e₀,hHeadCart,_hTailCart,hV',hp,_hpcoord,_he₀coord,hContact,hRaw⟩ :=
    IsActualTowerPullback.exists_split_original_contact_diagram hCart M hM.isWellFormed hBar w j V
  obtain ⟨hPN,q,hG',hq,hqcoord,hLower⟩ := exists_actual_remainder_open_smooth_diagram
    (X := CMfd.of (n := n) V) (Y := CMfd.of (n := m) V') hp L hLN hI
      (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) M.E.length
  let P := markedPullback (m := m) p L
  let G' := remainderOpen (X := CMfd.of (n := m) V') P hPN
  let B := MarkedIdeal.pullback (Subtype.val : G' → V') (contactRemainderMarked P M.E.length)
  let R := restrict G (restrict V (tail T j))
  let S := restrict G' (restrict V' (tail Q j))
  obtain ⟨q₀,e,hq₀,_he,hLowerCart⟩ := IsActualTowerPullback.exists_actual_open_restriction hRaw G G' hG'
  have hqSame : q₀=q := by
    funext z
    exact Subtype.ext ((hq₀ z).trans (hqcoord z).symm)
  subst q₀
  have hDict := IsActualTowerPullback.relative_marked_dictionary hLowerCart A hA.isWellFormed hF.1
  have hCos := IsActualTowerPullback.relative_cosupport_dictionary hLowerCart A hA.isWellFormed hF.1
  rw [hLower] at hDict hCos
  have hBDom := isInvDomain_markedPullback_submersion hq A hA
  rw [hLower] at hBDom
  have hBNext := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBDom S hDict.1
  exact ⟨a,V',p,hHeadCart,hV',hp,hContact,hPN,q,e,hG',hq,hqcoord,hLower,hBDom,
    hLowerCart,hLowerCart.isSubmersion,hF.1,hDict.1,hF.2.1,hBNext,hDict.2,hCos⟩

end
end Hironaka.HironakaOriginalActualSmoothLowerHistory
