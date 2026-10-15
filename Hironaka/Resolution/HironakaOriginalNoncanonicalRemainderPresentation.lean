/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalNoncanonicalUniformContactPresentation
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing
/-! Original-input noncanonical lower contact presentations on the actual
selected-component complement. All actual historical empty positions and the
entire exceptional suffix are retained. No frozen lower-history claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalNoncanonicalRemainderPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower ContactStageKept StepOneLowerDomain StepOneValue
  TangentDirectionAlong MaximalContactAlongTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaOriginalNoncanonicalUniformContactPresentation
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneZeroContactRemainderGlueing
  DivisorExponentAlong GermIdealOrder MemberInterTowerAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- Actual chosen tangent data and genuine selected-component complement are
internally constructed from ONLY original maximal-order domain/test data. -/
theorem exists_original_test_nonzero_contact_domain :
    ∀ (M : MarkedIdeal n X) (_hM : IsInvDomain (k+2) M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y) (_hT₀ : IsGeoTestTower M T₀)
    (y : Y) (_hy : y ∈ (geoTransformAlong M T₀).cosupp),
    let w := (tangentChoice M (T₀.proj y)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice M (T₀.proj y)).1 ∧ T₀.proj y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U w ∧
      let V := openPreimage T₀ U
      let L := contactMarkedKept M w T₀ V
      ∃ hLN : IsClosedSubmanifold n L.N, L.ideal.IsCoherent ∧
        let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
        let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
        IsInvDomain (k+1) A ∧
          ∀ p ∈ L.N, p ∈ G ↔ IsNonzeroAlongAt L.N L.ideal p := by
  intro M hM hmax T₀ hT₀ y hy
  dsimp only
  obtain ⟨U,hU,hyU,hw,hN,hI,_hdim,hd,_hE,_hcs⟩ :=
    exists_original_test_chosen_contact_geometry M hM hmax T₀ hT₀ y hy
  let V := openPreimage T₀ U
  let L := contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀ V
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hbar : IsGeoTestTower (barMarked M) T₀ := (he.2 T₀).1.mpr hT₀
  have hR := HironakaOriginalWholeContactRemainderDomain.contact_remainder_domain
    M hM U _ hw T₀ (.refl : BlowupTower Y Y) hbar
  change IsInvDomain (k+1) (contactRemainderMarked L M.E.length) at hR
  let G := remainderOpen (X := CMfd.of (n := n) V) L hN
  have hA := InvDomainTowerAlong.isInvDomain_pullback_val G hR
  refine ⟨U,hU,hyU,hw,hN,hI,hA,?_⟩
  intro p hp
  change p ∉ selectedComponents (n := n) L.N L.cosupp ↔ IsNonzeroAlongAt L.N L.ideal p
  have hs := HironakaStepOneZeroContactRemainderGlueing.selectedComponents_iff_not_isNonzeroAlongAt
    (X := CMfd.of (n := n) V) L hN hI hd hp
  exact (not_congr hs).trans not_not

/-- The SAME actual lower model, chosen BEFORE all future ORIGINAL test
extensions, supplies actual nested TEST/domain and ENTIRE controlled records. -/
theorem exists_original_test_uniform_nonzero_contact_presentation :
    ∀ (M : MarkedIdeal n X) (_hM : IsInvDomain (k+2) M)
    (_hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y) (_hT₀ : IsGeoTestTower M T₀)
    (y : Y) (_hy : y ∈ (geoTransformAlong M T₀).cosupp),
    let w := (tangentChoice M (T₀.proj y)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice M (T₀.proj y)).1 ∧ T₀.proj y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U w ∧
      let V := openPreimage T₀ U
      let L := contactMarkedKept M w T₀ V
      ∃ hLN : IsClosedSubmanifold n L.N, L.ideal.IsCoherent ∧
        let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
        let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
        IsInvDomain (k+1) A ∧
          (∀ p ∈ L.N, p ∈ G ↔ IsNonzeroAlongAt L.N L.ideal p) ∧
          ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z), IsGeoTestTower M (T₀.append Q) →
            let P := restrict V Q
            let O := openPreimage P G
            let A' := geoTransformAlong A (restrict G P)
            let B := MarkedIdeal.pullback (Subtype.val : O → openPreimage Q V) (geoTransformAlong L P)
            IsGeoTestTower A (restrict G P) ∧ IsInvDomain (k+1) A' ∧
              A'.N = B.N ∧ A'.ideal = B.ideal ∧ A'.d = B.d ∧
              A' = MarkedIdeal.pullback (Subtype.val : O → openPreimage Q V)
                (geoTransformAlong (contactRemainderMarked L M.E.length) P) ∧
              A'.cosupp = (fun z : O => ((z : openPreimage Q V) : Z)) ⁻¹'
                (geoTransformAlong M (T₀.append Q)).cosupp := by
  intro M hM hmax T₀ hT₀ y hy
  dsimp only
  obtain ⟨U,hU,hyU,hw,hLN,hI,hA,hPoint⟩ :=
    exists_original_test_nonzero_contact_domain M hM hmax T₀ hT₀ y hy
  refine ⟨U,hU,hyU,hw,hLN,hI,hA,hPoint,?_⟩
  intro Z Q hQ
  let V := openPreimage T₀ U
  let L := contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀ V
  let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
  let P := restrict V Q
  let O := openPreimage P G
  let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L M.E.length)
  let B := MarkedIdeal.pullback (Subtype.val : O → openPreimage Q V) (geoTransformAlong L P)
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hbar : IsGeoTestTower (barMarked M) (T₀.append Q) := (he.2 _).1.mpr hQ
  have ht := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
    U hw T₀ Q hbar V subset_rfl
  have hk : M.E.length ≤ L.E.length := by
    change M.E.length ≤ ((geoTransformAlong (barMarked M) T₀).E.map _).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked M) T₀
  obtain ⟨hTest,hN,hId,hd,hRec⟩ := remainder_restricted_isGeoTestTower
    (X := CMfd.of (n := n) V) L M.E.length hk hLN hI P ht.1
  have hFuture := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA (restrict G P) hTest
  refine ⟨hTest,hFuture,hN,hId,hd,hRec,?_⟩
  have hCos : (geoTransformAlong A (restrict G P)).cosupp = B.cosupp := by
    change cosupport n (geoTransformAlong A (restrict G P)).N
      (geoTransformAlong A (restrict G P)).ideal (geoTransformAlong A (restrict G P)).d =
      cosupport n B.N B.ideal B.d
    rw [hN,hId,hd]
  have hLP := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hLN hI P ht.1).2
  have hOpen := cosupp_pullback_val (geoTransformAlong L P)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hLP hg) (openPreimage P G)
  have hOrig := ht.2.trans (congrArg (fun S => (Subtype.val : openPreimage Q V → Z) ⁻¹' S)
    ((he.2 _).2 hbar))
  exact hCos.trans (hOpen.trans (congrArg (fun S => (Subtype.val : O → openPreimage Q V) ⁻¹' S) hOrig))

end
end Hironaka.HironakaOriginalNoncanonicalRemainderPresentation
