/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalNoncanonicalRemainderPresentation
/-! Genuine selected-zero strict persistence and reconstruction of the WHOLE
contact cosupport from independently constructed zero and nonzero branches. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSelectedContactCosupport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower ContactStageKept StepOneLowerDomain StepOneValue
  TangentDirectionAlong MaximalContactAlongTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberTailExtension MemberInterTowerAlong
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaOriginalNoncanonicalRemainderPresentation DivisorExponentAlong GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- Actual closure of the genuine off-centre preimage, not an assumed
persistence certificate, transports ANY initial cosupport subset. -/
theorem strictAlong_subset_cosupp_of_subset (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {S : Set X} (hS : S ⊆ M.cosupp) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      strictAlong T S ⊆ (geoTransformAlong M T).cosupp
  | _, .refl, _ => hS
  | _, .step T C π hπ, hT => by
    have ih := strictAlong_subset_cosupp_of_subset M hN hI hS T hT.1
    obtain ⟨hNT,hIT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT.1
    obtain ⟨hNP,hIP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI (.step T C π hπ) hT
    change closure (π ⁻¹' (strictAlong T S \ C)) ⊆ _
    apply closure_minimal ?_ (GiraudAlong.isClosed_cosupport_along hIP hNP _)
    intro z hz
    exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong M T) hNT.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIT hg)
      hπ hz.2).mpr (ih hz.1)

/-- Actual zero and nonzero branches together cover the ENTIRE cosupport
along ANY genuine test, with a real inclusion image of the actual lower model. -/
theorem whole_cosupp_selected_remainder_decomposition
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (m : ℕ) (hm : m ≤ L.E.length) (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    let G := remainderOpen L hN
    let O := openPreimage T G
    let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L m)
    (geoTransformAlong L T).cosupp = strictAlong T (selectedComponents (n := n) L.N L.cosupp) ∪
      (Subtype.val : O → Y) '' (geoTransformAlong A (restrict G T)).cosupp := by
  dsimp only
  let G := remainderOpen L hN
  let O := openPreimage T G
  let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L m)
  let B := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong L T)
  have hS : selectedComponents (n := n) L.N L.cosupp ⊆ L.cosupp := by
    rintro x ⟨K,⟨_hK,hKA⟩,hxK⟩
    exact hKA hxK
  have hPersist := strictAlong_subset_cosupp_of_subset L hN hI hS T hT
  obtain ⟨_hTest,hNA,hIA,hdA,_hRec⟩ := remainder_restricted_isGeoTestTower L m hm hN hI T hT
  have hCos : (geoTransformAlong A (restrict G T)).cosupp = B.cosupp := by
    change cosupport n (geoTransformAlong A (restrict G T)).N
      (geoTransformAlong A (restrict G T)).ideal (geoTransformAlong A (restrict G T)).d =
      cosupport n B.N B.ideal B.d
    rw [hNA,hIA,hdA]
  have hIT := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT).2
  have hOpen := cosupp_pullback_val (geoTransformAlong L T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIT hg) O
  have hTrace := hCos.trans hOpen
  have hSsub : selectedComponents (n := n) L.N L.cosupp ⊆ L.N := by
    rintro x ⟨K,⟨hK,_⟩,hxK⟩
    exact GlobalComponents.subset_of_mem_globalComponents
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hK hxK
  have hPart : L.N = selectedComponents (n := n) L.N L.cosupp ∪
      remainingComponents (n := n) L.N L.cosupp := by
    rw [remainingComponents_eq_diff_selected hN]
    rw [union_comm]
    exact (sdiff_union_of_subset hSsub).symm
  have hDis : Disjoint (selectedComponents (n := n) L.N L.cosupp)
      (remainingComponents (n := n) L.N L.cosupp) := by
    rw [remainingComponents_eq_diff_selected hN]
    exact disjoint_sdiff_right
  have hStrict := strictAlong_eq_inter_preimage_of_closed_partition
    (isClosedSubmanifold_selectedComponents hN L.cosupp).1
    (isClosedSubmanifold_remainingComponents hN L.cosupp).1 hDis hPart T
  apply Set.ext
  intro z
  constructor
  · intro hz
    by_cases hzS : T.proj z ∈ selectedComponents (n := n) L.N L.cosupp
    · left
      rw [hStrict]
      exact ⟨by rw [← N_geoTransformAlong L T]; exact hz.1,hzS⟩
    · right
      refine ⟨(⟨z,hzS⟩ : O),?_,rfl⟩
      rw [hTrace]
      exact hz
  · rintro (hz | ⟨p,hp,rfl⟩)
    · exact hPersist hz
    · exact (Set.ext_iff.mp hTrace p).mp hp

/-- All actual choices precede the future extension. Both genuine selected
zero branches and actual nonzero lower tests present the WHOLE original trace. -/
theorem exists_original_test_complete_contact_cosupport_presentation :
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
          ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z), IsGeoTestTower M (T₀.append Q) →
            let P := restrict V Q
            let O := openPreimage P G
            IsGeoTestTower A (restrict G P) ∧ IsInvDomain (k+1) (geoTransformAlong A (restrict G P)) ∧
              (Subtype.val : openPreimage Q V → Z) ⁻¹' (geoTransformAlong M (T₀.append Q)).cosupp =
                strictAlong P (selectedComponents (n := n) L.N L.cosupp) ∪
                  (Subtype.val : O → openPreimage Q V) '' (geoTransformAlong A (restrict G P)).cosupp := by
  intro M hM hmax T₀ hT₀ y hy
  dsimp only
  obtain ⟨U,hU,hyU,hw,hLN,hI,hA,_hPoint,hFuture⟩ :=
    exists_original_test_uniform_nonzero_contact_presentation M hM hmax T₀ hT₀ y hy
  refine ⟨U,hU,hyU,hw,hLN,hI,hA,?_⟩
  intro Z Q hQ
  let V := openPreimage T₀ U
  let L := contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀ V
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hbar : IsGeoTestTower (barMarked M) (T₀.append Q) := (he.2 _).1.mpr hQ
  have ht := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
    U hw T₀ Q hbar V subset_rfl
  have hm : M.E.length ≤ L.E.length := by
    change M.E.length ≤ ((geoTransformAlong (barMarked M) T₀).E.map _).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked M) T₀
  obtain ⟨hTest,hDom,_⟩ := hFuture Q hQ
  have hOrig := ht.2.trans (congrArg (fun S => (Subtype.val : openPreimage Q V → Z) ⁻¹' S)
    ((he.2 _).2 hbar))
  exact ⟨hTest,hDom,hOrig.symm.trans (whole_cosupp_selected_remainder_decomposition
    (X := CMfd.of (n := n) V) L hLN hI M.E.length hm (restrict V Q) ht.1)⟩

end
end Hironaka.HironakaOriginalSelectedContactCosupport
