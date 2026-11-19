import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing

/-!
# Entire actual curve components in genuine zero-contact nonzero models

The actual head codimension-one part is closed and relatively open in
its actual cosupport. Genuine global analytic components are preconnected,
so an actual reference avoiding this part makes the ENTIRE component
avoid it after genuine head projection. The actual stage weak equivalence
internally proves selected dead contact components lie in the head part.
Actual zero-run/canonical original inputs consequently give enlarged
nonzero contact models covering the whole component trace, including
historical-boundary points. No candidate canonicality is inferred.

Mathematics.tex was written first. Formal registration and native target
build are pending; deeper zero histories, whole zero-level General3 and
global noncompact G3 termination remain OPEN.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactCurveNonzeroExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit HomogenizedIdealAlong HomogenizedIdealAlongTower
  GermIdealOrder DivisorExponentAlong CodimOneSupportAlong GlobalComponents
  RegularLocusComponent ContactStageInvDomain ContactStageKept ContactEquivalenceStage
  ContactEquivalenceAlong CoefficientIdealRestriction MaximalContactAlongTower
  HomogenizedGlueingTower MemberInterTowerAlong TangentDirectionAlong HironakaStepOneZeroContactRemainderGlueing
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  CanonicalCentres StepOneValue StepOneRegime StepOneLowerDomain MaxLocusLocal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem preconnected_avoids_codimOnePartAlong
    (J : MarkedIdeal n X) (hN : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent)
    (hd : 1 ≤ J.d) (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    {B : Set X} (hB : IsPreconnected B) (hBC : B ⊆ J.cosupp)
    {p : X} (hp : p ∈ B) (hpD : p ∉ codimOnePartAlong J.N J.ideal J.d) :
    ∀ q ∈ B, q ∉ codimOnePartAlong J.N J.ideal J.d := by
  obtain ⟨O, hO, hCO⟩ := exists_isOpen_cosupport_inter_eq_codimOnePartAlong
    (N := J.N) (𝔞 := J.ideal) (μ := J.d)
  have hD := isClosed_codimOnePartAlong hI hN hd hmax
  intro q hq hqD
  have hqO : q ∈ O := (hCO ▸ hqD).2
  have hcov : B ⊆ O ∪ (codimOnePartAlong J.N J.ideal J.d)ᶜ := by
    intro z hz
    by_cases hzD : z ∈ codimOnePartAlong J.N J.ideal J.d
    · exact Or.inl ((hCO ▸ hzD).2)
    · exact Or.inr hzD
  obtain ⟨z, hzB, hzO, hzD⟩ := hB O _ hO hD.isOpen_compl hcov
    ⟨q, hq, hqO⟩ ⟨p, hp, hpD⟩
  exact hzD (hCO ▸ ⟨hBC hzB, hzO⟩)

private theorem global_component_isPreconnected {A B : Set Y}
    (hB : B ∈ globalComponents (n := n) A) : IsPreconnected B := by
  obtain ⟨c, _, rfl⟩ := hB
  exact isPreconnected_connectedComponentIn.closure

theorem global_component_avoids_head_codimOnePartAlong
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    {A B : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAC : A ⊆ (geoTransformAlong (barMarked J) T).cosupp)
    (hB : B ∈ globalComponents (n := n) A)
    (j : ℕ) {p : Y} (hp : p ∈ B)
    (hpD : (tail T j).proj p ∉
      codimOnePartAlong (geoTransformAlong (barMarked J) (head T j)).N
        (geoTransformAlong (barMarked J) (head T j)).ideal
        (geoTransformAlong (barMarked J) (head T j)).d) :
    ∀ q ∈ B, (tail T j).proj q ∉
      codimOnePartAlong (geoTransformAlong (barMarked J) (head T j)).N
        (geoTransformAlong (barMarked J) (head T j)).ideal
        (geoTransformAlong (barMarked J) (head T j)).d := by
  have hw := isWellFormed_barMarked J hJ
  have hh := ((isGeoTestTower_iff_head_tail (barMarked J) T j).mp hT).1
  obtain ⟨hN, hI⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hw.isClosedSubmanifold_N hw.isCoherent (head T j) hh
  have hdh : 1 ≤ (geoTransformAlong (barMarked J) (head T j)).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hmh := isMaximalOrderAlong_geoTransformAlong hw.isClosedSubmanifold_N hw.isCoherent
    (isMaximalOrderAlong_barMarked J hJ hd hmax) (head T j) hh
  have hpre : IsPreconnected ((tail T j).proj '' B) :=
    (global_component_isPreconnected hB).image _ (tail T j).contMDiff_proj.continuous.continuousOn
  have hsub : (tail T j).proj '' B ⊆ (geoTransformAlong (barMarked J) (head T j)).cosupp := by
    rintro _ ⟨q, hq, rfl⟩
    exact StepOneCanonicalTail.mem_cosupp_head J hJ T hT
      (hAC (subset_of_mem_globalComponents hA hB hq)) j
  have hn := preconnected_avoids_codimOnePartAlong _ hN hI hdh hmh hpre hsub
    ⟨p, hp, rfl⟩ hpD
  intro q hq
  exact hn _ ⟨q, hq, rfl⟩

theorem actual_zero_run_whole_component_head_avoidance (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    {Z B : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z)
    (hZC : Z ⊆ (geoTransformAlong K R).cosupp)
    (hB : B ∈ globalComponents (n := n) Z)
    (p : Y) (hpB : p ∈ B) (hns : ¬ IsSpecial K R p) (hl : level K R p = 0) :
    ∀ j ≤ regimeRun (stepRegime K (level K R p)) R p, ∀ q ∈ B,
      (tail R j).proj q ∉ codimOnePartAlong
        (geoTransformAlong (barMarked K) (head R j)).N
        (geoTransformAlong (barMarked K) (head R j)).ideal
        (geoTransformAlong (barMarked K) (head R j)).d := by
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    K hK hmax hn R hcan
  have hZbar : Z ⊆ (geoTransformAlong (barMarked K) R).cosupp := by
    rw [hb.2.2]
    exact hZC
  intro j hj
  have hreg : stepRegime K (level K R p) (head R j) ((tail R j).proj p) := by
    by_cases hz : j = 0
    · subst j
      cases R <;> exact ⟨rfl, hns⟩
    · exact regime_head_of_le_regimeRun (stepRegime K (level K R p)) R p j (by omega) hj
  have hpD : (tail R j).proj p ∉ codimOnePartAlong
      (geoTransformAlong (barMarked K) (head R j)).N
      (geoTransformAlong (barMarked K) (head R j)).ideal
      (geoTransformAlong (barMarked K) (head R j)).d := by
    intro hpD
    exact hreg.2 (Or.inl ⟨hreg.1.trans hl, hpD⟩)
  exact global_component_avoids_head_codimOnePartAlong K hK.isWellFormed hK.one_le_d
    hmax R hb.1 hZ hZbar hB j hpB hpD

private theorem contact_geometry
    (J : MarkedIdeal n X) (hN : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent)
    (hd : 1 ≤ J.d) (U : Opens X) (w : X → ℂ)
    (hw : IsTangentDirectionAlong J.N J.ideal J.d U w)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked J) H) :
    let L := contactMarkedKept J w H (openPreimage H U)
    IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧ 1 ≤ L.d := by
  dsimp only
  have hHa := ((coeff_homAlong_wEquiv J hN hI hd).2 H).1.mp hH
  refine ⟨isClosedSubmanifold_strictAlong_stage_of_le J hN hI hd U hw H hHa
    (openPreimage H U) subset_rfl, ?_, ?_⟩
  · exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff J hI hN w H hH)
  · exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _

theorem selected_contact_components_subset_codimOnePartAlong
    (J : MarkedIdeal n X) (hN : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent)
    (hd : 1 ≤ J.d) (U : Opens X) (w : X → ℂ)
    (hw : IsTangentDirectionAlong J.N J.ideal J.d U w)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked J) H) :
    let L := contactMarkedKept J w H (openPreimage H U)
    selectedComponents (n := n) L.N L.cosupp ⊆
      (Subtype.val : openPreimage H U → Y) ⁻¹'
        codimOnePartAlong (geoTransformAlong (barMarked J) H).N
          (geoTransformAlong (barMarked J) H).ideal (geoTransformAlong (barMarked J) H).d := by
  dsimp only
  let L := contactMarkedKept J w H (openPreimage H U)
  obtain ⟨hLN, hLI, hLd⟩ := contact_geometry J hN hI hd U w hw H hH
  have hbarN : IsClosedSubmanifold n (barMarked J).N := hN
  have hbarI : (barMarked J).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hI hN) hN
  have hHa := ((coeff_homAlong_wEquiv J hN hI hd).2 H).1.mp hH
  intro q hq
  have hqN : q ∈ L.N := by
    rcases hq with ⟨B, ⟨hB, _⟩, hqB⟩
    exact subset_of_mem_globalComponents
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hLN) hB hqB
  by_contra hqD
  have hnz : IsNonzeroAlongAt L.N L.ideal q := isNonzeroAlongAt_stage_of_wEquiv J hN hI hd U hw H hHa
    (barMarked J) hbarN hbarI rfl hH
    (wEquiv_stage_coeffHomAlong J hN hI hd U hw H hH) q hqN hqD
  have hnot : ¬ IsNonzeroAlongAt L.N L.ideal q :=
    (HironakaStepOneZeroContactRemainderGlueing.selectedComponents_iff_not_isNonzeroAlongAt
      (X := CMfd.of (n := n) (openPreimage H U)) L hLN hLI hLd hqN).mp hq
  exact hnot hnz

theorem contact_mem_remaining_of_notMem_codimOnePartAlong
    (J : MarkedIdeal n X) (hN : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent)
    (hd : 1 ≤ J.d) (U : Opens X) (w : X → ℂ)
    (hw : IsTangentDirectionAlong J.N J.ideal J.d U w)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked J) H)
    (q : openPreimage H U) (hq : q ∈ (contactMarkedKept J w H (openPreimage H U)).N)
    (hqD : (q : Y) ∉ codimOnePartAlong (geoTransformAlong (barMarked J) H).N
      (geoTransformAlong (barMarked J) H).ideal (geoTransformAlong (barMarked J) H).d) :
    q ∈ remainingComponents (n := n) (contactMarkedKept J w H (openPreimage H U)).N
      (contactMarkedKept J w H (openPreimage H U)).cosupp := by
  have hLN := (contact_geometry J hN hI hd U w hw H hH).1
  rw [HironakaDimensionTwoStepOneAnalyticSuperlevels.remainingComponents_eq_diff_selected hLN]
  exact ⟨hq, fun hs => hqD (selected_contact_components_subset_codimOnePartAlong
    J hN hI hd U w hw H hH hs)⟩

theorem global_component_contact_projection_mem_remaining
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1 ≤ J.d)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked J) T)
    {A B : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAC : A ⊆ (geoTransformAlong (barMarked J) T).cosupp)
    (hB : B ∈ globalComponents (n := n) A) (j : ℕ) {p : Y} (hp : p ∈ B)
    (hpD : (tail T j).proj p ∉ codimOnePartAlong (geoTransformAlong (barMarked J) (head T j)).N
      (geoTransformAlong (barMarked J) (head T j)).ideal (geoTransformAlong (barMarked J) (head T j)).d)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong J.N J.ideal J.d U w) :
    ∀ q ∈ B, ∀ hqU : (tail T j).proj q ∈ openPreimage (head T j) U,
      (⟨(tail T j).proj q, hqU⟩ : openPreimage (head T j) U) ∈
        remainingComponents (n := n) (contactMarkedKept J w (head T j) (openPreimage (head T j) U)).N
          (contactMarkedKept J w (head T j) (openPreimage (head T j) U)).cosupp := by
  have hh := ((isGeoTestTower_iff_head_tail (barMarked J) T j).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv J hJ.isClosedSubmanifold_N hJ.isCoherent hd).2
    (head T j)).1.mp hh
  have hC := (coeff_homAlong_wEquiv J hJ.isClosedSubmanifold_N hJ.isCoherent hd).2 (head T j)
  intro q hq hqU
  have hqc := StepOneCanonicalTail.mem_cosupp_head J hJ T hT
    (hAC (subset_of_mem_globalComponents hA hB hq)) j
  rw [hC.2 hh] at hqc
  have hstrict := cosupp_subset_strictAlong_along J hJ.isClosedSubmanifold_N hJ.isCoherent
    hd hw (head T j) hHa ⟨hqc, hqU⟩
  have hqN : (⟨(tail T j).proj q, hqU⟩ : openPreimage (head T j) U) ∈
      (contactMarkedKept J w (head T j) (openPreimage (head T j) U)).N :=
    strictAlong_mono (head T j) inter_subset_left hstrict
  exact contact_mem_remaining_of_notMem_codimOnePartAlong J hJ.isClosedSubmanifold_N
    hJ.isCoherent hd U w hw (head T j) hh _ hqN
    (global_component_avoids_head_codimOnePartAlong J hJ hd hmax T hT hA hAC hB j hp hpD q hq)

private def wholeCurveOutput (K : MarkedIdeal n X) (R : BlowupTower X Y) (B : Set Y) (p : Y) : Prop :=
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    let W := maskB K H p₀
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      ∃ hW : W ≤ openPreimage H U,
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      ∃ hLN : IsClosedSubmanifold n L.N,
      let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
      let A := MarkedIdeal.pullback (Subtype.val : G → V) (contactRemainderMarked L K.E.length)
      IsGeoTestTower A (restrict G (restrict V Q)) ∧ nestedOpens V W ≤ G ∧
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW)
          (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      (∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        let O := openPreimage (restrict V P) G
        IsInvDomain 2 (geoTransformAlong A (restrict G (restrict V P))) ∧
          geoTransformAlong A (restrict G (restrict V P)) =
            MarkedIdeal.pullback (Subtype.val : O → openPreimage P V)
              (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) ∧
          MarkedIdeal.pullback χ (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
            MarkedIdeal.pullback
              (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
              (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P))) ∧
      ∀ q ∈ B, ∀ hqU : Q.proj q ∈ V,
        (⟨Q.proj q, hqU⟩ : V) ∈ remainingComponents (n := n) L.N L.cosupp

theorem exists_actual_zero_run_whole_component_nonzero_model (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    {Z B : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z)
    (hZC : Z ⊆ (geoTransformAlong K R).cosupp)
    (hB : B ∈ globalComponents (n := n) Z)
    (p : Y) (hpB : p ∈ B) (hns : ¬ IsSpecial K R p) (hl : level K R p = 0) :
    wholeCurveOutput K R B p := by
  have hp := hZC (subset_of_mem_globalComponents hZ hB hpB)
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    K hK hmax hn R hcan
  have hZbar : Z ⊆ (geoTransformAlong (barMarked K) R).cosupp := by
    rw [hb.2.2]
    exact hZC
  have hpbar := hZbar (subset_of_mem_globalComponents hZ hB hpB)
  obtain ⟨hreg, _⟩ := StepOneValueMasked.stepRegime_and_mem_cosupp_head
    K hK.isWellFormed R hb.1 hpbar hns
  let r := regimeRun (stepRegime K (level K R p)) R p
  have hpD : (tail R r).proj p ∉ codimOnePartAlong
      (geoTransformAlong (barMarked K) (head R r)).N
      (geoTransformAlong (barMarked K) (head R r)).ideal
      (geoTransformAlong (barMarked K) (head R r)).d := by
    intro hpD
    exact hreg.2 (Or.inl ⟨hreg.1.trans hl, hpD⟩)
  obtain ⟨U, hU, hw, hW, hLN, ht, hmask, hinit, hpref⟩ :=
    exists_actual_zero_contact_remainder_test_tower hn K hK hmax R hcan p hp hns hl
  dsimp only [wholeCurveOutput]
  refine ⟨U, hU, hw, hW, hLN, ht, hmask, hinit, hpref, ?_⟩
  exact global_component_contact_projection_mem_remaining K hK.isWellFormed hK.one_le_d
    hmax R hb.1 hZ hZbar hB r hpB hpD U _ hw

open HironakaGeneralThreeNonspecialAnalyticLoci HironakaDimensionThreeStepOneCurveEnvelope

theorem exists_actual_general_three_zero_curve_nonzero_models (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x) :
    let K := companionAt m T x
    let R := companionTailAt m T x
    ∃ Z : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) Z ∧
      AnalyticDimensionBasics.DimLE (n := n) Z 1 ∧ Z ⊆ (geoTransformAlong K R).cosupp ∧
      (∀ p ∈ (geoTransformAlong K R).cosupp, ¬ IsSpecial K R p → p ∈ Z) ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ p ∈ B,
        ¬ IsSpecial K R p → level K R p = 0 → wholeCurveOutput K R B p := by
  dsimp only
  obtain ⟨_, hK, hmax, hcanK, _⟩ :=
    actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  obtain ⟨Z, hZ, hdZ, hZC, hns⟩ :=
    exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  refine ⟨Z, hZ, hdZ, hZC, hns, ?_⟩
  intro B hB p hp hsp hl
  exact exists_actual_zero_run_whole_component_nonzero_model hn _ hK hmax _ hcanK
    hZ hZC hB p hp hsp hl

end
end Hironaka.HironakaStepOneZeroContactCurveNonzeroExtension
