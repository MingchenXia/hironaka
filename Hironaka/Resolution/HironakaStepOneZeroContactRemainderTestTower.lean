/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaStepOneZeroContactClippedCentres


/-!
# Genuine original remainder test towers on the actual selected complement

The actual selected-component complement contains the entire true remaining
carrier. On it the SAME original restricted tail is internally a genuine test
tower of the actual remainder: dropping old boundary members and retaining
literal empty historical entries preserves real admissibility at every step.
The actual restricted original map satisfies the genuine blowup universal
property along the true clipped-centre trace, internally identified with the
original-centre trace. No unrestricted original map is renamed as a new blowup.

On this open the ENTIRE controlled carrier, ideal and mark agree with the
restricted full parent, while the boundary remains the candidate boundary.
Old boundary members may be nonempty away from the carrier. ENTIRE four-field
restriction identity is proved for the SAME remainder. Whole marked-record
equality with the original lower record is retained only on the SAME original
mask, which is internally proved to lie ENTIRELY in the selected complement.

Original domain3/max/literal constructed Step1 and real nonspecial zero-level
inputs internally produce ONE actual open, genuine candidate test tower,
all-prefix domain2 and whole original-mask controlled record dictionary.
The original literal invFamily3 consumer supplies its actual companion inputs.
Private propositions abbreviate ONLY conclusions, never caller certificates.

Unrestricted ambient clipped-tower comparison, canonicality on the entire
selected complement, deeper zero-contact histories, cross-contact descent,
whole original zero-level/General3 superlevels and noncompact global termination
remain OPEN. Blueprint: `hironaka-step-one-zero-contact-remainder-test-tower-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactRemainderTestTower
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit DropMembers NormalCrossings CoefficientIdealRestriction
  NormalCrossingsComparison
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneMemberTailExtension HironakaStepOneZeroContactRemainderExtension
  HironakaStepOneZeroContactClippedCentres StepOneRegime
  HomogenizedGlueingTower HironakaCoherentTransformExtension MemberInterTowerAlong
open StepOneLowerDomain StepOneValue CanonicalCentres
  HironakaDimensionThreeStepOneLowerAnalyticLoci ContactEquivalenceAlong MaximalContactAlongTower
  TangentDirectionAlong ContactStageKept ContactStageInvDomain HomogenizedIdealAlong HomogenizedIdealAlongTower
  HironakaGeneralThreeNonspecialAnalyticLoci MaxLocusLocal BlowupTowerIsomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

def remainderOpen (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) : Opens X :=
  ⟨(selectedComponents (n := n) L.N L.cosupp)ᶜ,
    (isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩

private theorem empty_prefix_transform (M : MarkedIdeal n X) (k : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong ({M with E := List.replicate k ∅ ++ M.E} : MarkedIdeal n X) T =
        {geoTransformAlong M T with E := List.replicate k ∅ ++ (geoTransformAlong M T).E}
  | _, .refl => rfl
  | _, .step T C π hπ => by
    rw [geoTransformAlong_step, empty_prefix_transform M k T, geoTransformAlong_step, geoTransform_withE]
    rw [geoTransform_E, List.map_append, List.map_replicate]
    have hempty : BlowupStrictSubmanifold.geoStrictTransform π C ∅ = ∅ := by
      simp [BlowupStrictSubmanifold.geoStrictTransform]
    simp only [hempty, List.append_assoc]

private theorem empty_prefix_test (M : MarkedIdeal n X) (k : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      IsGeoTestTower ({M with E := List.replicate k ∅ ++ M.E} : MarkedIdeal n X) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨empty_prefix_test M k T hT.1, ?_⟩
    rw [empty_prefix_transform M k T]
    refine ⟨hT.2.1, hT.2.2.1, ?_⟩
    apply hasNormalCrossings_of_forall_disjoint hT.2.2.2
    intro F hF hn
    rcases List.mem_append.mp hF with hF | hF
    · rw [List.eq_of_mem_replicate hF]
      exact disjoint_empty _
    · exact False.elim (hn hF)

private theorem initial_record (L : MarkedIdeal n X) (k : ℕ) (hN : IsClosedSubmanifold n L.N) :
    let G := remainderOpen L hN
    let M := MarkedIdeal.pullback (Subtype.val : G → X) L
    MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k) =
      {M with E := List.replicate k ∅ ++ M.E.drop k} := by
  dsimp only
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    change ((x : X) ∈ remainingComponents (n := n) L.N L.cosupp) ↔ (x : X) ∈ L.N
    rw [remainingComponents_eq_diff_selected hN]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  · change (List.replicate k ∅ ++ L.E.drop k).map ((Subtype.val : remainderOpen L hN → X) ⁻¹' ·) =
      List.replicate k ∅ ++ (L.E.map ((Subtype.val : remainderOpen L hN → X) ⁻¹' ·)).drop k
    rw [List.map_append, List.map_replicate, preimage_empty, List.map_drop]
  · rfl
  · rfl

private theorem actual_restricted_test (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    let G := remainderOpen L hN
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)) (restrict G T) := by
  dsimp only
  let G := remainderOpen L hN
  let M := MarkedIdeal.pullback (Subtype.val : G → X) L
  have ht := isGeoTestTower_restrict G hN hI T hT
  have hkM : k ≤ M.E.length := by simpa only [M, MarkedIdeal.pullback, List.length_map] using hk
  have hdrop := isGeoTestTower_dropE (X := CMfd.of (n := n) G) M hkM (restrict G T) ht
  have hpad := empty_prefix_test (X := CMfd.of (n := n) G)
    ({M with E := M.E.drop k} : MarkedIdeal n G) k (restrict G T) hdrop
  rw [initial_record L k hN]
  exact hpad

private theorem transform_formula (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (T : BlowupTower X Y) :
    let G := remainderOpen L hN
    let M := MarkedIdeal.pullback (Subtype.val : G → X) L
    geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)) (restrict G T) =
      {geoTransformAlong M (restrict G T) with
        E := List.replicate k ∅ ++ (geoTransformAlong M (restrict G T)).E.drop k} := by
  dsimp only
  let G := remainderOpen L hN
  let M := MarkedIdeal.pullback (Subtype.val : G → X) L
  have hkM : k ≤ M.E.length := by simpa only [M, MarkedIdeal.pullback, List.length_map] using hk
  rw [initial_record L k hN]
  have he := empty_prefix_transform (X := CMfd.of (n := n) G)
    ({M with E := M.E.drop k} : MarkedIdeal n G) k (restrict G T)
  rw [geoTransformAlong_dropE (X := CMfd.of (n := n) G) M hkM (restrict G T)] at he
  exact he

private theorem remainder_boundary (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (T : BlowupTower X Y) : (geoTransformAlong (contactRemainderMarked L k) T).E =
      List.replicate k ∅ ++ (geoTransformAlong L T).E.drop k := by
  have hi : (contactRemainderMarked L k).E =
      ({L with E := List.replicate k ∅ ++ L.E.drop k} : MarkedIdeal n X).E := rfl
  have h := HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq hi T
  have he := empty_prefix_transform ({L with E := L.E.drop k} : MarkedIdeal n X) k T
  rw [geoTransformAlong_dropE L hk T] at he
  exact h.trans (congrArg MarkedIdeal.E he)

private theorem carrier_trace (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (T : BlowupTower X Y) :
    let O := openPreimage T (remainderOpen L hN)
    (Subtype.val : O → Y) ⁻¹' (geoTransformAlong L T).N =
      (Subtype.val : O → Y) ⁻¹' (geoTransformAlong (contactRemainderMarked L k) T).N := by
  dsimp only
  have hr := isClosedSubmanifold_remainingComponents hN L.cosupp
  have hs := isClosedSubmanifold_selectedComponents hN L.cosupp
  have hsub : selectedComponents (n := n) L.N L.cosupp ⊆ L.N := by
    rintro x ⟨B, ⟨hB, _⟩, hxB⟩
    exact GlobalComponents.subset_of_mem_globalComponents
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hB hxB
  have hpart : L.N = remainingComponents (n := n) L.N L.cosupp ∪ selectedComponents (n := n) L.N L.cosupp := by
    rw [remainingComponents_eq_diff_selected hN]
    exact (sdiff_union_of_subset hsub).symm
  have hdis : Disjoint (remainingComponents (n := n) L.N L.cosupp) (selectedComponents (n := n) L.N L.cosupp) := by
    rw [remainingComponents_eq_diff_selected hN]; exact disjoint_sdiff_left
  have hstrict := strictAlong_eq_inter_preimage_of_closed_partition hr.1 hs.1 hdis hpart T
  ext x
  simp only [mem_preimage, N_geoTransformAlong, contactRemainderMarked]
  rw [hstrict]
  refine ⟨fun hx => ⟨hx, ?_⟩, fun hx => hx.1⟩
  rw [remainingComponents_eq_diff_selected hN]
  exact ⟨MemberInterTowerAlong.strictAlong_subset_preimage T hN.1 hx, x.2⟩

theorem remainder_restricted_isGeoTestTower (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    let G := remainderOpen L hN
    let O := openPreimage T G
    let A := geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)) (restrict G T)
    let B := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong L T)
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)) (restrict G T) ∧
      A.N = B.N ∧ A.ideal = B.ideal ∧ A.d = B.d ∧
      A = MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (contactRemainderMarked L k) T) := by
  dsimp only
  let G := remainderOpen L hN
  let O := openPreimage T G
  let B := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong L T)
  have hf := transform_formula L k hk hN T
  dsimp only at hf
  rw [geoTransformAlong_restrict G hN hI T hT] at hf
  refine ⟨actual_restricted_test L k hk hN hI T hT, ?_⟩
  rw [hf]
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact carrier_trace L k hN T
  · change List.replicate k ∅ ++ ((geoTransformAlong L T).E.map ((Subtype.val : O → Y) ⁻¹' ·)).drop k =
      (geoTransformAlong (contactRemainderMarked L k) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)
    rw [remainder_boundary L k hk T, List.map_append, List.map_replicate, preimage_empty, List.map_drop]
  · exact (remainder_controlled_ideal_open_eq L k hN hI T hT).symm
  · simp only [MarkedIdeal.pullback, d_geoTransformAlong, contactRemainderMarked]

theorem remainder_original_centre_trace_and_blowup {Z : CMfd.{u} n}
    (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hC : (geoTransformAlong L T).IsAdmissibleCentre C) :
    let G := remainderOpen L hN
    let O := openPreimage T G
    let O' : Opens Z := ⟨π ⁻¹' (O : Set Y), hπ.contMDiff.continuous.isOpen_preimage _ O.isOpen⟩
    (Subtype.val : O → Y) ⁻¹' C =
      (Subtype.val : O → Y) ⁻¹' (C ∩ (geoTransformAlong (contactRemainderMarked L k) T).N) ∧
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k))
      (restrict G T)).IsAdmissibleCentre ((Subtype.val : O → Y) ⁻¹' C) ∧
    IsBlowupAlong n ((Subtype.val : O → Y) ⁻¹' (C ∩ (geoTransformAlong (contactRemainderMarked L k) T).N))
      (fun z : O' => (⟨π z, z.2⟩ : O)) := by
  dsimp only
  let G := remainderOpen L hN
  let O := openPreimage T G
  have htrace : (Subtype.val : O → Y) ⁻¹' C =
      (Subtype.val : O → Y) ⁻¹' (C ∩ (geoTransformAlong (contactRemainderMarked L k) T).N) := by
    ext x
    refine ⟨fun hx => ⟨hx, ?_⟩, fun hx => hx.1⟩
    exact (Set.ext_iff.mp (carrier_trace L k hN T) x).mp (hC.subset_N hx)
  have ht' := (remainder_restricted_isGeoTestTower L k hk hN hI (.step T C π hπ) ⟨hT, hC⟩).1
  refine ⟨htrace, ht'.2, ?_⟩
  rw [← htrace]
  exact BlowupRestrictOpen.isBlowupAlong_restrict hπ O _

/-- A conclusion-only abbreviation: no caller supplies these produced fields. -/
private def testTowerOutput (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) : Prop :=
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
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      ∀ j : ℕ, let P := head Q j
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
              (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P))

theorem exists_actual_zero_contact_remainder_test_tower (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) : testTowerOutput K R p := by
  obtain ⟨U, hU, hw, hW, hinit, hpref⟩ :=
    contactRemainder_actual_masked_prefix_eq hn K hK hmax R hcan p hp hns hl
  dsimp only [testTowerOutput]
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let w := (tangentChoice K (H.proj p₀)).2
  let V := openPreimage H U
  let W := maskB K H p₀
  let L := contactMarkedKept K w H V
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) (H.append Q) := by
    dsimp only [H, Q]; rw [head_append_tail]; exact hb.1
  have hH := ((isGeoTestTower_append_iff _ H Q).mp ht).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hglobal := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent
    hK.isWellFormed.isClosedSubmanifold_N w H hH
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hglobal
  have htV : IsGeoTestTower L (restrict V Q) := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H Q ht V subset_rfl).1
  have hk : K.E.length ≤ L.E.length := by
    change K.E.length ≤ ((geoTransformAlong (barMarked K) H).E.map
      ((Subtype.val : V → _) ⁻¹' ·)).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked K) H
  let G := remainderOpen (X := CMfd.of (n := n) V) L hLN
  have hfull : MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) L =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) :=
    pullback_val_pullback_val hglobal hW
  have hmask : nestedOpens V W ≤ G := by
    have heq := congrArg MarkedIdeal.N (hinit.trans hfull.symm)
    intro z hz
    change z ∉ selectedComponents (n := n) L.N L.cosupp
    intro hs
    have hzN : z ∈ L.N := by
      rcases hs with ⟨B, ⟨hB, _⟩, hzB⟩
      exact GlobalComponents.subset_of_mem_globalComponents
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hLN) hB hzB
    have hzR : z ∈ remainingComponents (n := n) L.N L.cosupp :=
      (Set.ext_iff.mp heq ⟨z, hz⟩).mpr hzN
    rw [remainingComponents_eq_diff_selected hLN] at hzR
    exact hzR.2 hs
  refine ⟨U, hU, hw, hW, hLN,
    (remainder_restricted_isGeoTestTower (X := CMfd.of (n := n) V) L K.E.length hk hLN hLI _ htV).1,
    hmask, hinit, ?_⟩
  intro j
  have htP : IsGeoTestTower L (restrict V (head Q j)) := by
    have hparent := ((isGeoTestTower_iff_head_tail _ _ j).mp
      ((isGeoTestTower_append_iff _ H Q).mp ht).2).1
    exact (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H (head Q j)
      ((isGeoTestTower_append_iff _ H (head Q j)).mpr ⟨hH, hparent⟩) V subset_rfl).1
  have heq := (remainder_restricted_isGeoTestTower (X := CMfd.of (n := n) V)
    L K.E.length hk hLN hLI _ htP).2.2.2.2
  refine ⟨?_, heq, (hpref j).2⟩
  rw [heq]
  exact InvDomainTowerAlong.isInvDomain_pullback_val _ (hpref j).1

theorem exists_actual_general_three_remainder_test_tower (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hns : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hl : level (companionAt m T x) (companionTailAt m T x) p = 0) :
    testTowerOutput
      (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
      (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
      (companionAt m T x) (companionTailAt m T x) p := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact exists_actual_zero_contact_remainder_test_tower
    (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
    (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hns hl

end
end Hironaka.HironakaStepOneZeroContactRemainderTestTower
