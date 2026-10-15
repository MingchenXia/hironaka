/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Support.ContactStageGlueingExact
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderTestTower

/-!
# Actual zero-contact remainder records under genuine contact glueing

The true selected smooth-component union is internally identified with the
actual zero-along ideal-germ locus, without dimension or finiteness bounds.
Genuine open and biholomorphic ideal pullbacks therefore transport the entire
remaining carrier and all four fields of the actual remainder record.
Actual contact lifts internally supply smoothness, coherence and positive mark,
preserve the entire exceptional boundary and retain literal empty history pads.
Original domain3/max/literal canonical Step1 inputs generate their real chosen
tangent directions and whole remainder dictionaries at EVERY literal prefix.

Candidate canonicality, deeper zero histories, whole zero-level/General3
analytic superlevels and noncompact global G3 termination remain OPEN.
The mathematics was written first in Mathematics.tex beside this own draft.
This offlib checkpoint is not yet a formal registered module or target build.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactRemainderGlueing
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction
  GermIdealOrder BlowupTowers BlowupTowerTransforms
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneMemberLowerExtension HironakaStepOneZeroContactRemainderExtension
  HironakaStepOneZeroContactClippedCentres HironakaStepOneZeroContactRemainderTestTower
  DivisorExponentAlong CodimOneSupportAlong GlobalComponents
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
open HomogenizedGlueingAlongTower HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingLiftAlong ContactIndependenceAlong ContactStageInvDomain
  ContactStageKept ContactEquivalenceAlong MemberInterTowerAlong StepOneRegime
  TangentDirectionAlong MaximalContactAlongTower MaximalOrderStepOneB
  StepOneValue StepOneLowerDomain CanonicalCentres BlowupTowerSplit
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem selectedComponents_iff_not_isNonzeroAlongAt (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) {x : X} (hx : x ∈ L.N) :
    x ∈ selectedComponents (n := n) L.N L.cosupp ↔
      ¬ IsNonzeroAlongAt L.N L.ideal x := by
  constructor
  · intro hxS hnz
    obtain ⟨g, hg, hfreq⟩ := hnz
    have hxR : x ∉ remainingComponents (n := n) L.N L.cosupp := by
      rw [remainingComponents_eq_diff_selected hN]
      exact fun h => h.2 hxS
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ L.N → y ∈ L.cosupp := by
      filter_upwards [(isClosedSubmanifold_remainingComponents hN L.cosupp).1.isOpen_compl.mem_nhds hxR]
        with y hy hyN
      have hyS : y ∈ selectedComponents (n := n) L.N L.cosupp := by
        by_contra hnot
        apply hy
        rw [remainingComponents_eq_diff_selected hN]
        exact ⟨hyN, hnot⟩
      obtain ⟨B, ⟨_, hBA⟩, hyB⟩ := hyS
      exact hBA hyB
    have hf := (hfreq.and_eventually
      (hnear.and (HomogenizedGlueing.eventually_mem hI hg))).exists
    obtain ⟨y, ⟨hyN, hgy⟩, hycs, hmem⟩ := hf
    have hhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hmem
    exact hgy ((vanishesToOrderOn_one_iff hyN hhol).mp
      (VanishesToOrderOn.mono hd ((hycs hyN).2 g hmem)))
  · intro hz
    by_contra hxS
    have hxR : x ∈ remainingComponents (n := n) L.N L.cosupp := by
      rw [remainingComponents_eq_diff_selected hN]
      exact ⟨hx, hxS⟩
    have hA := isComplexAnalyticSubset_cosupport_along hI hN hd
    have hthin := thin_inter_remainingComponents hN hA
    have hnzR := isNonzeroAlongAt_of_thin_cosupport (d := L.d) hI (by
      intro O hO hsub
      apply hthin O hO
      intro z hzO
      have he := (remainder_actual_stalk_and_all_orders L 0 hN hI .refl trivial z hzO.2).2 L.d
      exact ⟨he.mp (hsub hzO), hzO.2⟩) hxR
    obtain ⟨g, hg, hfreq⟩ := hnzR
    apply hz
    refine ⟨g, hg, hfreq.mono fun y hy => ?_⟩
    rw [remainingComponents_eq_diff_selected hN] at hy
    exact ⟨hy.1.1, hy.2⟩

theorem not_isNonzeroAlongAt_iff_vanishing_stalk {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) (x : X) :
    ¬ IsNonzeroAlongAt N I x ↔ ∀ g, I.mem x g → (vanishingIdeal (n := n) N).mem x g := by
  constructor
  · intro hz g hg
    refine ⟨RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg, ?_⟩
    have hn : ∀ᶠ y in 𝓝 x, ¬ (y ∈ N ∧ g y ≠ 0) :=
      Filter.not_frequently.mp (fun hf => hz ⟨g, hg, hf⟩)
    exact hn.mono fun y hy hyN => by_contra fun hne => hy ⟨hyN, hne⟩
  · intro hz ⟨g, hg, hfreq⟩
    obtain ⟨y, ⟨hyN, hne⟩, hzero⟩ := (hfreq.and_eventually (hz g hg).2).exists
    exact hne (hzero hyN)

theorem isNonzeroAlongAt_pullback_val_iff {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) (U : Opens X) (p : U) :
    IsNonzeroAlongAt ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I) p ↔
      IsNonzeroAlongAt N I (p : X) := by
  constructor
  · rintro ⟨g, hg, hfreq⟩
    refine ⟨extendOpens U g, (mem_pullback_val_iff U hI).mp hg, ?_⟩
    have hf : ∃ᶠ q : U in 𝓝 p, (q : X) ∈ N ∧ extendOpens U g q ≠ 0 := by
      simpa only [mem_preimage, extendOpens_val] using hfreq
    have hm : ∃ᶠ y in Filter.map (Subtype.val : U → X) (𝓝 p), y ∈ N ∧ extendOpens U g y ≠ 0 :=
      Filter.frequently_map.mpr hf
    have hmap : Filter.map (Subtype.val : U → X) (𝓝 p) = 𝓝 (p : X) :=
      U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p
    rwa [hmap] at hm
  · rintro ⟨g, hg, hfreq⟩
    refine ⟨g ∘ Subtype.val, comp_val_mem_pullback_val U hI hg, ?_⟩
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p] at hfreq
    exact Filter.frequently_map.mp hfreq

private theorem nonzero_pullback_diffeo
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {N : Set Y} {I : GermIdeal n Y} (hI : I.IsCoherent) {p : X}
    (hp : IsNonzeroAlongAt N I (Φ p)) :
    IsNonzeroAlongAt (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ I) p := by
  obtain ⟨g, hg, hf⟩ := hp
  refine ⟨g ∘ Φ, BlowupBiholomorphismLift.comp_mem_pullback_diffeo Φ hI hg, ?_⟩
  have hm : Filter.map (Φ : X → Y) (𝓝 p) = 𝓝 (Φ p) := Φ.toHomeomorph.map_nhds_eq p
  rw [← hm] at hf
  exact Filter.frequently_map.mp hf

theorem isNonzeroAlongAt_pullback_diffeo_iff
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {N : Set Y} {I : GermIdeal n Y} (hI : I.IsCoherent) (p : X) :
    IsNonzeroAlongAt (Φ ⁻¹' N) (GermIdeal.pullback (m := n) Φ I) p ↔
      IsNonzeroAlongAt N I (Φ p) := by
  refine ⟨fun hp => ?_, nonzero_pullback_diffeo Φ hI⟩
  have h := nonzero_pullback_diffeo Φ.symm
    (GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hI)
    (p := Φ p) (by simpa only [Diffeomorph.symm_apply_apply] using hp)
  have hi := (GermIdealTotalTransform.pullback_comp Φ.contMDiff Φ.symm.contMDiff hI).symm
  rw [show (Φ : X → Y) ∘ (Φ.symm : Y → X) = id from funext Φ.apply_symm_apply,
    BlowupControlledTransform.pullback_id hI] at hi
  rw [hi, MarkedIdealTowerTransport.symm_preimage_preimage] at h
  exact h

private theorem mem_remaining_iff (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) (x : X) :
    x ∈ remainingComponents (n := n) L.N L.cosupp ↔
      x ∈ L.N ∧ IsNonzeroAlongAt L.N L.ideal x := by
  rw [remainingComponents_eq_diff_selected hN]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    by_contra hz
    exact hs ((selectedComponents_iff_not_isNonzeroAlongAt L hN hI hd hx).mpr hz)
  · rintro ⟨hx, hnz⟩
    exact ⟨hx, fun hs => (selectedComponents_iff_not_isNonzeroAlongAt L hN hI hd hx).mp hs hnz⟩

theorem remainingComponents_pullback_val (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) (U : Opens X) :
    remainingComponents (n := n) (MarkedIdeal.pullback (Subtype.val : U → X) L).N
        (MarkedIdeal.pullback (Subtype.val : U → X) L).cosupp =
      (Subtype.val : U → X) ⁻¹' remainingComponents (n := n) L.N L.cosupp := by
  let A := MarkedIdeal.pullback (Subtype.val : U → X) L
  have haN : IsClosedSubmanifold n A.N := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have haI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  ext p
  rw [mem_remaining_iff (X := CMfd.of (n := n) U) A haN haI hd, mem_preimage, mem_remaining_iff L hN hI hd]
  exact and_congr_right fun _ => isNonzeroAlongAt_pullback_val_iff hI U p

theorem remainingComponents_pullback_diffeo
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (L : MarkedIdeal n Y) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) :
    remainingComponents (n := n) (MarkedIdeal.pullback Φ L).N (MarkedIdeal.pullback Φ L).cosupp =
      Φ ⁻¹' remainingComponents (n := n) L.N L.cosupp := by
  let A := MarkedIdeal.pullback Φ L
  have haN : IsClosedSubmanifold n A.N :=
    (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff Φ).mpr hN
  have haI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hI
  ext p
  rw [mem_remaining_iff A haN haI hd, mem_preimage, mem_remaining_iff L hN hI hd]
  exact and_congr_right fun _ => isNonzeroAlongAt_pullback_diffeo_iff Φ hI p

theorem contactRemainderMarked_pullback_val (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) (U : Opens X) :
    contactRemainderMarked (MarkedIdeal.pullback (Subtype.val : U → X) L) k =
      MarkedIdeal.pullback (Subtype.val : U → X) (contactRemainderMarked L k) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact remainingComponents_pullback_val L hN hI hd U
  · change List.replicate k ∅ ++ (L.E.map ((Subtype.val : U → X) ⁻¹' ·)).drop k =
      (List.replicate k ∅ ++ L.E.drop k).map ((Subtype.val : U → X) ⁻¹' ·)
    simp only [List.map_append, List.map_replicate, preimage_empty, List.map_drop]
  · rfl
  · rfl

theorem contactRemainderMarked_pullback_diffeo
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (L : MarkedIdeal n Y) (k : ℕ) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) :
    contactRemainderMarked (MarkedIdeal.pullback Φ L) k =
      MarkedIdeal.pullback Φ (contactRemainderMarked L k) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact remainingComponents_pullback_diffeo Φ L hN hI hd
  · change List.replicate k ∅ ++ (L.E.map (Φ ⁻¹' ·)).drop k =
      (List.replicate k ∅ ++ L.E.drop k).map (Φ ⁻¹' ·)
    simp only [List.map_append, List.map_replicate, preimage_empty, List.map_drop]
  · rfl
  · rfl

private def paddedRemainder (L : MarkedIdeal n X) (k : ℕ) : MarkedIdeal n X :=
  { contactRemainderMarked L 0 with E := List.replicate k ∅ ++ L.E }

private theorem paddedRemainder_pullback_diffeo
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (L : MarkedIdeal n Y) (k : ℕ) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) :
    paddedRemainder (MarkedIdeal.pullback Φ L) k = MarkedIdeal.pullback Φ (paddedRemainder L k) := by
  have h := contactRemainderMarked_pullback_diffeo Φ L 0 hN hI hd
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change (contactRemainderMarked (MarkedIdeal.pullback Φ L) 0).N =
      (MarkedIdeal.pullback Φ (contactRemainderMarked L 0)).N
    exact congrArg MarkedIdeal.N h
  · change List.replicate k ∅ ++ L.E.map (Φ ⁻¹' ·) =
      (List.replicate k ∅ ++ L.E).map (Φ ⁻¹' ·)
    simp only [List.map_append, List.map_replicate, preimage_empty]
  · rfl
  · rfl

theorem exists_contact_remainder_glueing (K : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n K.N) (hI : K.ideal.IsCoherent) (hd : 1 ≤ K.d)
    (x : X) (hx : x ∈ K.cosupp) (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong K.N K.ideal K.d V v) (hxV : x ∈ V) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d u v,
      x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set X) ⊆ U ∩ V ∧ (G.cod : Set X) ⊆ U ∩ V ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
        IsGeoTestTower (stepOneMarked K.N K.ideal K.d) T →
        ∃ Φ, IsGlueingLiftAlong G T Φ ∧
          (let A := contactMarkedKept ({K with E := []} : MarkedIdeal n X) u T (openPreimage T G.cod)
           let B := contactMarkedKept ({K with E := []} : MarkedIdeal n X) v T (openPreimage T G.dom)
           MarkedIdeal.pullback Φ A = B ∧
             ∀ k, MarkedIdeal.pullback Φ (paddedRemainder (X := CMfd.of (n := n) (openPreimage T G.cod)) A k) =
               paddedRemainder (X := CMfd.of (n := n) (openPreimage T G.dom)) B k) ∧
          ∀ p : openPreimage T G.dom,
            (p : Y) ∈ (geoTransformAlong (stepOneMarked K.N K.ideal K.d) T).cosupp → (Φ p : Y) = p := by
  obtain ⟨G, hxW, hsub, htriv⟩ := exists_glueingDataAlong_trivial_subset hI hN hd hx hu hxU hv hxV
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  have hdom : (G.dom : Set X) ⊆ U ∩ V := fun p hp => hsub hp.1
  have hcod : (G.cod : Set X) ⊆ U ∩ V := fun p hp => hsub hp.1
  refine ⟨G, hxd, hxc, hdom, hcod, fun T hT => ?_⟩
  obtain ⟨Φ, hL, _, hS, _, hfix⟩ := exists_isGlueingLiftAlong_coeffHom G hI hN hd htriv T hT
  let K0 : MarkedIdeal n X := {K with E := []}
  let A := contactMarkedKept K0 u T (openPreimage T G.cod)
  let B := contactMarkedKept K0 v T (openPreimage T G.dom)
  have hT0 : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong K0)) T := hT
  have hTa : IsGeoTestTower K0 T := ((coeff_homAlong_wEquiv K0 hN hI hd).2 T).1.mp hT0
  have hAN : IsClosedSubmanifold n A.N :=
    isClosedSubmanifold_strictAlong_stage_of_le K0 hN hI hd U hu T hTa (openPreimage T G.cod)
      (fun p hp => (hcod hp).1)
  have hAI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K0 hI hN u T hT0)
  have hAd : 1 ≤ A.d := one_le_coeffMarkedAlong_d _
  have heq : MarkedIdeal.pullback Φ A = B := hS
  refine ⟨Φ, hL, ⟨heq, fun k => ?_⟩, hfix⟩
  have ht := paddedRemainder_pullback_diffeo
    (X := CMfd.of (n := n) (openPreimage T G.dom))
    (Y := CMfd.of (n := n) (openPreimage T G.cod)) Φ A k hAN hAI hAd
  rw [heq] at ht
  exact ht.symm

private theorem contactMarkedKept_emptyE (K : MarkedIdeal n X) (w : X → ℂ)
    (T : BlowupTower X Y) (O : Opens Y) :
    contactMarkedKept ({K with E := []} : MarkedIdeal n X) w T O =
      ({contactMarkedKept K w T O with E := (contactMarkedKept K w T O).E.drop K.E.length} : MarkedIdeal n O) := by
  change MarkedIdeal.pullback (Subtype.val : O → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked K.N K.ideal K.d) T))
        (strictAlong T (K.N ∩ {x | w x = 0}))) = _
  rw [geoTransformAlong_coeffHom_dropE K T]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change ((geoTransformAlong (barMarked K) T).E.drop K.E.length).map ((Subtype.val : O → Y) ⁻¹' ·) =
      ((geoTransformAlong (barMarked K) T).E.map ((Subtype.val : O → Y) ⁻¹' ·)).drop K.E.length
    exact List.map_drop
  · rfl
  · rfl

theorem contactRemainderMarked_contactMarkedKept_emptyE (K : MarkedIdeal n X) (w : X → ℂ)
    (T : BlowupTower X Y) (O : Opens Y) :
    contactRemainderMarked (contactMarkedKept K w T O) K.E.length =
      paddedRemainder (X := CMfd.of (n := n) O)
        (contactMarkedKept ({K with E := []} : MarkedIdeal n X) w T O) K.E.length := by
  rw [contactMarkedKept_emptyE K w T O]
  rfl

theorem exists_actual_chosen_contact_remainder_glueing (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (x y : X) (hx : x ∈ K.cosupp) (hy : y ∈ K.cosupp)
    (hxy : x ∈ (tangentChoice K y).1) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d (tangentChoice K x).2 (tangentChoice K y).2,
      x ∈ G.dom ∧ x ∈ G.cod ∧
      (G.dom : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      (G.cod : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      ∀ j : ℕ, ∃ Φ, IsGlueingLiftAlong G (head R j) Φ ∧
        MarkedIdeal.pullback Φ
          (contactRemainderMarked
            (contactMarkedKept K (tangentChoice K x).2 (head R j) (openPreimage (head R j) G.cod)) K.E.length) =
          contactRemainderMarked
            (contactMarkedKept K (tangentChoice K y).2 (head R j) (openPreimage (head R j) G.dom)) K.E.length ∧
        ∀ p : openPreimage (head R j) G.dom,
          (p : (split R j).1) ∈ (geoTransformAlong K (head R j)).cosupp → (Φ p : (split R j).1) = p := by
  have hN := hK.isWellFormed.isClosedSubmanifold_N
  have hI := hK.isWellFormed.isCoherent
  have hd := hK.one_le_d
  have hW := coeff_homAlong_wEquiv K hN hI hd
  have hxbar : x ∈ (geoTransformAlong (barMarked K) .refl).cosupp := by
    rw [(hW.2 .refl).2 trivial]
    exact hx
  have hybar : y ∈ (geoTransformAlong (barMarked K) .refl).cosupp := by
    rw [(hW.2 .refl).2 trivial]
    exact hy
  obtain ⟨hxU, hu⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hd hmax .refl trivial hxbar)
  obtain ⟨_, hv⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hd hmax .refl trivial hybar)
  let U : Opens X := ⟨(tangentChoice K x).1, hu.isOpen⟩
  let V : Opens X := ⟨(tangentChoice K y).1, hv.isOpen⟩
  obtain ⟨G, hxd, hxc, hdom, hcod, hglue⟩ :=
    exists_contact_remainder_glueing K hN hI hd x hx U V hu hxU hv hxy
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  refine ⟨G, hxd, hxc, hdom, hcod, fun j => ?_⟩
  have hhead := ((isGeoTestTower_iff_head_tail (barMarked K) R j).mp hb.1).1
  have hstep := isGeoTestTower_stepOneMarked_of_coeffHom K (head R j) hhead
  obtain ⟨Φ, hL, hmodels, hfix⟩ := hglue (head R j) hstep
  obtain ⟨_, hrem⟩ := hmodels
  refine ⟨Φ, hL, ?_, fun p hp => ?_⟩
  · rw [contactRemainderMarked_contactMarkedKept_emptyE, contactRemainderMarked_contactMarkedKept_emptyE]
    exact hrem K.E.length
  · apply hfix p
    rw [cosupp_geoTransformAlong_stepOneMarked K (head R j), (hW.2 (head R j)).2 hhead]
    exact hp

end
end Hironaka.HironakaStepOneZeroContactRemainderGlueing
