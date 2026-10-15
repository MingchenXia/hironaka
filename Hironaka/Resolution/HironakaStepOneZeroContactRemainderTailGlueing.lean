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
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing
import Hironaka.Invariant.StepOneTangentChange

/-!
# Genuine actual zero-contact remainder tails and literal historical records

The actual selected-component complement and whole remainder record commute
with genuine contact biholomorphisms. The SAME actual restricted original tails
are internally produced genuine remainder test towers and genuinely isomorphic,
with ENTIRE controlled records at the endpoint and EVERY literal head.
Original domain3/max/literal canonical Step1 inputs produce their chosen tangent
directions, tests and one joint glueing datum for every literal split.
The final producer identifies the SAME original boundary-kept contact remainder
with the truly padded empty-initial-boundary model. ALL actual exceptional entries
are retained; every length condition and padded-test condition is internal.
Private output propositions abbreviate ONLY conclusions, never caller inputs.
Enlarged remainder canonicality, deeper zero histories, whole zero/General3
analytic superlevels and general noncompact G3 termination remain OPEN.
Mathematics.tex was written first. This is an OWN OFFLIB checkpoint; formal
write-set registration and native target build are pending root recovery.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactRemainderTailGlueing
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  HironakaStepOneSpecialAnalyticLoci HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderTestTower
  HironakaStepOneZeroContactRemainderGlueing GlobalComponents
  BlowupTowerIsomorphism StepOneTangentChange BlowupTowerSplitIso
  ContactStageInvDomain ContactStageKept ContactIndependenceAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  NormalCrossings NormalCrossingsComparison DropMembers
  CoefficientIdealRestriction TangentDirectionAlong ContactEquivalenceAlong MaximalOrderStepOneB
  StepOneValue StepOneLowerDomain CanonicalCentres StepOneRegime
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem selected_subset (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) :
    selectedComponents (n := n) L.N L.cosupp ⊆ L.N := by
  rintro x ⟨B, ⟨hB, _⟩, hxB⟩
  exact subset_of_mem_globalComponents
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hB hxB

theorem selectedComponents_pullback_diffeo
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) :
    selectedComponents (n := n) (MarkedIdeal.pullback Φ L).N (MarkedIdeal.pullback Φ L).cosupp =
      Φ ⁻¹' selectedComponents (n := n) L.N L.cosupp := by
  let P := MarkedIdeal.pullback Φ L
  have hPN : IsClosedSubmanifold n P.N := (isClosedSubmanifold_preimage_iff Φ).mpr hN
  have hPI : P.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hI
  ext p
  by_cases hp : p ∈ P.N
  · rw [selectedComponents_iff_not_isNonzeroAlongAt P hPN hPI hd hp, mem_preimage,
      selectedComponents_iff_not_isNonzeroAlongAt L hN hI hd hp]
    exact not_congr (isNonzeroAlongAt_pullback_diffeo_iff Φ hI p)
  · have hps : p ∉ selectedComponents (n := n) P.N P.cosupp := fun hs => hp (selected_subset P hPN hs)
    have hqs : Φ p ∉ selectedComponents (n := n) L.N L.cosupp := fun hs => hp (selected_subset L hN hs)
    exact iff_of_false hps hqs

theorem mem_remainderOpen_pullback_diffeo_iff
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) (q : X') :
    q ∈ remainderOpen (MarkedIdeal.pullback Φ L) ((isClosedSubmanifold_preimage_iff Φ).mpr hN) ↔
      Φ q ∈ remainderOpen L hN := by
  change q ∉ selectedComponents (n := n) (MarkedIdeal.pullback Φ L).N
    (MarkedIdeal.pullback Φ L).cosupp ↔ Φ q ∉ selectedComponents (n := n) L.N L.cosupp
  rw [selectedComponents_pullback_diffeo Φ L hN hI hd]
  rfl

theorem remainderOpen_pullback_record
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (L : MarkedIdeal n X) (k : ℕ) (hN : IsClosedSubmanifold n L.N)
    (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d) :
    let P := MarkedIdeal.pullback Φ L
    let G := remainderOpen L hN
    let G' := remainderOpen P ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
    let Ψ := diffeoOpens Φ G' G (mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd)
    MarkedIdeal.pullback Ψ (MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)) =
      MarkedIdeal.pullback (Subtype.val : G' → X') (contactRemainderMarked P k) := by
  dsimp only
  let G := remainderOpen L hN
  let G' := remainderOpen (MarkedIdeal.pullback Φ L) ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
  let Ψ := diffeoOpens Φ G' G (mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd)
  have hR : (contactRemainderMarked L k).ideal.IsCoherent := hI
  rw [contactRemainderMarked_pullback_diffeo Φ L k hN hI hd]
  have h1 := pullback_pullback_of_comp (n := n) hR contMDiff_subtype_val Ψ.contMDiff
    (d := fun q : G' => Φ q) (fun _ => rfl)
  have h2 := pullback_pullback_of_comp (n := n) hR Φ.contMDiff contMDiff_subtype_val
    (d := fun q : G' => Φ q) (fun _ => rfl)
  exact h1.trans h2.symm


theorem remainderOpen_test_tower_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hχ : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower L T) :
    let P := MarkedIdeal.pullback Φ L
    let G := remainderOpen L hN
    let G' := remainderOpen P ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
    let hG := mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd
    let Ψ := diffeoOpens Φ G' G hG
    let χG := diffeoOpens χ (openPreimage T' G') (openPreimage T G)
      (isTowerIso_mem_openPreimage_iff hχ hG)
    let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)
    let A' := MarkedIdeal.pullback (Subtype.val : G' → X') (contactRemainderMarked P k)
    IsTowerIso Ψ (restrict G' T') (restrict G T) χG ∧
      IsGeoTestTower A (restrict G T) ∧ IsGeoTestTower A' (restrict G' T') ∧
      geoTransformAlong A' (restrict G' T') = MarkedIdeal.pullback χG (geoTransformAlong A (restrict G T)) := by
  dsimp only
  let P := MarkedIdeal.pullback Φ L
  let G := remainderOpen L hN
  let G' := remainderOpen P ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
  let hG := mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd
  let Ψ := diffeoOpens Φ G' G hG
  let χG := diffeoOpens χ (openPreimage T' G') (openPreimage T G)
    (isTowerIso_mem_openPreimage_iff hχ hG)
  let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)
  let A' := MarkedIdeal.pullback (Subtype.val : G' → X') (contactRemainderMarked P k)
  have hIso : IsTowerIso Ψ (restrict G' T') (restrict G T) χG :=
    isTowerIso_restrictOpens hG hχ (isTowerIso_mem_openPreimage_iff hχ hG)
  have hrec : MarkedIdeal.pullback Ψ A = A' := remainderOpen_pullback_record Φ L k hN hI hd
  have hAN : IsClosedSubmanifold n A.N := BlowupRestrictOpen.isClosedSubmanifold_preimage_val
    (isClosedSubmanifold_remainingComponents hN L.cosupp) G
  have hAI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hAT : IsGeoTestTower A (restrict G T) := (remainder_restricted_isGeoTestTower L k hk hN hI T hT).1
  have hA'T := (IsTowerIso.isGeoTestTower_iff Ψ hAN hAI hIso).mpr hAT
  have htrans := IsTowerIso.geoTransformAlong_eq Ψ hAN hAI hIso hAT
  rw [hrec] at hA'T htrans
  exact ⟨hIso, hAT, hA'T, htrans⟩

theorem remainderOpen_prefix_transport
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hχ : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower L T) :
    let P := MarkedIdeal.pullback Φ L
    let G := remainderOpen L hN
    let G' := remainderOpen P ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
    let hG := mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd
    let Ψ := diffeoOpens Φ G' G hG
    let χG := diffeoOpens χ (openPreimage T' G') (openPreimage T G)
      (isTowerIso_mem_openPreimage_iff hχ hG)
    let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)
    let A' := MarkedIdeal.pullback (Subtype.val : G' → X') (contactRemainderMarked P k)
    ∀ j : ℕ, ∃ χj,
      IsTowerIso Ψ (head (restrict G' T') j) (head (restrict G T) j) χj ∧
      IsTowerIso χj (tail (restrict G' T') j) (tail (restrict G T) j) χG ∧
      geoTransformAlong A' (head (restrict G' T') j) =
        MarkedIdeal.pullback χj (geoTransformAlong A (head (restrict G T) j)) := by
  dsimp only
  let P := MarkedIdeal.pullback Φ L
  let G := remainderOpen L hN
  let G' := remainderOpen P ((isClosedSubmanifold_preimage_iff Φ).mpr hN)
  let hG := mem_remainderOpen_pullback_diffeo_iff Φ L hN hI hd
  let Ψ := diffeoOpens Φ G' G hG
  let χG := diffeoOpens χ (openPreimage T' G') (openPreimage T G)
    (isTowerIso_mem_openPreimage_iff hχ hG)
  let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)
  let A' := MarkedIdeal.pullback (Subtype.val : G' → X') (contactRemainderMarked P k)
  obtain ⟨hIso, hAT, _, _⟩ := remainderOpen_test_tower_transport Φ L k hk hN hI hd T' T χ hχ hT
  have hrec : MarkedIdeal.pullback Ψ A = A' := remainderOpen_pullback_record Φ L k hN hI hd
  have hAN : IsClosedSubmanifold n A.N := BlowupRestrictOpen.isClosedSubmanifold_preimage_val
    (isClosedSubmanifold_remainingComponents hN L.cosupp) G
  have hAI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  intro j
  obtain ⟨χj, hhead, htail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso j
  have ht := ((isGeoTestTower_iff_head_tail A (restrict G T) j).mp hAT).1
  have heq := IsTowerIso.geoTransformAlong_eq Ψ hAN hAI hhead ht
  rw [hrec] at heq
  exact ⟨χj, hhead, htail, heq⟩


theorem empty_pad_geoTransformAlong (M : MarkedIdeal n X) (k : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong ({M with E := List.replicate k ∅ ++ M.E} : MarkedIdeal n X) T =
        {geoTransformAlong M T with E := List.replicate k ∅ ++ (geoTransformAlong M T).E}
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [geoTransformAlong_step, empty_pad_geoTransformAlong M k T, geoTransformAlong_step,
        NormalCrossingsComparison.geoTransform_withE]
      rw [geoTransform_E, List.map_append, List.map_replicate]
      have he : BlowupStrictSubmanifold.geoStrictTransform π C ∅ = ∅ := by
        simp [BlowupStrictSubmanifold.geoStrictTransform]
      simp only [he, List.append_assoc]

theorem empty_pad_isGeoTestTower (M : MarkedIdeal n X) (k : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      IsGeoTestTower ({M with E := List.replicate k ∅ ++ M.E} : MarkedIdeal n X) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      refine ⟨empty_pad_isGeoTestTower M k T hT.1, ?_⟩
      rw [empty_pad_geoTransformAlong M k T]
      refine ⟨hT.2.1, hT.2.2.1, ?_⟩
      apply hasNormalCrossings_of_forall_disjoint hT.2.2.2
      intro F hF hn
      rcases List.mem_append.mp hF with hF | hF
      · rw [List.eq_of_mem_replicate hF]
        exact disjoint_empty _
      · exact False.elim (hn hF)

private theorem old_history_remainder_eq (K : MarkedIdeal n X) (w : X → ℂ)
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

private def contactRemainderTailOutput (K : MarkedIdeal n X) {u v : X → ℂ}
    (G : GlueingDataAlong K.N K.ideal K.d u v) {Y Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z) : Prop :=
        ∃ Φ χ, IsGlueingLiftAlong G T₀ Φ ∧
        ∃ hχ : IsTowerIso Φ (restrict (openPreimage T₀ G.dom) T₁)
          (restrict (openPreimage T₀ G.cod) T₁) χ,
        let A := contactMarkedKept ({K with E := []} : MarkedIdeal n X) u T₀ (openPreimage T₀ G.cod)
        let B := contactMarkedKept ({K with E := []} : MarkedIdeal n X) v T₀ (openPreimage T₀ G.dom)
        MarkedIdeal.pullback Φ A = B ∧
        ∃ (hAN : IsClosedSubmanifold n A.N) (hAI : A.ideal.IsCoherent) (hdA : 1 ≤ A.d),
        IsGeoTestTower A (restrict (openPreimage T₀ G.cod) T₁) ∧
        let O := remainderOpen (X := CMfd.of (n := n) (openPreimage T₀ G.cod)) A hAN
        let O' := remainderOpen (X := CMfd.of (n := n) (openPreimage T₀ G.dom))
          (MarkedIdeal.pullback Φ A) ((isClosedSubmanifold_preimage_iff Φ).mpr hAN)
        let hO := mem_remainderOpen_pullback_diffeo_iff Φ A hAN hAI hdA
        let Ψ := diffeoOpens Φ O' O hO
        let T := restrict (openPreimage T₀ G.cod) T₁
        let T' := restrict (openPreimage T₀ G.dom) T₁
        let χO := diffeoOpens χ (openPreimage T' O') (openPreimage T O)
          (isTowerIso_mem_openPreimage_iff hχ hO)
        let R := MarkedIdeal.pullback (Subtype.val : O → openPreimage T₀ G.cod) (contactRemainderMarked A 0)
        let R' := MarkedIdeal.pullback (Subtype.val : O' → openPreimage T₀ G.dom)
          (contactRemainderMarked (MarkedIdeal.pullback Φ A) 0)
        IsTowerIso Ψ (restrict O' T') (restrict O T) χO ∧
        IsGeoTestTower R (restrict O T) ∧ IsGeoTestTower R' (restrict O' T') ∧
        geoTransformAlong R' (restrict O' T') = MarkedIdeal.pullback χO (geoTransformAlong R (restrict O T)) ∧
        (∀ j : ℕ, ∃ χj,
          IsTowerIso Ψ (head (restrict O' T') j) (head (restrict O T) j) χj ∧
          IsTowerIso χj (tail (restrict O' T') j) (tail (restrict O T) j) χO ∧
          geoTransformAlong R' (head (restrict O' T') j) =
            MarkedIdeal.pullback χj (geoTransformAlong R (head (restrict O T) j))) ∧
        ∀ p : openPreimage T₁ (openPreimage T₀ G.dom),
          (p : Z) ∈ (geoTransformAlong (stepOneMarked K.N K.ideal K.d) (T₀.append T₁)).cosupp →
            (χ p : Z) = p

theorem exists_contact_remainder_tail_glueing (K : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n K.N) (hI : K.ideal.IsCoherent) (hd : 1 ≤ K.d)
    (x : X) (hx : x ∈ K.cosupp) (U V : Opens X) {u v : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong K.N K.ideal K.d V v) (hxV : x ∈ V) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d u v,
      x ∈ G.dom ∧ x ∈ G.cod ∧ (G.dom : Set X) ⊆ U ∩ V ∧ (G.cod : Set X) ⊆ U ∩ V ∧
      ∀ {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z),
        IsGeoTestTower (stepOneMarked K.N K.ideal K.d) (T₀.append T₁) →
        contactRemainderTailOutput K G T₀ T₁ := by
  obtain ⟨G, hxd, hxc, hdom, hcod, hglue⟩ :=
    contact_independence_along_tail_subset hI hN hd hx hu hxU hv hxV
  refine ⟨G, hxd, hxc, hdom, hcod, fun T₀ T₁ hT => ?_⟩
  dsimp only [contactRemainderTailOutput]
  obtain ⟨Φ, χ, hL, hχ, heq, hfix⟩ := hglue T₀ T₁ hT
  let K0 : MarkedIdeal n X := {K with E := []}
  let A := contactMarkedKept K0 u T₀ (openPreimage T₀ G.cod)
  let B := contactMarkedKept K0 v T₀ (openPreimage T₀ G.dom)
  have hT₀ := ((isGeoTestTower_append_iff (stepOneMarked K.N K.ideal K.d) T₀ T₁).mp hT).1
  have hT₀a : IsGeoTestTower K0 T₀ := ((coeff_homAlong_wEquiv K0 hN hI hd).2 T₀).1.mp hT₀
  have hAN : IsClosedSubmanifold n A.N := isClosedSubmanifold_strictAlong_stage_of_le
    K0 hN hI hd U hu T₀ hT₀a (openPreimage T₀ G.cod) (fun p hp => (hcod hp).1)
  have hAI : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K0 hI hN u T₀ hT₀)
  have hdA : 1 ≤ A.d := one_le_coeffMarkedAlong_d _
  have hAT : IsGeoTestTower A (restrict (openPreimage T₀ G.cod) T₁) :=
    (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K0 hN hI hd U hu T₀ T₁ hT
      (openPreimage T₀ G.cod) (fun p hp => (hcod hp).1)).1
  have hcalc := remainderOpen_test_tower_transport Φ A 0 (Nat.zero_le _) hAN hAI hdA
    (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ hχ hAT
  have hpref := remainderOpen_prefix_transport Φ A 0 (Nat.zero_le _) hAN hAI hdA
    (restrict (openPreimage T₀ G.dom) T₁) (restrict (openPreimage T₀ G.cod) T₁) χ hχ hAT
  refine ⟨Φ, χ, hL, hχ, heq, hAN, hAI, hdA, hAT, ?_⟩
  exact ⟨hcalc.1, hcalc.2.1, hcalc.2.2.1, hcalc.2.2.2, hpref, hfix⟩


theorem exists_actual_chosen_contact_remainder_tail_glueing (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (x y : X) (hx : x ∈ K.cosupp) (hy : y ∈ K.cosupp)
    (hxy : x ∈ (tangentChoice K y).1) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d (tangentChoice K x).2 (tangentChoice K y).2,
      x ∈ G.dom ∧ x ∈ G.cod ∧
      (G.dom : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      (G.cod : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      ∀ j : ℕ, contactRemainderTailOutput K G (head R j) (tail R j) := by
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
    exists_contact_remainder_tail_glueing K hN hI hd x hx U V hu hxU hv hxy
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hstep := isGeoTestTower_stepOneMarked_of_coeffHom K R hb.1
  refine ⟨G, hxd, hxc, hdom, hcod, fun j => ?_⟩
  apply hglue (head R j) (tail R j)
  rw [head_append_tail]
  exact hstep


private def oldHistoryTailOutput (K : MarkedIdeal n X) {u v : X → ℂ}
    (G : GlueingDataAlong K.N K.ideal K.d u v) {Y Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z) : Prop :=
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
          (p : Z) ∈ (geoTransformAlong (stepOneMarked K.N K.ideal K.d) (T₀.append T₁)).cosupp →
            (χ p : Z) = p

private theorem old_history_tail_of_data (K : MarkedIdeal n X) {u v : X → ℂ}
    (G : GlueingDataAlong K.N K.ideal K.d u v) {Z : CMfd.{u} n}
    (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z)
    (hdata : contactRemainderTailOutput K G T₀ T₁) : oldHistoryTailOutput K G T₀ T₁ := by
  dsimp only [contactRemainderTailOutput] at hdata
  obtain ⟨Φ, χ, hL, hχ, hmodel, hAN, hAI, hdA, hAT, hrest⟩ := hdata
  let A0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) u T₀ (openPreimage T₀ G.cod)
  let B0 := contactMarkedKept ({K with E := []} : MarkedIdeal n X) v T₀ (openPreimage T₀ G.dom)
  let A : MarkedIdeal n (openPreimage T₀ G.cod) := {A0 with E := List.replicate K.E.length ∅ ++ A0.E}
  have hpad : MarkedIdeal.pullback Φ A =
      ({B0 with E := List.replicate K.E.length ∅ ++ B0.E} : MarkedIdeal n (openPreimage T₀ G.dom)) := by
    rw [pullback_replicate_empty, hmodel]
  have hi := old_history_remainder_eq K u T₀ (openPreimage T₀ G.cod)
  have hi' : contactRemainderMarked (contactMarkedKept K v T₀ (openPreimage T₀ G.dom)) K.E.length =
      contactRemainderMarked (MarkedIdeal.pullback Φ A) K.E.length := by
    rw [hpad]
    exact old_history_remainder_eq K v T₀ (openPreimage T₀ G.dom)
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
  dsimp only [oldHistoryTailOutput]
  refine ⟨Φ, χ, hL, hχ, hmodel, hAN, hAI, hdA, hAT, hi, hi', ?_⟩
  exact ⟨hcalc.1, hcalc.2.1, hcalc.2.2.1, hcalc.2.2.2, hpref, hrest.2.2.2.2.2⟩

theorem exists_actual_chosen_contact_old_history_tail_glueing (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (x y : X) (hx : x ∈ K.cosupp) (hy : y ∈ K.cosupp)
    (hxy : x ∈ (tangentChoice K y).1) :
    ∃ G : GlueingDataAlong K.N K.ideal K.d (tangentChoice K x).2 (tangentChoice K y).2,
      x ∈ G.dom ∧ x ∈ G.cod ∧
      (G.dom : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      (G.cod : Set X) ⊆ (tangentChoice K x).1 ∩ (tangentChoice K y).1 ∧
      ∀ j : ℕ, oldHistoryTailOutput K G (head R j) (tail R j) := by
  obtain ⟨G, hxd, hxc, hdom, hcod, hdata⟩ :=
    exists_actual_chosen_contact_remainder_tail_glueing hn K hK hmax R hcan x y hx hy hxy
  exact ⟨G, hxd, hxc, hdom, hcod, fun j => old_history_tail_of_data K G (head R j) (tail R j) (hdata j)⟩

end
end Hironaka.HironakaStepOneZeroContactRemainderTailGlueing
