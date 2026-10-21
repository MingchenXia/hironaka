/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFirstMeetingPrefixUniqueness

/-!
# Independent actual smooth source stopping on the literal pulled marked record

The same embedded target prefix is compared with a separately stopped source
canonical history.  Nonempty pulled carriers supply a true source maximum
encounter; empty carriers give genuine all-empty canonical histories.
The source marked record is exactly `b * M`, with no identification of a
singular pulled ideal with a separately reduced vanishing ideal.

Blueprint: `hironaka-original-independent-stopped-source-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalIndependentStoppedSource

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres EmbeddedFromResolution
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalCompactTerminal HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaSmoothSubmersionOriginalTerminalSubmersion HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalFirstMeetingPrefixUniqueness HironakaOriginalStoppedPrefixSmoothComparison
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNormalCrossings

open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.ResolutionInvariantExt (IsEmptyTower)
open _root_.Hironaka.ResolutionDriver (maxLocus)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E F : CMfd.{u} m}

/-- Exact cosupport persistence over any original open avoided by all
actual centres, with no reduced-ideal assumption. -/
theorem mem_cosupp_iff_of_centresAvoid (M : MarkedIdeal n X) (hM : M.IsWellFormed) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D), IsGeoTestTower M T →
      ∀ (O : Opens X), CentresAvoid O T → ∀ z : D, T.proj z ∈ O →
        (z ∈ (geoTransformAlong M T).cosupp ↔ T.proj z ∈ M.cosupp)
  | _, .refl, _, _, _, _, _ => Iff.rfl
  | _, .step T C π hπ, ht, O, ha, z, hz => by
    have hzC : π z ∉ C := fun hzC => Set.disjoint_left.mp ha.2 hzC hz
    obtain ⟨hN,hI⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hM.isClosedSubmanifold_N hM.isCoherent T ht.1
    rw [geoTransformAlong_step, TransformOffCentre.mem_cosupp_geoTransform_iff _ hN.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hπ hzC,
      mem_cosupp_iff_of_centresAvoid M hM T ht.1 O ha.1 (π z) hz]
    rfl

private theorem transformed_cosupp_empty (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (he : M.cosupp = ∅) (T : BlowupTower X D) (ht : IsGeoTestTower M T) :
    (geoTransformAlong M T).cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := TransformOffCentre.cosupp_geoTransformAlong_subset M hM.isClosedSubmanifold_N
    hM.isCoherent T ht hz
  rw [he,preimage_empty] at hh
  exact hh

/-- Empty ORIGINAL cosupport forces every actual canonical centre empty,
and every actual finite canonical history is genuinely terminal. -/
theorem canonical_histories_empty_of_original_cosupp_empty
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (he : M.cosupp = ∅)
    (T : BlowupTower X D) (hc : IsCanonical M ((canonicalInvariant n).inv M) T) :
    IsEmptyTower T ∧ IsGeoResolution M T := by
  have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hc
  have hcos := transformed_cosupp_empty M hM.isWellFormed he T ht
  refine ⟨?_,ht,hcos⟩
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hc.1
    have hcosT := transformed_cosupp_empty M hM.isWellFormed he T htT
    refine ⟨ih hc.1 htT hcosT,?_⟩
    rcases hc.2 with he | hm
    · exact he
    · rw [hm,hcosT]
      exact eq_empty_iff_forall_notMem.mpr fun z hz => hz.1

private theorem preimage_regular_part_nonempty {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hne : (b ⁻¹' V.carrier).Nonempty) :
    (b ⁻¹' (V.carrier ∩ (regularOpen V : Set X))).Nonempty := by
  have hd := preimage_mono (HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V) (f := b)
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous] at hd
  by_contra hh
  have he := Set.not_nonempty_iff_eq_empty.mp hh
  obtain ⟨y,hy⟩ := hne
  have hz := hd hy
  rw [he,closure_empty] at hz
  exact hz

/-- Actual original openness and the true ambient value embedding produce
a source next-maximum encounter on the actual pulled-back stopped prefix. -/
theorem source_maximum_meets_pulled_regular_open
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g)
    (hc : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (ha : CentresAvoid (regularOpen V) T)
    (hm : ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ regularOpen V)
    (hne : (b ⁻¹' V.carrier).Nonempty) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let N := markedPullback (m := m) b M
    ∃ z ∈ maxLocus ((canonicalInvariant m).inv N Q) (geoTransformAlong N Q).cosupp,
      b (Q.proj z) ∈ regularOpen V := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let N := markedPullback (m := m) b M
  let hM : IsInvDomain n M := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  let hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have ht := hF.isGeoTestTower_of_isCanonical hM T hc
  have hcs := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary
    h M hM.isWellFormed ht
  obtain ⟨y,hyV,hyO⟩ := preimage_regular_part_nonempty hb V hne
  obtain ⟨z,hzy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence y
  obtain ⟨c,hcm,hcO⟩ := hm
  have hzO : T.proj (g z) ∈ regularOpen V := by rw [h.proj_comm,hzy]; exact hyO
  have hzV : T.proj (g z) ∈ V.carrier := by rw [h.proj_comm,hzy]; exact hyV
  have hzm : g z ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp :=
    (EmbeddedFromResolution.mem_maxLocus_iff_of_centresAvoid hF V hM T hc ha hcm hcO hzO).mpr hzV
  have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hb.isSubmersionAt y)
  have hv : ∀ p, g p ∈ (geoTransformAlong M T).cosupp →
      (canonicalInvariant m).inv N Q p = ambientDimensionMap hnm ((canonicalInvariant n).inv M T (g p)) := by
    intro p hp
    exact HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_value
      h M hM hc p hp
  refine ⟨z,⟨?_,?_⟩,?_⟩
  · rw [hcs]
    exact hzm.1
  · intro p hp
    have hp' : g p ∈ (geoTransformAlong M T).cosupp := by rw [hcs] at hp; exact hp
    rw [hv p hp',hv z hzm.1]
    exact (strictMono_ambientDimensionMap hnm).monotone (hzm.2 (g p) hp')
  · rw [hzy]
    exact hyO

private theorem cartesian_precompose_biholomorphism {b : Y → X} {g : E → D}
    (q : E → Y) (s : F → Y) (p : D → X)
    (η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E)
    (hη : ∀ z, q (η z) = s z) (hU : HolomorphicSquarePullback b g q p) :
    HolomorphicSquarePullback b (g ∘ η) s p := by
  intro k W a c ha hc hcone
  obtain ⟨w,hw,huniq⟩ := hU k W a c ha hc hcone
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro z
    exact (hη (η.symm (w z))).symm.trans (by rw [η.apply_symm_apply]; exact hw.2.1 z)
  · intro z
    change g (η (η.symm (w z))) = c z
    rw [η.apply_symm_apply]
    exact hw.2.2 z
  · intro v hv
    have he : η ∘ v = w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun z => (hη (v z)).trans (hv.2.1 z),hv.2.2⟩
    funext z
    apply η.injective
    change η (v z) = η (η.symm (w z))
    rw [η.apply_symm_apply]
    exact congrFun he z

/-- Any independently chosen source first-meeting prefix for the literal
pulled marked record compares with the SAME actual target prefix.  The
empty pulled-carrier branch permits any finite source canonical history. -/
theorem independent_source_prefix_comparison
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g)
    (hc : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (ha : CentresAvoid (regularOpen V) T)
    (hm : ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ regularOpen V) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let N := markedPullback (m := m) b M
    let U : Opens Y := ⟨b ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage hb.contMDiff.continuous⟩
    ∀ (S : BlowupTower Y F), IsCanonical N ((canonicalInvariant m).inv N) S → CentresAvoid U S →
      ((b ⁻¹' V.carrier).Nonempty →
        ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S) (geoTransformAlong N S).cosupp,
          S.proj z ∈ U) →
      ∃ η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
        (∀ z, Q.proj (η z) = S.proj z) ∧
        (∀ η' : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
          (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
        let G := g ∘ η
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
        (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
        IsGeoTestTower N S ∧ IsSNCDivisor m (geoTransformAlong N S).E ∧
        strictTransform m S.proj (b ⁻¹' V.carrier) = G ⁻¹' strictTransform n T.proj V.carrier ∧
        (IsClosedSubmanifold n (strictTransform n T.proj V.carrier) →
          IsClosedSubmanifold m (strictTransform m S.proj (b ⁻¹' V.carrier))) ∧
        (HasNormalCrossings n (strictTransform n T.proj V.carrier) (geoTransformAlong M T).E →
          HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' V.carrier))
            ((geoTransformAlong M T).E.map (G ⁻¹' ·))) := by
  dsimp only
  intro S hcS haS hmS
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let N := markedPullback (m := m) b M
  let U : Opens Y := ⟨b ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage hb.contMDiff.continuous⟩
  let hM : IsInvDomain n M := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  let hN := original_ambient_domain_pullback hb M hM
  have hcQ := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    h M hM hc
  have haQ : CentresAvoid U Q :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.centresAvoid_preimage hb h (regularOpen V) ha
  have hcosN : N.cosupp = b ⁻¹' V.carrier := by
    have hcos : N.cosupp = b ⁻¹' M.cosupp :=
      HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hb hcoh M.N M.d
    rw [hcos,SmoothCentreLocus.cosupp_vanishingIdeal V.isClosed_carrier (subset_univ _)]
  have he : ∃! η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
      ∀ z, Q.proj (η z) = S.proj z := by
    by_cases hne : (b ⁻¹' V.carrier).Nonempty
    · have hmQ := source_maximum_meets_pulled_regular_open V hV hcoh hb h hc ha hm hne
      exact first_meeting_prefixes_existsUnique_biholomorphism N hN S Q hcS hcQ U haS haQ
        (hmS hne) hmQ
    · have hzero : N.cosupp = ∅ := hcosN.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      have hrS := (canonical_histories_empty_of_original_cosupp_empty N hN hzero S hcS).2
      have hrQ := (canonical_histories_empty_of_original_cosupp_empty N hN hzero Q hcQ).2
      exact original_ambient_terminal_choice_existsUnique N hN S Q hcS hcQ hrS hrQ
  obtain ⟨η,hη,huniq⟩ := he
  let G := g ∘ η
  have hG := isSubmersion_precompose_biholomorphism h.isSubmersion η
  have htS := (canonicalInvariant m).isInvValue.isGeoTestTower_of_isCanonical hN S hcS
  have hstrictQ :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
      hb h (regularOpen V) ha V.carrier (HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V)
  have hstrict : strictTransform m S.proj (b ⁻¹' V.carrier) =
      G ⁻¹' strictTransform n T.proj V.carrier := by
    have hh := HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞) η S.contMDiff_proj Q.contMDiff_proj
      (b ⁻¹' V.carrier) (V.isClosed_carrier.preimage hb.contMDiff.continuous) hη
    change strictTransform m S.proj (b ⁻¹' V.carrier) =
      η ⁻¹' strictTransform m Q.proj (b ⁻¹' V.carrier) at hh
    rw [hstrictQ] at hh
    exact hh
  refine ⟨η,hη,huniq,hG,?_,cartesian_precompose_biholomorphism Q.proj S.proj T.proj η hη h.universal,
    htS,(InvDomainTowerAlong.isInvDomain_geoTransformAlong hN S htS).isWellFormed.isSNCDivisor,
    hstrict,?_,?_⟩
  · intro z
    exact (h.proj_comm (η z)).trans (congrArg b (hη z))
  · intro hSM
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion hG hSM
  · intro hNC
    rw [hstrict]
    exact hasNormalCrossings_preimage_submersion hG hNC

/-- Original compact target data construct a source stopping independently
inside its own actual full finite canonical history, without source compactness
or any supplied source history/comparison map. -/
theorem exists_original_independently_stopped_smooth_source [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let hM := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
    let P := compactCanonicalTower M hM
    let B := chosenActualTower defaultSmoothBlowupChoices hb P.2.val
    let N := markedPullback (m := m) b M
    let O := regularOpen V
    let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1)
      (E₀ : CMfd.{u} m) (S : BlowupTower Y E₀) (R' : BlowupTower E₀ B.1) (G : E₀ → D₀),
      T.append R = P.2.val ∧ S.append R' = B.2.1 ∧
      IsCanonical M ((canonicalInvariant n).inv M) T ∧ CentresAvoid O T ∧
      (∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      IsCanonical N ((canonicalInvariant m).inv N) S ∧ CentresAvoid U S ∧
      ((b ⁻¹' V.carrier).Nonempty →
        ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S) (geoTransformAlong N S).cosupp, S.proj z ∈ U) ∧
      (¬ (b ⁻¹' V.carrier).Nonempty → S.length = 0 ∧ IsEmptyTower B.2.1) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
      strictTransform m S.proj (b ⁻¹' V.carrier) = G ⁻¹' strictTransform n T.proj V.carrier ∧
      IsGeoTestTower N S ∧ IsSNCDivisor m (geoTransformAlong N S).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj V.carrier) ∧
      (∀ z ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) z V.dim) ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier) (geoTransformAlong M T).E ∧
      IsIsomorphismOver n T.proj (O : Set X) ∧
      IsClosedSubmanifold m (strictTransform m S.proj (b ⁻¹' V.carrier)) ∧
      (∀ z ∈ strictTransform m S.proj (b ⁻¹' V.carrier),
        RegularAtDim (n := m) (strictTransform m S.proj (b ⁻¹' V.carrier)) z (V.dim+(m-n))) ∧
      HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' V.carrier))
        ((geoTransformAlong M T).E.map (G ⁻¹' ·)) ∧
      CentresOver (b ⁻¹' singularLocus V) S ∧
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence m Y [] (b ⁻¹' singularLocus V)
        E₀ S.proj (geoTransformAlong N S).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
      IsProperMap S.proj ∧ Surjective S.proj ∧
      S.proj '' exceptionalLocus m S.proj ⊆ b ⁻¹' singularLocus V ∧
      IsIsomorphismOver m S.proj (U : Set Y) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let hM : IsInvDomain n M := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  let P := compactCanonicalTower M hM
  let B := chosenActualTower defaultSmoothBlowupChoices hb P.2.val
  let N := markedPullback (m := m) b M
  let O := regularOpen V
  let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
  let hN := original_ambient_domain_pullback hb M hM
  obtain ⟨D₀,T,R,C₀,Q,g,hTR,hcT,_htT,haT,hmT,hactual,
    _hg,_hlen,_hcomm,_hcart,_hcQ,_htQ,_hrecord,_hE,_haQ,_hoverT,_hoverQ,_hadmT,_hadmQ,
    hSNCT,_hSNCQ,_hstrict,hSMT,_hSMQ,hrT,_hrQ,hNCT,_hNCQ,_hholT,_hholQ,
    _hproperT,_hproperQ,_hsurjT,_hsurjQ,_hExcT,_hExcQ,hisoT,_hisoQ⟩ :=
    exists_original_smooth_embedded_stopped_prefix V hV hcoh hb
  have hcP := compactCanonicalTower_isCanonical M hM
  have hrP : IsGeoResolution M P.2.val := P.2.property.2
  have hB := originalFiniteSmoothSourceHistory_properties hb M hM P.2.val hcP hrP
  have hcosN : N.cosupp = b ⁻¹' V.carrier := by
    have hh : N.cosupp = b ⁻¹' M.cosupp :=
      HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hb hcoh M.N M.d
    rw [hh,SmoothCentreLocus.cosupp_vanishingIdeal V.isClosed_carrier (subset_univ _)]
  have hSdata : ∃ (E₀ : CMfd.{u} m) (S : BlowupTower Y E₀) (R' : BlowupTower E₀ B.1),
      S.append R' = B.2.1 ∧ IsCanonical N ((canonicalInvariant m).inv N) S ∧ CentresAvoid U S ∧
      ((b ⁻¹' V.carrier).Nonempty →
        ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S) (geoTransformAlong N S).cosupp, S.proj z ∈ U) ∧
      (¬ (b ⁻¹' V.carrier).Nonempty → S.length = 0 ∧ IsEmptyTower B.2.1) := by
    by_cases hne : (b ⁻¹' V.carrier).Nonempty
    · have hnot : ¬ CentresAvoid U B.2.1 := by
        intro hav
        obtain ⟨y,hyV,hyO⟩ := preimage_regular_part_nonempty hb V hne
        obtain ⟨z,hzy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective B.2.1.isBlowupSequence y
        have hzU : B.2.1.proj z ∈ U := by change b (B.2.1.proj z) ∈ O; rw [hzy]; exact hyO
        have hzN : B.2.1.proj z ∈ N.cosupp := by rw [hcosN,hzy]; exact hyV
        have hz := (mem_cosupp_iff_of_centresAvoid N hN.isWellFormed B.2.1 hB.2.1 U hav z hzU).mpr hzN
        rw [hB.2.2] at hz
        exact hz
      obtain ⟨E₀,S,R',hSR,hcS,haS,hmS⟩ :=
        exists_first_centre N ((canonicalInvariant m).inv N) U B.2.1 hB.1 hnot
      exact ⟨E₀,S,R',hSR,hcS,haS,fun _ => hmS,fun hh => False.elim (hh hne)⟩
    · have hzero : N.cosupp = ∅ := hcosN.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      have heB := (canonical_histories_empty_of_original_cosupp_empty N hN hzero B.2.1 hB.1).1
      exact ⟨Y,BlowupTower.refl,B.2.1,BlowupTower.refl_append B.2.1,True.intro,True.intro,
        fun hh => False.elim (hne hh),fun _ => ⟨rfl,heB⟩⟩
  obtain ⟨E₀,S,R',hSR,hcS,haS,hmS,heS⟩ := hSdata
  obtain ⟨η,_hη,_huniq,hG,hproj,hcart,htS,hSNCS,hstrict,hSMS,hNCS⟩ :=
    independent_source_prefix_comparison V hV hcoh hb hactual hcT haT hmT S hcS haS hmS
  let G := g ∘ η
  have hregS : ∀ z ∈ strictTransform m S.proj (b ⁻¹' V.carrier),
      RegularAtDim (n := m) (strictTransform m S.proj (b ⁻¹' V.carrier)) z (V.dim+(m-n)) := by
    rw [hstrict]
    intro z hz
    exact regularAtDim_preimage_submersion (hG.isSubmersionAt z) (hrT (G z) hz)
  have hoverS : CentresOver (b ⁻¹' singularLocus V) S := by
    simpa only [U,O,regularOpen,Opens.coe_mk,preimage_compl,compl_compl] using
      HironakaAdmissibleSequence.centresOver_compl_of_centresAvoid U S haS
  have hExcS : S.proj '' exceptionalLocus m S.proj ⊆ b ⁻¹' singularLocus V := by
    simpa only [U,O,regularOpen,Opens.coe_mk,preimage_compl,compl_compl] using
      EmbeddedFromResolution.image_exceptionalLocus_subset_compl U S haS
  have hisoS : IsIsomorphismOver m S.proj (U : Set Y) := by
    simpa only [U,O,regularOpen,Opens.coe_mk,preimage_compl] using
      HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        S.isBlowupSequence hExcS
  exact ⟨D₀,T,R,E₀,S,R',G,hTR,hSR,hcT,haT,hmT,hcS,haS,hmS,heS,hG,hproj,hcart,hstrict,
    htS,hSNCS,hSNCT,hSMT,hrT,hNCT,hisoT,hSMS hSMT,hregS,hNCS hNCT,hoverS,
    HironakaAdmissibleSequence.isAdmissibleBlowupSequence_proj N _ S htS hoverS,
    S.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj S,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence,hExcS,hisoS⟩

end

end Hironaka.HironakaOriginalIndependentStoppedSource
