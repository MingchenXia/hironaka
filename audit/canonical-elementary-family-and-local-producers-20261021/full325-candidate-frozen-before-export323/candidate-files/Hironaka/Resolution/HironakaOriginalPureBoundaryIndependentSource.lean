/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSmoothIntrinsicRegularLoci
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback

/-!
# Independently stopped intrinsic smooth sources with their actual boundaries

The whole original singular vanishing-ideal pullback identifies the actual
source record with its separately defined intrinsic vanishing-ideal record.
The intrinsic source good open and bad set are also identified by proved
geometric dictionaries. Actual first-meeting uniqueness then compares the
independently stopped source, retaining arbitrary actual empty positions.

Blueprint: `hironaka-original-pure-boundary-independent-source-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalPureBoundaryIndependentSource

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres EmbeddedFromResolution HironakaAdmissibleSequence
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionOriginalTerminalSubmersion
  HironakaSmoothSubmersionNormalCrossings HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalFirstMeetingPrefixUniqueness HironakaOriginalIndependentStoppedSource
  HironakaOriginalStoppedBoundaryTransport HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalSmoothIntrinsicRegularLoci

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E F : CMfd.{u} m} {b : Y → X}

/-- The actual whole ideal theorem identifies the entire independently defined source record. -/
private theorem intrinsic_marked_pullback_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (E₀ : List (Set X)) :
    markedPullback (m := m) b (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) =
      (⟨univ,E₀.map (b ⁻¹' ·),vanishingIdeal (n := m) (b ⁻¹' W),1⟩ : MarkedIdeal m Y) := by
  change (⟨b ⁻¹' univ,E₀.map (b ⁻¹' ·),GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) W),1⟩ :
    MarkedIdeal m Y) = _
  rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb W]

/-- Whole filtered boundaries of actual empty histories, with arbitrary
closed initial boundary and arbitrary different empty-step counts. -/
theorem empty_towers_filtered_boundary_transport
    (M : MarkedIdeal m Y) (hE : ∀ H ∈ M.E, IsClosed H)
    (S : BlowupTower Y F) (Q : BlowupTower Y E) (heS : IsEmptyTower S) (heQ : IsEmptyTower Q)
    (a : F → E) (hproj : ∀ z, Q.proj (a z) = S.proj z) :
    (geoTransformAlong M S).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M Q).E.map (a ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  rw [boundary_of_all_empty_tower M hE S heS,boundary_of_all_empty_tower M hE Q heQ]
  simp only [List.map_append,List.map_replicate,preimage_empty,List.filter_append,
    List.filter_replicate,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,reduceIte,List.append_nil,List.map_map]
  have hmap : M.E.map (S.proj ⁻¹' ·) = M.E.map (fun H => a ⁻¹' (Q.proj ⁻¹' H)) := by
    apply List.map_congr_left
    intro H _hH
    ext z
    change S.proj z ∈ H ↔ Q.proj (a z) ∈ H
    rw [hproj]
  exact congrArg (List.filter (fun H => decide H.Nonempty)) hmap

private theorem source_maximum_over_good_open
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g)
    (hc : IsCanonical (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)) T)
    (ha : CentresAvoid (boundaryGoodOpen W hWa d E₀ hE₀) T)
    (hm : W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ boundaryGoodOpen W hWa d E₀ hE₀)
    (hne : (b ⁻¹' W).Nonempty) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let N := markedPullback (m := m) b M
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    ∃ z ∈ maxLocus ((canonicalInvariant m).inv N Q) (geoTransformAlong N Q).cosupp,
      b (Q.proj z) ∈ O := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let N := markedPullback (m := m) b M
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have ht := hF.isGeoTestTower_of_isCanonical hM T hc
  have hcs := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary
    h M hM.isWellFormed ht
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hEO : ∀ H ∈ E₀, Disjoint H (O : Set X) := fun H hH =>
    disjoint_left.mpr fun x hxH hxO => hxO (Or.inr (mem_biUnion hH hxH))
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hxW hxO
    by_contra hh
    exact hxO (Or.inl ⟨hxW,hh⟩)
  have hneWO : (b ⁻¹' (W ∩ (O : Set X))).Nonempty := by
    by_contra hh
    have he := Set.not_nonempty_iff_eq_empty.mp hh
    obtain ⟨y,hy⟩ := hne
    have hz := preimage_mono (f := b) hdense hy
    have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
    rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous,he,closure_empty] at hz
    exact hz
  obtain ⟨y,hyW,hyO⟩ := hneWO
  obtain ⟨z,hzy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence y
  obtain ⟨c,hcm,hcO⟩ := hm ⟨b y,hyW⟩
  have hzO : T.proj (g z) ∈ O := by rw [h.proj_comm,hzy]; exact hyO
  have hzW : T.proj (g z) ∈ W := by rw [h.proj_comm,hzy]; exact hyW
  have hzm : g z ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp :=
    (HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O hEO
      (fun x hx => hreg x hx x.2) hM T hc ha hcm hcO hzO).mpr hzW
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



/-- Any independently chosen first-meeting prefix of the INTRINSIC source
compares with this SAME target prefix, retaining arbitrary actual empty slots. -/
theorem independent_intrinsic_source_prefix_comparison
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g)
    (hcT : IsCanonical (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)) T)
    (haT : CentresAvoid (boundaryGoodOpen W hWa d E₀ hE₀) T)
    (hmT : W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ boundaryGoodOpen W hWa d E₀ hE₀) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let M' : MarkedIdeal m Y := ⟨univ,E₀.map (b ⁻¹' ·),vanishingIdeal (n := m) (b ⁻¹' W),1⟩
    let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
    let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
    let U := boundaryGoodOpen (b ⁻¹' W) hWaY (d+(m-n)) (E₀.map (b ⁻¹' ·)) hEY
    ∀ (S : BlowupTower Y F), IsCanonical M' ((canonicalInvariant m).inv M') S → CentresAvoid U S →
      ((b ⁻¹' W).Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
        (geoTransformAlong M' S).cosupp, S.proj z ∈ U) →
      ∃ η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
        (∀ z, Q.proj (η z) = S.proj z) ∧
        (∀ η' : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
          (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
        let G := g ∘ η
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
        (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
        IsGeoTestTower M' S ∧ IsSNCDivisor m (geoTransformAlong M' S).E ∧
        strictTransform m S.proj (b ⁻¹' W) = G ⁻¹' strictTransform n T.proj W ∧
        (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
          ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
        (IsClosedSubmanifold n (strictTransform n T.proj W) →
          IsClosedSubmanifold m (strictTransform m S.proj (b ⁻¹' W))) ∧
        ((∀ z ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) z d) →
          ∀ z ∈ strictTransform m S.proj (b ⁻¹' W),
            RegularAtDim (n := m) (strictTransform m S.proj (b ⁻¹' W)) z (d+(m-n))) ∧
        (HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E →
          HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' W)) (geoTransformAlong M' S).E) := by
  dsimp only
  intro S hcS haS hmS
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let N := markedPullback (m := m) b M
  let M' : MarkedIdeal m Y := ⟨univ,E₀.map (b ⁻¹' ·),vanishingIdeal (n := m) (b ⁻¹' W),1⟩
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let V : Opens Y := ⟨b ⁻¹' (O : Set X),O.isOpen.preimage hb.contMDiff.continuous⟩
  let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
  let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
  let U := boundaryGoodOpen (b ⁻¹' W) hWaY (d+(m-n)) (E₀.map (b ⁻¹' ·)) hEY
  have hEq : N = M' := intrinsic_marked_pullback_eq hb W E₀
  have hU : U = V := boundary_good_open_preimage_eq hb W hWa d E₀ hE₀
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hN := original_ambient_domain_pullback hb M hM
  have hcSN : IsCanonical N ((canonicalInvariant m).inv N) S := by rw [hEq]; exact hcS
  have haSN : CentresAvoid V S := by rw [← hU]; exact haS
  have hmSN : (b ⁻¹' W).Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S)
      (geoTransformAlong N S).cosupp, S.proj z ∈ V := by
    intro hne
    rw [hEq,← hU]
    exact hmS hne
  have hcQ := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    h M hM hcT
  have haQ : CentresAvoid V Q :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.centresAvoid_preimage hb h O haT
  have hcosN : N.cosupp = b ⁻¹' W := by
    have hh : N.cosupp = b ⁻¹' M.cosupp :=
      HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hb hM.isWellFormed.isCoherent M.N M.d
    rw [hh,HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀]
  have hcomparison : ∃! η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
      ∀ z, Q.proj (η z) = S.proj z := by
    by_cases hne : (b ⁻¹' W).Nonempty
    · have hmQ := source_maximum_over_good_open W hWa d hd hpure E₀ hE₀ hE₀W hb h hcT haT hmT hne
      exact first_meeting_prefixes_existsUnique_biholomorphism N hN S Q hcSN hcQ V haSN haQ (hmSN hne) hmQ
    · have hzero : N.cosupp = ∅ := hcosN.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      exact original_ambient_terminal_choice_existsUnique N hN S Q hcSN hcQ
        (canonical_histories_empty_of_original_cosupp_empty N hN hzero S hcSN).2
        (canonical_histories_empty_of_original_cosupp_empty N hN hzero Q hcQ).2
  obtain ⟨η,hη,huniq⟩ := hcomparison
  let G := g ∘ η
  have hG := isSubmersion_precompose_biholomorphism h.isSubmersion η
  have htSN := (canonicalInvariant m).isInvValue.isGeoTestTower_of_isCanonical hN S hcSN
  have htS : IsGeoTestTower M' S := by rw [← hEq]; exact htSN
  have hSNCS : IsSNCDivisor m (geoTransformAlong M' S).E := by
    rw [← hEq]
    exact (InvDomainTowerAlong.isInvDomain_geoTransformAlong hN S htSN).isWellFormed.isSNCDivisor
  have hboundaryN : (geoTransformAlong N S).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong N Q).E.map (η ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    by_cases hne : (b ⁻¹' W).Nonempty
    · have hmQ := source_maximum_over_good_open W hWa d hd hpure E₀ hE₀ hE₀W hb h hcT haT hmT hne
      exact first_meeting_boundary_transport N hN S Q hcSN hcQ V haSN haQ (hmSN hne) hmQ η hη
    · have hzero : N.cosupp = ∅ := hcosN.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      exact empty_towers_filtered_boundary_transport N hN.isWellFormed.isSNCDivisor.1 S Q
        (canonical_histories_empty_of_original_cosupp_empty N hN hzero S hcSN).1
        (canonical_histories_empty_of_original_cosupp_empty N hN hzero Q hcQ).1 η hη
  have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hcT
  have hrecord := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    h M hM.isWellFormed htT).2
  have hEQ : (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) := congrArg MarkedIdeal.E hrecord
  have hmaps : ((geoTransformAlong M T).E.map (g ⁻¹' ·)).map (η ⁻¹' ·) =
      (geoTransformAlong M T).E.map (G ⁻¹' ·) := by
    simp only [List.map_map]
    rfl
  rw [hEQ,hmaps] at hboundaryN
  have hboundary : (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    rw [← hEq]
    exact hboundaryN
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hstrictQ :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
      hb h O haT W hdense
  have hstrict : strictTransform m S.proj (b ⁻¹' W) = G ⁻¹' strictTransform n T.proj W := by
    have hh := HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel m) Y ∞) η S.contMDiff_proj Q.contMDiff_proj (b ⁻¹' W)
      (hWa.isClosed.preimage hb.contMDiff.continuous) hη
    change strictTransform m S.proj (b ⁻¹' W) = η ⁻¹' strictTransform m Q.proj (b ⁻¹' W) at hh
    rw [hstrictQ] at hh
    exact hh
  refine ⟨η,hη,huniq,hG,?_,cartesian_precompose_biholomorphism Q.proj S.proj T.proj η hη h.universal,
    htS,hSNCS,hstrict,hboundary,?_,?_,?_⟩
  · intro z
    exact (h.proj_comm (η z)).trans (congrArg b (hη z))
  · intro hSM
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion hG hSM
  · intro hrT
    rw [hstrict]
    intro z hz
    exact regularAtDim_preimage_submersion (hG.isSubmersionAt z) (hrT (G z) hz)
  · intro hNC
    apply (hasNormalCrossings_filter_nonempty_iff _ _).mp
    rw [hboundary]
    apply (hasNormalCrossings_filter_nonempty_iff _ _).mpr
    rw [hstrict]
    exact hasNormalCrossings_preimage_submersion hG hNC
/-! The independent source prefix below is selected inside the actual smooth
pullback of the full target terminal history, rather than supplied by a caller. -/

/-- Original pure-carrier and initial-boundary data internally supply an
independently stopped intrinsic source and its complete elementary dictionary. -/
theorem exists_original_independently_stopped_intrinsic_source
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
      (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
    let hC : IsCompact M.cosupp :=
      (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
    let P := compactCosupportCanonicalTower M hM hC
    let B := chosenActualTower defaultSmoothBlowupChoices hb P.2.val
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    let F₀ := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
    let W' := b ⁻¹' W
    let E' := E₀.map (b ⁻¹' ·)
    let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
    let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
    let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
    let U := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
    let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1)
      (C₀ : CMfd.{u} m) (S : BlowupTower Y C₀) (R' : BlowupTower C₀ B.1) (G : C₀ → D₀),
      S.append R' = B.2.1 ∧ IsCanonical M' ((canonicalInvariant m).inv M') S ∧
      IsGeoTestTower M' S ∧ CentresAvoid U S ∧
      (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S) (geoTransformAlong M' S).cosupp,
        S.proj z ∈ U) ∧
      (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B.2.1) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
      strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj W ∧
      (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
      IsSNCDivisor m (geoTransformAlong M' S).E ∧
      IsClosedSubmanifold m (strictTransform m S.proj W') ∧
      (∀ z ∈ strictTransform m S.proj W',
        RegularAtDim (n := m) (strictTransform m S.proj W') z (d+(m-n))) ∧
      HasNormalCrossings m (strictTransform m S.proj W') (geoTransformAlong M' S).E ∧
      CentresOver F' S ∧
      IsAdmissibleBlowupSequence m Y E' F' C₀ S.proj (geoTransformAlong M' S).E ∧
      exceptionalLocus m S.proj ⊆ ⋃ H ∈ (geoTransformAlong M' S).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong M' S).E.drop E₀.length, H) ⊆ S.proj ⁻¹' F' ∧
      S.proj ⁻¹' (W' \ regularLocus (n := m) W' (d+(m-n))) ⊆ exceptionalLocus m S.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
      IsProperMap S.proj ∧ Surjective S.proj ∧ IsIsomorphismOver m S.proj F'ᶜ ∧
      T.append R = P.2.val ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧
      (W = ∅ → T.length = 0 ∧ IsEmptyTower P.2.val) ∧
      CentresOver F₀ T ∧
      IsAdmissibleBlowupSequence n X E₀ F₀ D₀ T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ z ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H) ⊆ T.proj ⁻¹' F₀ ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj F₀ᶜ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hC : IsCompact M.cosupp :=
    (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
  let P := compactCosupportCanonicalTower M hM hC
  let B := chosenActualTower defaultSmoothBlowupChoices hb P.2.val
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let W' := b ⁻¹' W
  let E' := E₀.map (b ⁻¹' ·)
  let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
  let N := markedPullback (m := m) b M
  let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
  let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
  let U := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
  let V : Opens Y := ⟨b ⁻¹' (O : Set X),O.isOpen.preimage hb.contMDiff.continuous⟩
  let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
  have hEq : N = M' := intrinsic_marked_pullback_eq hb W E₀
  have hU : U = V := boundary_good_open_preimage_eq hb W hWa d E₀ hE₀
  have hM' : IsInvDomain m M' := by
    rw [← hEq]
    exact original_ambient_domain_pullback hb M hM
  have hcos : M'.cosupp = W' :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := m) hWaY.isClosed E'
  obtain ⟨D₀,T,R,hTarget⟩ :=
    exists_original_pure_boundary_canonical_prefix W hWa hK d hd hpure E₀ hE₀ hE₀W
  have hcopy := hTarget
  rcases hcopy with ⟨_hTR,hcT,_htT,haT,hmT,_heT,_hoverT,_hadmT,_hSNCT,hSMT,hrT,hNCT,
    _hExcT,_hNewT,_hSingT,_hholT,_hproperT,_hsurjT,_hisoT⟩
  obtain ⟨C₁,Q,g,hactual⟩ := exists_actual_tower hb T
  have hBN := originalFiniteSmoothSourceHistory_properties hb M hM P.2.val P.2.property.1 P.2.property.2
  have hB : IsCanonical M' ((canonicalInvariant m).inv M') B.2.1 ∧ IsGeoResolution M' B.2.1 := by
    rw [← hEq]
    exact hBN
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hSource : ∃ (C₀ : CMfd.{u} m) (S : BlowupTower Y C₀) (R' : BlowupTower C₀ B.1),
      S.append R' = B.2.1 ∧ IsCanonical M' ((canonicalInvariant m).inv M') S ∧ CentresAvoid U S ∧
      (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S) (geoTransformAlong M' S).cosupp,
        S.proj z ∈ U) ∧ (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B.2.1) := by
    by_cases hne : W'.Nonempty
    · have hnot : ¬ CentresAvoid U B.2.1 := by
        intro hav
        have hneWO : (b ⁻¹' (W ∩ (O : Set X))).Nonempty := by
          by_contra hh
          have he := Set.not_nonempty_iff_eq_empty.mp hh
          obtain ⟨y,hy⟩ := hne
          have hz := preimage_mono (f := b) hdense hy
          have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
          rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous,he,closure_empty] at hz
          exact hz
        obtain ⟨y,hyW,hyO⟩ := hneWO
        obtain ⟨z,hzy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective B.2.1.isBlowupSequence y
        have hzU : B.2.1.proj z ∈ U := by
          rw [hU]
          change b (B.2.1.proj z) ∈ O
          rw [hzy]
          exact hyO
        have hzW : B.2.1.proj z ∈ M'.cosupp := by rw [hcos,hzy]; exact hyW
        have hz := (mem_cosupp_iff_of_centresAvoid M' hM'.isWellFormed B.2.1 hB.2.1 U hav z hzU).mpr hzW
        rw [hB.2.2] at hz
        exact hz
      obtain ⟨C₀,S,R',hSR,hcS,haS,hmS⟩ :=
        exists_first_centre M' ((canonicalInvariant m).inv M') U B.2.1 hB.1 hnot
      exact ⟨C₀,S,R',hSR,hcS,haS,fun _ => hmS,fun hh => False.elim (hh hne)⟩
    · have hzero : M'.cosupp = ∅ := hcos.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      have heB := (canonical_histories_empty_of_original_cosupp_empty M' hM' hzero B.2.1 hB.1).1
      exact ⟨Y,BlowupTower.refl,B.2.1,BlowupTower.refl_append B.2.1,True.intro,True.intro,
        fun hh => False.elim (hne hh),fun _ => ⟨rfl,heB⟩⟩
  obtain ⟨C₀,S,R',hSR,hcS,haS,hmS,heS⟩ := hSource
  obtain ⟨η,_hη,_huniq,hG,hproj,hcart,htS,hSNCS,hstrict,hboundary,hSM,hr,hNC⟩ :=
    independent_intrinsic_source_prefix_comparison W hWa d hd hpure E₀ hE₀ hE₀W hb
      hactual hcT haT hmT S hcS haS hmS
  let G := g ∘ η
  have hSMS := hSM hSMT
  have hrS := hr hrT
  have hNCS := hNC hNCT
  have hoverS : CentresOver F' S := by
    apply HironakaEmbeddedBoundary.centresOver_of_inter_subset (F := M'.cosupp) (G := (U : Set Y)ᶜ)
      (H := F') ?_ S
      (centresOver_cosupp M' hM'.isWellFormed.isClosedSubmanifold_N hM'.isWellFormed.isCoherent S htS)
      (centresOver_compl_of_centresAvoid U S haS)
    rintro y ⟨hyW,hyU⟩
    rw [hcos] at hyW
    have hh : y ∈ W' \ regularLocus (n := m) W' (d+(m-n)) ∪ ⋃ H ∈ E', H := not_not.mp hyU
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hyW,hh⟩
  have hlen : M'.E.length = E₀.length := List.length_map _
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M' hEY.1 S
  rw [hlen] at hsupp
  have hsuppF := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver F' S hoverS
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support S
  have hExcF : S.proj '' exceptionalLocus m S.proj ⊆ F' := by
    rintro y ⟨z,hz,rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨D₀,T,R,C₀,S,R',G,hSR,hcS,htS,haS,hmS,heS,hG,hproj,hcart,hstrict,hboundary,hSNCS,
    hSMS,hrS,hNCS,hoverS,isAdmissibleBlowupSequence_proj M' F' S htS hoverS,?_,?_,
    HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus S.contMDiff_proj
      hWaY.isClosed hrS,S.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj S,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      S.isBlowupSequence hExcF,hTarget⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF

end

end Hironaka.HironakaOriginalPureBoundaryIndependentSource
