/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStoppedBoundaryTransport
import Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-!
# Actual canonical stopped prefixes for original pure analytic carriers

Original compact analytic pure-dimensional data and an initial SNC boundary
internally supply the actual canonical stopped target prefix and its tail.
The smooth source is the genuine actual pullback of that SAME prefix, with
whole conventional strict carrier and own actual ordered boundary.

Source canonicality concerns the literal pulled marked record only.
Blueprint: `hironaka-original-pure-boundary-canonical-prefix-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalPureBoundaryCanonicalPrefix

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres EmbeddedFromResolution HironakaAdmissibleSequence
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings HironakaOriginalIndependentStoppedSource
  HironakaOriginalBoundaryCanonicalPrincipalization

open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.ResolutionDriver (maxLocus)
open _root_.Hironaka.ResolutionInvariantExt (IsEmptyTower)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}

/-- The genuine original boundary-free regular open, not a supplied good-locus certificate. -/
def boundaryGoodOpen (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) : Opens X :=
  ⟨(W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H)ᶜ,
    ((HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).union
      (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1)).isOpen_compl⟩

/-- The actual original finite canonical target is stopped before its first
whole maximum meeting the original good open; its actual tail is retained. -/
theorem exists_original_pure_boundary_canonical_prefix
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
      (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
    let hC : IsCompact M.cosupp := (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
    let P := compactCosupportCanonicalTower M hM hC
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    let F := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1),
      T.append R = P.2.val ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧
      (W = ∅ → T.length = 0 ∧ IsEmptyTower P.2.val) ∧
      CentresOver F T ∧
      IsAdmissibleBlowupSequence n X E₀ F D₀ T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ z ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj Fᶜ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  have hcos : M.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀
  let hC : IsCompact M.cosupp := hcos.symm ▸ hK
  let P := compactCosupportCanonicalTower M hM hC
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let F := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
  let hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hEO : ∀ H ∈ E₀, Disjoint H (O : Set X) := fun H hH =>
    disjoint_left.mpr fun x hxH hxO => hxO (Or.inr (mem_biUnion hH hxH))
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hxW hxO
    by_contra hh
    exact hxO (Or.inl ⟨hxW,hh⟩)
  have hdense : W ⊆ closure (W ∩ (O : Set X)) :=
    HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
      (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hprefix : ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1),
      T.append R = P.2.val ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧ (W = ∅ → T.length = 0 ∧ IsEmptyTower P.2.val) := by
    by_cases hne : W.Nonempty
    · have hnot : ¬ CentresAvoid O P.2.val := by
        intro hav
        have hneWO : (W ∩ (O : Set X)).Nonempty := by
          by_contra hh
          have he := Set.not_nonempty_iff_eq_empty.mp hh
          obtain ⟨x,hx⟩ := hne
          have hx' := hdense hx
          rw [he,closure_empty] at hx'
          exact hx'
        obtain ⟨x,hxW,hxO⟩ := hneWO
        obtain ⟨z,hzx⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective P.2.val.isBlowupSequence x
        have hzO : P.2.val.proj z ∈ O := by rw [hzx]; exact hxO
        have hzW : P.2.val.proj z ∈ M.cosupp := by rw [hcos,hzx]; exact hxW
        have hz := (HironakaOriginalIndependentStoppedSource.mem_cosupp_iff_of_centresAvoid
          M hM.isWellFormed P.2.val P.2.property.2.1 O hav z hzO).mpr hzW
        rw [P.2.property.2.2] at hz
        exact hz
      obtain ⟨D₀,T,R,hTR,hc,ha,hm⟩ := exists_first_centre M ((canonicalInvariant n).inv M)
        O P.2.val P.2.property.1 hnot
      exact ⟨D₀,T,R,hTR,hc,ha,fun _ => hm,fun he => False.elim (hne.ne_empty he)⟩
    · have heW := Set.not_nonempty_iff_eq_empty.mp hne
      have heP := (canonical_histories_empty_of_original_cosupp_empty M hM (hcos.trans heW)
        P.2.val P.2.property.1).1
      exact ⟨X,.refl,P.2.val,BlowupTower.refl_append P.2.val,True.intro,True.intro,
        fun hh => False.elim (hne hh),fun _ => ⟨rfl,heP⟩⟩
  obtain ⟨D₀,T,R,hTR,hcT,haT,hmT,heT⟩ := hprefix
  have htT := hF.isGeoTestTower_of_isCanonical hM T hcT
  have hgeom : IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ z ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E := by
    by_cases hne : W.Nonempty
    · obtain ⟨c,hc,hcO⟩ := hmT hne
      have hadm := hF.isAdmissibleCentre_maxLocus hM T hcT htT
      have hCV := fun y (hy : T.proj y ∈ O) =>
        HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O hEO
          (fun x hx => hreg x hx x.2) hM T hcT haT hc hcO hy
      obtain ⟨hSC,hev,hr⟩ := HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid
        hWa O hreg hdense T haT hadm.1 hCV
      exact ⟨⟨isClosed_closure,fun z hz => ⟨d,hr z hz⟩⟩,hr,
        CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
          (fun z hz => ⟨_,hSC hz,hev z hz,hadm.2.2⟩)⟩
    · have heW := Set.not_nonempty_iff_eq_empty.mp hne
      have hST : strictTransform n T.proj W = ∅ := by rw [heW]; simp [strictTransform]
      rw [hST]
      exact ⟨⟨isClosed_empty,fun z hz => hz.elim⟩,fun z hz => hz.elim,fun z hz => hz.elim⟩
  have hover : CentresOver F T := by
    apply HironakaEmbeddedBoundary.centresOver_of_inter_subset (F := M.cosupp) (G := (O : Set X)ᶜ)
      (H := F) ?_ T
      (centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T htT)
      (centresOver_compl_of_centresAvoid O T haT)
    rintro x ⟨hxW,hxO⟩
    rw [hcos] at hxW
    have hh : x ∈ W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H := not_not.mp hxO
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hxW,hh⟩
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M hE₀.1 T
  have hsuppF := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver F T hover
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support T
  have hExcF : T.proj '' exceptionalLocus n T.proj ⊆ F := by
    rintro x ⟨z,hz,rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨D₀,T,R,hTR,hcT,htT,haT,hmT,heT,hover,
    isAdmissibleBlowupSequence_proj M F T htT hover,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T htT).isWellFormed.isSNCDivisor,
    hgeom.1,hgeom.2.1,hgeom.2.2,?_,?_,
    HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus T.contMDiff_proj
      hWa.isClosed hgeom.2.1,T.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence hExcF⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF


private theorem centresOver_actual_pullback {b : Y → X}
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (h : IsActualTowerPullback b Q T g) (F : Set X) (hT : CentresOver F T) :
    CentresOver (b ⁻¹' F) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hT.1,?_⟩
    intro z hz
    change b (Q.proj z) ∈ F
    rw [← h.proj_comm z]
    exact hT.2 hz


/-- The source-first pure boundary embedded prefix admits genuine arbitrary smooth base change. -/
theorem exists_original_pure_boundary_stopped_smooth_source
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
      (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
    let hC : IsCompact M.cosupp := (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
    let P := compactCosupportCanonicalTower M hM hC
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    let F := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
    let N := markedPullback (m := m) b M
    let U : Opens Y := ⟨b ⁻¹' (O : Set X),O.isOpen.preimage hb.contMDiff.continuous⟩
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1)
      (C₀ : CMfd.{u} m) (Q : BlowupTower Y C₀) (g : C₀ → D₀),
      IsActualTowerPullback b Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
      HolomorphicSquarePullback b g Q.proj T.proj ∧
      IsCanonical N ((canonicalInvariant m).inv N) Q ∧ IsGeoTestTower N Q ∧
      geoTransformAlong N Q = markedPullback (m := m) g (geoTransformAlong M T) ∧
      (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
      CentresAvoid U Q ∧ CentresOver (b ⁻¹' F) Q ∧
      IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' F) C₀ Q.proj (geoTransformAlong N Q).E ∧
      IsSNCDivisor m (geoTransformAlong N Q).E ∧
      strictTransform m Q.proj (b ⁻¹' W) = g ⁻¹' strictTransform n T.proj W ∧
      IsClosedSubmanifold m (strictTransform m Q.proj (b ⁻¹' W)) ∧
      (∀ z ∈ strictTransform m Q.proj (b ⁻¹' W),
        RegularAtDim (n := m) (strictTransform m Q.proj (b ⁻¹' W)) z (d+(m-n))) ∧
      HasNormalCrossings m (strictTransform m Q.proj (b ⁻¹' W)) (geoTransformAlong N Q).E ∧
      exceptionalLocus m Q.proj ⊆ ⋃ H ∈ (geoTransformAlong N Q).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong N Q).E.drop E₀.length, H) ⊆ Q.proj ⁻¹' (b ⁻¹' F) ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
      IsProperMap Q.proj ∧ Surjective Q.proj ∧ IsIsomorphismOver m Q.proj (b ⁻¹' F)ᶜ ∧
      T.append R = P.2.val ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧
      (W = ∅ → T.length = 0 ∧ IsEmptyTower P.2.val) ∧
      CentresOver F T ∧
      IsAdmissibleBlowupSequence n X E₀ F D₀ T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ z ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj Fᶜ := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let hM := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hC : IsCompact M.cosupp := (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
  let P := compactCosupportCanonicalTower M hM hC
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let F := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
  let N := markedPullback (m := m) b M
  let U : Opens Y := ⟨b ⁻¹' (O : Set X),O.isOpen.preimage hb.contMDiff.continuous⟩
  obtain ⟨D₀,T,R,h⟩ := exists_original_pure_boundary_canonical_prefix W hWa hK d hd hpure E₀ hE₀ hE₀W
  have hcopy := h
  rcases hcopy with ⟨hTR,hcT,htT,haT,hmT,heT,hoverT,hadmT,hSNCT,hSMT,hrT,hNCT,
    hExcT,hNewT,hSingT,hholT,hproperT,hsurjT,hisoT⟩
  obtain ⟨C₀,Q,g,hactual⟩ := exists_actual_tower hb T
  let hN := original_ambient_domain_pullback hb M hM
  obtain ⟨htQ,hrecord⟩ :=
    HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      hactual M hM.isWellFormed htT
  have hcQ := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    hactual M hM hcT
  have hE : (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) :=
    congrArg MarkedIdeal.E hrecord
  have haQ : CentresAvoid U Q :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.centresAvoid_preimage hb hactual O haT
  have hoverQ : CentresOver (b ⁻¹' F) Q := centresOver_actual_pullback hactual F hoverT
  have hdense : W ⊆ closure (W ∩ (O : Set X)) :=
    HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
      (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hstrict :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
      hb hactual O haT W hdense
  have hSMQ : IsClosedSubmanifold m (strictTransform m Q.proj (b ⁻¹' W)) := by
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion hactual.isSubmersion hSMT
  have hrQ : ∀ z ∈ strictTransform m Q.proj (b ⁻¹' W),
      RegularAtDim (n := m) (strictTransform m Q.proj (b ⁻¹' W)) z (d+(m-n)) := by
    rw [hstrict]
    intro z hz
    exact regularAtDim_preimage_submersion (hactual.isSubmersion.isSubmersionAt z) (hrT (g z) hz)
  have hNCQ : HasNormalCrossings m (strictTransform m Q.proj (b ⁻¹' W)) (geoTransformAlong N Q).E := by
    rw [hstrict,hE]
    exact hasNormalCrossings_preimage_submersion hactual.isSubmersion hNCT
  have hlenN : N.E.length = E₀.length := List.length_map _
  have hsuppQ := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop N
    hN.isWellFormed.isSNCDivisor.1 Q
  rw [hlenN] at hsuppQ
  have hsuppFQ := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver
    (b ⁻¹' F) Q hoverQ
  have hexcQ := HironakaPrincipalization.exceptionalLocus_subset_support Q
  have hExcFQ : Q.proj '' exceptionalLocus m Q.proj ⊆ b ⁻¹' F := by
    rintro y ⟨z,hz,rfl⟩
    exact hsuppFQ (hexcQ hz)
  refine ⟨D₀,T,R,C₀,Q,g,hactual,hactual.isSubmersion,hactual.length_eq,hactual.proj_comm,
    hactual.universal,hcQ,htQ,hrecord,hE,haQ,hoverQ,
    isAdmissibleBlowupSequence_proj N (b ⁻¹' F) Q htQ hoverQ,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hN Q htQ).isWellFormed.isSNCDivisor,
    hstrict,hSMQ,hrQ,hNCQ,?_,?_,Q.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj Q,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      Q.isBlowupSequence hExcFQ,h⟩
  · rw [← hsuppQ]
    exact hexcQ
  · rw [← hsuppQ]
    exact hsuppFQ

end

end Hironaka.HironakaOriginalPureBoundaryCanonicalPrefix
