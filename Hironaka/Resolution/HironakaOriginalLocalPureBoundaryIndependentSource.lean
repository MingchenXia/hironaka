/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalPureBoundaryCanonicalPrefix

/-! # Internally stopped intrinsic smooth sources of the same local pure target

The original-only prescribed-open producer chooses the actual target BEFORE
every source. Its source is now internally cut in the actual pullback of the
SAME full target terminal history. Relative dimension is bounded only when
there is a source point; empty sources use the genuine identity prefix.
The compact-neighbourhood form keeps that same chosen open and target.
Blueprint: `hironaka-original-local-pure-boundary-independent-source-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalPureBoundaryIndependentSource
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres HironakaAdmissibleSequence
  HironakaOriginalLocalPureBoundaryCanonicalPrefix HironakaOriginalPureBoundaryTerminalPrefix
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionRelativeControlledTower HironakaOriginalIndependentStoppedSource

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X : CMfd.{u} n}

/-- An explicit RESULT property, with target histories before every source.
It assumes no source, history, maximum, comparison or ideal certificate. -/
def HasIndependentLocalPureBoundaryResolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (d : ℕ)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (U : Opens X) : Prop :=
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let hWaU := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  let hEU := isSNCDivisor_preimage_submersion (isSubmersion_val U) E₀ hE₀
  let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
  let O := boundaryGoodOpen (X := CMfd.of (n := n) U) WU hWaU d EU hEU
  let F₀ := WU \ regularLocus (n := n) WU d ∪ WU ∩ ⋃ H ∈ EU, H
  ∃ (Z : CMfd.{u} n) (P : BlowupTower (CMfd.of (n := n) U) Z)
    (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D) (R : BlowupTower D Z),
    IsCanonical M ((canonicalInvariant n).inv M) P ∧ IsGeoResolution M P ∧
    (T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (WU.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T)
        (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      (WU = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧ CentresOver F₀ T ∧
      IsAdmissibleBlowupSequence n U EU F₀ D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj WU) ∧
      (∀ z ∈ strictTransform n T.proj WU,
        RegularAtDim (n := n) (strictTransform n T.proj WU) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj WU) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H) ⊆ T.proj ⁻¹' F₀ ∧
      T.proj ⁻¹' (WU \ regularLocus (n := n) WU d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj F₀ᶜ) ∧
    ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → U)
      (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      let W' := b ⁻¹' WU
      let E' := EU.map (b ⁻¹' ·)
      let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
      let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWaU
      let hEY := isSNCDivisor_preimage_submersion hb EU hEU
      let V := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
      let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
      ∃ (ZB : CMfd.{u} m) (B : BlowupTower Y ZB) (gP : ZB → Z)
        (CQ : CMfd.{u} m) (Q : BlowupTower Y CQ) (g : CQ → D)
        (C : CMfd.{u} m) (S : BlowupTower Y C) (R' : BlowupTower C ZB)
        (η : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ),
        IsActualTowerPullback b B P gP ∧
        IsCanonical M' ((canonicalInvariant m).inv M') B ∧ IsGeoResolution M' B ∧
        IsActualTowerPullback b Q T g ∧ S.append R' = B ∧
        IsCanonical M' ((canonicalInvariant m).inv M') S ∧ IsGeoTestTower M' S ∧
        CentresAvoid V S ∧
        (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
          (geoTransformAlong M' S).cosupp, S.proj z ∈ V) ∧
        (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B) ∧ F' = b ⁻¹' F₀ ∧
        (∀ z, Q.proj (η z) = S.proj z) ∧
        (∀ η' : C ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ CQ,
          (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
        let G := g ∘ η
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
        (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
        strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj WU ∧
        (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
          ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
        IsSNCDivisor m (geoTransformAlong M' S).E ∧
        IsClosedSubmanifold m (strictTransform m S.proj W') ∧
        (∀ z ∈ strictTransform m S.proj W',
          RegularAtDim (n := m) (strictTransform m S.proj W') z (d+(m-n))) ∧
        HasNormalCrossings m (strictTransform m S.proj W') (geoTransformAlong M' S).E ∧
        CentresOver F' S ∧
        IsAdmissibleBlowupSequence m Y E' F' C S.proj (geoTransformAlong M' S).E ∧
        exceptionalLocus m S.proj ⊆ ⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H ∧
        (⋃ H ∈ (geoTransformAlong M' S).E.drop E'.length, H) ⊆ S.proj ⁻¹' F' ∧
        S.proj ⁻¹' (W' \ regularLocus (n := m) W' (d+(m-n))) ⊆ exceptionalLocus m S.proj ∧
        ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
        IsProperMap S.proj ∧ Surjective S.proj ∧ IsIsomorphismOver m S.proj F'ᶜ

/-- Original-only prescribed local data internally choose S in the actual
pullback of SAME full target P, rather than assuming S's stopping certificate. -/
theorem exists_local_original_independently_stopped_intrinsic_source
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    HasIndependentLocalPureBoundaryResolution W hWa d E₀ hE₀ U := by
  unfold HasIndependentLocalPureBoundaryResolution
  dsimp only
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
  obtain ⟨hWaU,hpureU,hEU,hEUW⟩ := original_open_data U W hWa d hpure E₀ hE₀ hE₀W
  have hM : IsInvDomain n M := HironakaEmbeddedBoundary.isInvDomain_boundary hWaU
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpureU) hEU
  obtain ⟨Z,P,D,T,R,hcP,hrP,hTarget,hSources⟩ :=
    exists_local_original_pure_boundary_stopped_smooth_source W hWa d hd hpure E₀ hE₀ hE₀W U hK hUK
  refine ⟨Z,P,D,T,R,hcP,hrP,hTarget,?_⟩
  intro m Y b hb
  let W' := b ⁻¹' WU
  let E' := EU.map (b ⁻¹' ·)
  let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
  let N := markedPullback (m := m) b M
  let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWaU
  let hEY := isSNCDivisor_preimage_submersion hb EU hEU
  let V := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
  let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
  have hEq : N = M' := by
    change (⟨b ⁻¹' univ,EU.map (b ⁻¹' ·),
      GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) WU),1⟩ : MarkedIdeal m Y) = _
    rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb WU]
  have hM' : IsInvDomain m M' := by rw [← hEq]; exact original_ambient_domain_pullback (X := CMfd.of (n := n) U) (Y := Y) hb M hM
  have hcos : M'.cosupp = W' := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWaY.isClosed E'
  obtain ⟨ZB,B,gP,hactualB⟩ := exists_actual_tower hb P
  have hcB : IsCanonical M' ((canonicalInvariant m).inv M') B := by
    rw [← hEq]
    exact IsActualTowerPullback.original_ambient_canonical hactualB M hM hcP
  have hrB : IsGeoResolution M' B := by
    rw [← hEq]
    refine ⟨(IsActualTowerPullback.relative_marked_dictionary hactualB M hM.isWellFormed hrP.1).1,?_⟩
    rw [IsActualTowerPullback.relative_cosupport_dictionary hactualB M hM.isWellFormed hrP.1,
      hrP.2,preimage_empty]
  obtain ⟨CQ,Q,g,hactualQ,_hcQ,_htQ,_hg,_hlen,_hproj,_hcart,_hstrictQ,_hEQ,hCompare⟩ := hSources Y b hb
  have hSource : ∃ (C : CMfd.{u} m) (S : BlowupTower Y C) (R' : BlowupTower C ZB),
      S.append R' = B ∧ IsCanonical M' ((canonicalInvariant m).inv M') S ∧ CentresAvoid V S ∧
      (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
        (geoTransformAlong M' S).cosupp, S.proj z ∈ V) ∧
      (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B) := by
    by_cases hY : Nonempty Y
    · obtain ⟨y⟩ := hY
      have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hb.isSubmersionAt y)
      have hdm : d+(m-n)<m := by omega
      have hpureY := pure_regular_density_preimage (X := CMfd.of (n := n) U) (Y := Y) hb WU d hpureU
      have hEYD := boundary_density_preimage (X := CMfd.of (n := n) U) (Y := Y) hb WU EU hEUW
      obtain ⟨C,S,R',hSR,hcS,_htS,haS,hmS,heS,_hrest⟩ :=
        exists_pure_boundary_prefix_of_terminal W' hWaY (d+(m-n)) hdm hpureY E' hEY hEYD B hcB hrB
      exact ⟨C,S,R',hSR,hcS,haS,hmS,fun hne => heS (Set.not_nonempty_iff_eq_empty.mp hne)⟩
    · have hne : ¬ W'.Nonempty := by rintro ⟨y,_hy⟩; exact hY ⟨y⟩
      have heB := (canonical_histories_empty_of_original_cosupp_empty M' hM'
        (hcos.trans (Set.not_nonempty_iff_eq_empty.mp hne)) B hcB).1
      exact ⟨Y,.refl,B,BlowupTower.refl_append B,True.intro,True.intro,
        fun hh => False.elim (hne hh),fun _ => ⟨rfl,heB⟩⟩
  obtain ⟨C,S,R',hSR,hcS,haS,hmS,heS⟩ := hSource
  obtain ⟨η,hη,huniq,hG,hproj,hcart,htS,hSNCS,hstrict,hboundary,hSM,hr,hNC⟩ :=
    hCompare C S hcS haS hmS
  have hoverS : CentresOver F' S := by
    apply HironakaEmbeddedBoundary.centresOver_of_inter_subset (F := M'.cosupp) (G := (V : Set Y)ᶜ)
      (H := F') ?_ S
      (centresOver_cosupp M' hM'.isWellFormed.isClosedSubmanifold_N hM'.isWellFormed.isCoherent S htS)
      (centresOver_compl_of_centresAvoid V S haS)
    rintro y ⟨hyW,hyV⟩
    rw [hcos] at hyW
    have hh : y ∈ W' \ regularLocus (n := m) W' (d+(m-n)) ∪ ⋃ H ∈ E', H := not_not.mp hyV
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨hyW,hh⟩
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M' hEY.1 S
  have hsuppF := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver F' S hoverS
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support S
  have hExcF : S.proj '' exceptionalLocus m S.proj ⊆ F' := by
    rintro y ⟨z,hz,rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨ZB,B,gP,CQ,Q,g,C,S,R',η,hactualB,hcB,hrB,hactualQ,hSR,hcS,htS,haS,hmS,heS,
    ?_,hη,huniq,hG,hproj,hcart,hstrict,hboundary,hSNCS,hSM,hr,hNC,hoverS,
    isAdmissibleBlowupSequence_proj M' F' S htS hoverS,?_,?_,
    HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus S.contMDiff_proj
      hWaY.isClosed hr,S.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj S,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      S.isBlowupSequence hExcF⟩
  · exact (boundary_bad_set_preimage_eq (X := CMfd.of (n := n) U) (Y := Y) hb WU d EU).symm
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF

/-- ONE open neighbourhood with compact closure and its target are fixed BEFORE
all smooth sources. No functorial choice of neighbourhoods is asserted. -/
theorem exists_original_pure_boundary_canonical_local
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      HasIndependentLocalPureBoundaryResolution W hWa d E₀ hE₀ U := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U,hUo⟩,hKU,hUc,exists_local_original_independently_stopped_intrinsic_source
    W hWa d hd hpure E₀ hE₀ hE₀W ⟨U,hUo⟩ hUc subset_closure⟩

end
end Hironaka.HironakaOriginalLocalPureBoundaryIndependentSource
