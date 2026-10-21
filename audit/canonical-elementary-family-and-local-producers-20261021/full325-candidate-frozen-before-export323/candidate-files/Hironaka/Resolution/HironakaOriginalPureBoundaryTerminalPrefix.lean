/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureBoundaryCanonicalPrefix

/-!
# Literal first-meeting prefix of any genuine original canonical terminal tower

Compactness is needed by a separate terminal-history producer, not by this
actual cutting argument. Every same-map geometry field and literal tail is
retained for later genuine local original-only consumers.
Blueprint: `hironaka-original-pure-boundary-terminal-prefix-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPureBoundaryTerminalPrefix
noncomputable section
open HironakaOriginalPureBoundaryCanonicalPrefix
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres EmbeddedFromResolution HironakaAdmissibleSequence
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings HironakaOriginalIndependentStoppedSource
  HironakaOriginalBoundaryCanonicalPrincipalization

open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Z : CMfd.{u} n}

/-- Cut the unchanged actual terminal tower, retaining its literal tail and all pure geometry. -/
theorem exists_pure_boundary_prefix_of_terminal
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) 
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (P : BlowupTower X Z)
    (hcP : IsCanonical (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)) P)
    (hrP : IsGeoResolution (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) P) :
    let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
    let O := boundaryGoodOpen W hWa d E₀ hE₀
    let F := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ Z),
      T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧
      (W = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧
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
  have hprefix : ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ Z),
      T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
        T.proj c ∈ O) ∧ (W = ∅ → T.length = 0 ∧ IsEmptyTower P) := by
    by_cases hne : W.Nonempty
    · have hnot : ¬ CentresAvoid O P := by
        intro hav
        have hneWO : (W ∩ (O : Set X)).Nonempty := by
          by_contra hh
          have he := Set.not_nonempty_iff_eq_empty.mp hh
          obtain ⟨x,hx⟩ := hne
          have hx' := hdense hx
          rw [he,closure_empty] at hx'
          exact hx'
        obtain ⟨x,hxW,hxO⟩ := hneWO
        obtain ⟨z,hzx⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective P.isBlowupSequence x
        have hzO : P.proj z ∈ O := by rw [hzx]; exact hxO
        have hzW : P.proj z ∈ M.cosupp := by rw [hcos,hzx]; exact hxW
        have hz := (HironakaOriginalIndependentStoppedSource.mem_cosupp_iff_of_centresAvoid
          M hM.isWellFormed P hrP.1 O hav z hzO).mpr hzW
        rw [hrP.2] at hz
        exact hz
      obtain ⟨D₀,T,R,hTR,hc,ha,hm⟩ := exists_first_centre M ((canonicalInvariant n).inv M)
        O P hcP hnot
      exact ⟨D₀,T,R,hTR,hc,ha,fun _ => hm,fun he => False.elim (hne.ne_empty he)⟩
    · have heW := Set.not_nonempty_iff_eq_empty.mp hne
      have heP := (canonical_histories_empty_of_original_cosupp_empty M hM (hcos.trans heW)
        P hcP).1
      exact ⟨X,.refl,P,BlowupTower.refl_append P,True.intro,True.intro,
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


end
end Hironaka.HironakaOriginalPureBoundaryTerminalPrefix
