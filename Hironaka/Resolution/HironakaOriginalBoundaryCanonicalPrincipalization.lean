/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalElementaryPrincipalization
import Hironaka.Resolution.HironakaPrincipalizationBoundary

/-!
# Canonical elementary principalization with original SNC boundary

Compactness of the original zero locus internally supplies the actual finite
canonical terminal tower, retaining the entire elementary dictionary and its
identification with the original global terminal map.  Arbitrary smooth
sources are constructed from that same tower, without source compactness.

The preliminary whole ordered boundary formula for actual all-empty towers
also retains every original boundary member and every empty chronological step.
Blueprint: `hironaka-original-boundary-canonical-principalization-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalBoundaryCanonicalPrincipalization

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaSmoothSubmersionOriginalCompactTerminal
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}

/-- Every original ordered member survives as its literal inverse image;
every actual empty step appends exactly one empty boundary entry. -/
theorem boundary_of_all_empty_tower (M : MarkedIdeal n X)
    (hE : ∀ H ∈ M.E, IsClosed H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D), IsEmptyTower T →
      (geoTransformAlong M T).E = M.E.map (T.proj ⁻¹' ·) ++ List.replicate T.length ∅
  | _, .refl, _ => by simp
  | _, .step T C π hπ, he => by
    rcases he with ⟨heT,rfl⟩
    rw [geoTransformAlong_step,geoTransform_E,boundary_of_all_empty_tower M hE T heT]
    simp only [List.map_append,List.map_map,List.map_replicate,preimage_empty,Function.comp_def]
    have hmap : M.E.map (fun H => BlowupStrictSubmanifold.geoStrictTransform π ∅ (T.proj ⁻¹' H)) =
        M.E.map ((T.step ∅ π hπ).proj ⁻¹' ·) := by
      apply List.map_congr_left
      intro H hH
      change closure (π ⁻¹' ((T.proj ⁻¹' H) \ ∅)) = _
      rw [sdiff_empty]
      exact ((hE H hH).preimage (T.contMDiff_proj.comp hπ.contMDiff).continuous).closure_eq
    rw [hmap]
    simp only [BlowupStrictSubmanifold.geoStrictTransform,empty_sdiff,preimage_empty,
      closure_empty,BlowupTower.length_step,List.replicate_add,List.replicate_one,List.append_assoc]

/-- The genuine compact-cosupport driver selects an actual canonical terminal
tower from original marked input, with no incoming finite history. -/
def compactCosupportCanonicalTower (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hK : IsCompact M.cosupp) :
    Σ D : CMfd.{u} n, {T : BlowupTower X D //
      IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T} :=
  let h := exists_isGeoResolution_isCanonical_of_isCompact (canonicalInvariant n) hM hK
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec⟩

private theorem boundary_principalization_dictionary
    (I : GermIdeal n X) (E₀ : List (Set X))
    (hM : IsInvDomain n (⟨univ,E₀,I,1⟩ : MarkedIdeal n X))
    (T : BlowupTower X D)
    (hc : IsCanonical (⟨univ,E₀,I,1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ,E₀,I,1⟩ : MarkedIdeal n X)) T)
    (hr : IsGeoResolution (⟨univ,E₀,I,1⟩ : MarkedIdeal n X) T) :
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let E := (geoTransformAlong M T).E
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ CentresOver I.zeroLocus T ∧
      IsAdmissibleBlowupSequence n X E₀ I.zeroLocus D T.proj E ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧ IsSNCDivisor n E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ E.drop E₀.length, H ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      ∃ η : originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
        ∀ z, T.proj (η z) = originalTerminalGluedProjection M hM z := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  have hcos : M.cosupp = I.zeroLocus := cosupp_univ_one hI
  have hover : CentresOver I.zeroLocus T := by
    rw [← hcos]
    exact centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hI T hr.1
  have hpb : GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hr
  have hsupp : (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus := by
    rw [EffectiveDivisor.support,← hpb,BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hI]
  have hiso : IsIsomorphismOver n T.proj I.zeroLocusᶜ := by
    refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence ?_
    rintro x ⟨z,hz,rfl⟩
    have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
    rw [hsupp] at hz'
    exact hz'
  exact ⟨T.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence,hover,
    isAdmissibleBlowupSequence_proj M I.zeroLocus T hr.1 hover,hpb,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hr.1).isWellFormed.isSNCDivisor,
    HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M
      hM.isWellFormed.isSNCDivisor.1 T,hsupp,HironakaPrincipalization.exceptionalLocus_subset_support T,hiso,
    originalTerminalFiniteBiholomorphism M hM T hc hr,
    originalTerminalFiniteBiholomorphism_proj M hM T hc hr⟩


/-- The original ideal, compact zero locus and original SNC boundary internally
produce the SAME finite canonical elementary principalization and glued map. -/
theorem canonical_boundary_principalization
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
    let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
    let P := compactCosupportCanonicalTower M hM hK
    let T := P.2.val
    let E := (geoTransformAlong M T).E
    IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ CentresOver I.zeroLocus T ∧
      IsAdmissibleBlowupSequence n X E₀ I.zeroLocus P.1 T.proj E ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧ IsSNCDivisor n E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ E.drop E₀.length, H ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' I.zeroLocus ∧
      exceptionalLocus n T.proj ⊆ (exceptionalDivisor T).support ∧
      IsIsomorphismOver n T.proj I.zeroLocusᶜ ∧
      ∃ η : originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ P.1,
        ∀ z, T.proj (η z) = originalTerminalGluedProjection M hM z := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
  let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
  let P := compactCosupportCanonicalTower M hM hK
  exact ⟨P.2.property.1,P.2.property.2,
    boundary_principalization_dictionary I E₀ hM P.2.val P.2.property.1 P.2.property.2⟩


/-- Actual smooth source data are built from the SAME compact-cosupport target
principalization, retaining the whole ideal and entire indexed boundary. -/
theorem canonical_boundary_principalization_smooth_base_change
    (I : GermIdeal n X) (hI : I.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ I x)
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
    let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
    let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
    let P := compactCosupportCanonicalTower M hM hK
    let T := P.2.val
    let hc := P.2.property.1
    let hr := P.2.property.2
    let N := markedPullback (m := m) b M
    let hN := original_ambient_domain_pullback hb M hM
    let Q := chosenActualTower defaultSmoothBlowupChoices hb T
    let S := Q.2.1
    let hS := originalFiniteSmoothSourceHistory_properties hb M hM T hc hr
    let g := terminalSmoothMap hb M hM S T hS.1 hc hS.2 hr
    let G := originalGlobalFiniteSmoothMap hb M hM S T hS.1 hc hS.2 hr
    let ηX := originalTerminalFiniteBiholomorphism M hM T hc hr
    let ηY := originalTerminalFiniteBiholomorphism N hN S hS.1 hS.2
    IsCanonical N ((canonicalInvariant m).inv N) S ∧ IsGeoResolution N S ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      GermIdeal.pullback (m := m) S.proj (GermIdeal.pullback (m := m) b I) = (exceptionalDivisor S).ideal ∧
      IsSNCDivisor m (geoTransformAlong N S).E ∧
      (geoTransformAlong N S).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ z, T.proj (g z) = b (S.proj z)) ∧ HolomorphicSquarePullback b g S.proj T.proj ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z) = b (originalTerminalGluedProjection N hN z)) ∧
      HolomorphicSquarePullback b G (originalTerminalGluedProjection N hN) (originalTerminalGluedProjection M hM) ∧
      (∀ z, ηX (G z) = g (ηY z)) ∧
      (∀ z, T.proj (ηX z) = originalTerminalGluedProjection M hM z) ∧
      (∀ z, S.proj (ηY z) = originalTerminalGluedProjection N hN z) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,I,1⟩
  let hM := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor hI hne hE₀
  let hK : IsCompact M.cosupp := (show M.cosupp = I.zeroLocus from cosupp_univ_one hI).symm ▸ hZ
  let P := compactCosupportCanonicalTower M hM hK
  let T := P.2.val
  let hc := P.2.property.1
  let hr := P.2.property.2
  let N := markedPullback (m := m) b M
  let hN := original_ambient_domain_pullback hb M hM
  let Q := chosenActualTower defaultSmoothBlowupChoices hb T
  let S := Q.2.1
  let hS := originalFiniteSmoothSourceHistory_properties hb M hM T hc hr
  let g := terminalSmoothMap hb M hM S T hS.1 hc hS.2 hr
  let G := originalGlobalFiniteSmoothMap hb M hM S T hS.1 hc hS.2 hr
  let ηX := originalTerminalFiniteBiholomorphism M hM T hc hr
  let ηY := originalTerminalFiniteBiholomorphism N hN S hS.1 hS.2
  have hg := terminalSmoothMap_properties hb M hM S T hS.1 hc hS.2 hr
  have hG := originalGlobalFiniteSmoothMap_properties hb M hM S T hS.1 hc hS.2 hr
  have hraw : Q.2.2.val = g := terminalSmoothMap_unique hb M hM S T hS.1 hc hS.2 hr
    Q.2.2.val Q.2.2.property.isSubmersion.contMDiff Q.2.2.property.proj_comm Q.2.2.property.universal
  have hrecord := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    Q.2.2.property M hM.isWellFormed hr.1).2
  have hE : (geoTransformAlong N S).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) := by
    have hh := congrArg MarkedIdeal.E hrecord
    change (geoTransformAlong N S).E = (geoTransformAlong M T).E.map (Q.2.2.val ⁻¹' ·) at hh
    rw [hraw] at hh
    exact hh
  have hpbS : GermIdeal.pullback (m := m) S.proj (GermIdeal.pullback (m := m) b I) =
      (exceptionalDivisor S).ideal :=
    pullback_eq_exceptionalDivisor_of_isGeoResolution N rfl hN.isWellFormed.isCoherent rfl S hS.2
  refine ⟨hS.1,hS.2,pullback_eq_exceptionalDivisor_of_isGeoResolution M rfl hI rfl T hr,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hr.1).isWellFormed.isSNCDivisor,hpbS,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hN S hS.2.1).isWellFormed.isSNCDivisor,
    hE,hg.1,hg.2.1,hg.2.2,hG.1,hG.2.1,hG.2.2,?_,
    originalTerminalFiniteBiholomorphism_proj M hM T hc hr,
    originalTerminalFiniteBiholomorphism_proj N hN S hS.1 hS.2⟩
  intro z
  change ηX (ηX.symm (g (ηY z))) = g (ηY z)
  exact ηX.apply_symm_apply _

end

end Hironaka.HironakaOriginalBoundaryCanonicalPrincipalization
