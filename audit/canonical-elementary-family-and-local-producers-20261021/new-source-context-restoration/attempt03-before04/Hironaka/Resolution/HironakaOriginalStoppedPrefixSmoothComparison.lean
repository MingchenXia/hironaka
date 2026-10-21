/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalElementaryPrincipalization

/-!
# Actual smooth comparison of the embedded stopped canonical prefix

The literal conventional strict transform is computed from an original
dense open avoided by all actual centres.  Actual open Cartesian arrows
then give a whole strict-transform equality.  The original compact target
internally supplies its canonical stopped prefix and its actual smooth
source pullback; no source history or strict-set square is a premise.

The source canonical marked record is the literal marked pullback of the
target vanishing-ideal record.  Equality with the separately reduced source
vanishing ideal, and comparison with an independently stopped source
choice, are not asserted.
Blueprint: `hironaka-original-stopped-prefix-smooth-comparison-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalStoppedPrefixSmoothComparison

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower DivisorExponentAlong CanonicalCentres
  HironakaAdmissibleSequence HironakaSmoothSubmersionOriginalCompactTerminal
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionNormalCrossings
  EmbeddedFromResolution

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m}

/-- The whole conventional strict transform is the closure of its part over
any original dense open avoided by every actual centre. -/
theorem strictTransform_eq_closure_preimage_inter_of_centresAvoid
    (T : BlowupTower X D) (O : Opens X) (hT : CentresAvoid O T)
    (W : Set X) (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    strictTransform n T.proj W = closure (T.proj ⁻¹' (W ∩ (O : Set X))) := by
  apply Subset.antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨hyW, hyE⟩
    rw [mem_closure_iff_nhds]
    intro V hV
    have himg : T.proj '' V ∈ 𝓝 (T.proj y) := by
      rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
        T.contMDiff_proj hyE]
      exact image_mem_map hV
    obtain ⟨_, ⟨v, hv, rfl⟩, hvW, hvO⟩ := mem_closure_iff_nhds.mp (hdense hyW) _ himg
    exact ⟨v, hv, hvW, hvO⟩
  · apply closure_mono
    intro y hy
    exact ⟨hy.1, notMem_exceptionalLocus_of_centresAvoid O T hT y hy.2⟩

/-- Every actual pulled-back centre avoids the literal pulled-back original
good open; this is derived from the actual projection square. -/
theorem IsActualTowerPullback.centresAvoid_preimage {b : Y → X} {g : E → D}
    {Q : BlowupTower Y E} {T : BlowupTower X D}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (h : IsActualTowerPullback b Q T g) (O : Opens X) (hT : CentresAvoid O T) :
    CentresAvoid (⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩ : Opens Y) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hT.1, Set.disjoint_left.mpr ?_⟩
    intro z hzC hzO
    apply Set.disjoint_left.mp hT.2 hzC
    change T.proj (g z) ∈ O
    rw [h.proj_comm]
    exact hzO

/-- Actual openness and the original dense preserved open give the literal
whole conventional strict-transform square, including exceptional points. -/
theorem IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
    {b : Y → X} {g : E → D} {Q : BlowupTower Y E} {T : BlowupTower X D}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (h : IsActualTowerPullback b Q T g) (O : Opens X) (hT : CentresAvoid O T)
    (W : Set X) (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    strictTransform m Q.proj (b ⁻¹' W) = g ⁻¹' strictTransform n T.proj W := by
  let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
  have hQ : CentresAvoid U Q := IsActualTowerPullback.centresAvoid_preimage hb h O hT
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  have hgo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion h.isSubmersion
  have hdenQ : b ⁻¹' W ⊆ closure ((b ⁻¹' W) ∩ (U : Set Y)) := by
    have hh := preimage_mono hdense (f := b)
    rw [hbo.preimage_closure_eq_closure_preimage hb.contMDiff.continuous] at hh
    simpa only [U, Opens.coe_mk, preimage_inter] using hh
  rw [strictTransform_eq_closure_preimage_inter_of_centresAvoid Q U hQ _ hdenQ,
    strictTransform_eq_closure_preimage_inter_of_centresAvoid T O hT W hdense,
    hgo.preimage_closure_eq_closure_preimage h.isSubmersion.contMDiff.continuous]
  congr 1
  ext z
  change (b (Q.proj z) ∈ W ∧ b (Q.proj z) ∈ O) ↔
    (T.proj (g z) ∈ W ∧ T.proj (g z) ∈ O)
  rw [h.proj_comm]

/-- Original compact input constructs the actual embedded stopped target
prefix and its actual arbitrary smooth source, retaining the whole ordinary
strict-set square and the exact accumulated boundaries. -/
theorem exists_original_smooth_embedded_stopped_prefix [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let hM := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
    let P := compactCanonicalTower M hM
    let N := markedPullback (m := m) b M
    let O := regularOpen V
    let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
    ∃ (D₀ : CMfd.{u} n) (T₀ : BlowupTower X D₀) (R : BlowupTower D₀ P.1)
      (C₀ : CMfd.{u} m) (Q₀ : BlowupTower Y C₀) (g : C₀ → D₀),
      let E₀ := (geoTransformAlong M T₀).E
      let E₁ := (geoTransformAlong N Q₀).E
      let W₀ := strictTransform n T₀.proj V.carrier
      let W₁ := strictTransform m Q₀.proj (b ⁻¹' V.carrier)
      T₀.append R = P.2.val ∧
      IsCanonical M ((canonicalInvariant n).inv M) T₀ ∧ IsGeoTestTower M T₀ ∧
      CentresAvoid O T₀ ∧
      (∃ c ∈ ResolutionDriver.maxLocus ((canonicalInvariant n).inv M T₀)
        (geoTransformAlong M T₀).cosupp, T₀.proj c ∈ O) ∧
      IsActualTowerPullback b Q₀ T₀ g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      Q₀.length = T₀.length ∧ (∀ z, T₀.proj (g z) = b (Q₀.proj z)) ∧
      HolomorphicSquarePullback b g Q₀.proj T₀.proj ∧
      IsCanonical N ((canonicalInvariant m).inv N) Q₀ ∧ IsGeoTestTower N Q₀ ∧
      geoTransformAlong N Q₀ = markedPullback (m := m) g (geoTransformAlong M T₀) ∧
      E₁ = E₀.map (g ⁻¹' ·) ∧ CentresAvoid U Q₀ ∧
      CentresOver (singularLocus V) T₀ ∧ CentresOver (b ⁻¹' singularLocus V) Q₀ ∧
      IsAdmissibleBlowupSequence n X [] (singularLocus V) D₀ T₀.proj E₀ ∧
      IsAdmissibleBlowupSequence m Y [] (b ⁻¹' singularLocus V) C₀ Q₀.proj E₁ ∧
      IsSNCDivisor n E₀ ∧ IsSNCDivisor m E₁ ∧ W₁ = g ⁻¹' W₀ ∧
      IsClosedSubmanifold n W₀ ∧ IsClosedSubmanifold m W₁ ∧
      (∀ z ∈ W₀, RegularAtDim (n := n) W₀ z V.dim) ∧
      (∀ z ∈ W₁, RegularAtDim (n := m) W₁ z (V.dim + (m-n))) ∧
      HasNormalCrossings n W₀ E₀ ∧ HasNormalCrossings m W₁ E₁ ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T₀.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q₀.proj ∧
      IsProperMap T₀.proj ∧ IsProperMap Q₀.proj ∧
      Surjective T₀.proj ∧ Surjective Q₀.proj ∧
      T₀.proj '' exceptionalLocus n T₀.proj ⊆ singularLocus V ∧
      Q₀.proj '' exceptionalLocus m Q₀.proj ⊆ b ⁻¹' singularLocus V ∧
      IsIsomorphismOver n T₀.proj (O : Set X) ∧
      IsIsomorphismOver m Q₀.proj (U : Set Y) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let hM : IsInvDomain n M := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  let P := compactCanonicalTower M hM
  let N := markedPullback (m := m) b M
  let O := regularOpen V
  let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
  have hcan := compactCanonicalTower_isCanonical M hM
  have hres : IsGeoResolution M P.2.val := P.2.property.2
  obtain ⟨D₀, T₀, R, hTR, hc₀, hav₀, c, hc, hcO⟩ := exists_first_centre M
    ((canonicalInvariant n).inv M) O P.2.val hcan
    (not_centresAvoid_of_cosupp_eq_empty V hM P.2.val hres.1 hres.2)
  let hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have ht₀ : IsGeoTestTower M T₀ := hF.isGeoTestTower_of_isCanonical hM T₀ hc₀
  have hadm := hF.isAdmissibleCentre_maxLocus hM T₀ hc₀ ht₀
  have hCV : ∀ z : D₀, T₀.proj z ∈ O →
      (z ∈ ResolutionDriver.maxLocus ((canonicalInvariant n).inv M T₀)
        (geoTransformAlong M T₀).cosupp ↔ T₀.proj z ∈ V.carrier) :=
    fun z hz => mem_maxLocus_iff_of_centresAvoid hF V hM T₀ hc₀ hav₀ hc hcO hz
  have hdense := HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V
  obtain ⟨hSC, hlocal, hreg₀⟩ := HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid
    V.analytic O (fun x hx hxO => regularAtDim_of_mem_regularOpen hx hxO)
    hdense T₀ hav₀ hadm.1 hCV
  have hSM₀ : IsClosedSubmanifold n (strictTransform n T₀.proj V.carrier) :=
    ⟨isClosed_closure, fun z hz => ⟨V.dim, hreg₀ z hz⟩⟩
  have hNC₀ : HasNormalCrossings n (strictTransform n T₀.proj V.carrier)
      (geoTransformAlong M T₀).E :=
    CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun z hz =>
      ⟨_, hSC hz, hlocal z hz, hadm.2.2⟩
  have hSNC₀ : IsSNCDivisor n (geoTransformAlong M T₀).E :=
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T₀ ht₀).isWellFormed.isSNCDivisor
  obtain ⟨C₀, Q₀, g, h⟩ := exists_actual_tower hb T₀
  obtain ⟨ht₁, hrecord⟩ :=
    HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      h M hM.isWellFormed ht₀
  have hc₁ :=
    HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
      h M hM hc₀
  have hE : (geoTransformAlong N Q₀).E = (geoTransformAlong M T₀).E.map (g ⁻¹' ·) :=
    congrArg MarkedIdeal.E hrecord
  have hav₁ : CentresAvoid U Q₀ := IsActualTowerPullback.centresAvoid_preimage hb h O hav₀
  have hstrict : strictTransform m Q₀.proj (b ⁻¹' V.carrier) =
      g ⁻¹' strictTransform n T₀.proj V.carrier :=
    IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb h O hav₀ V.carrier hdense
  have hover₀ : CentresOver (singularLocus V) T₀ := by
    simpa only [O, regularOpen, Opens.coe_mk, compl_compl] using
      centresOver_compl_of_centresAvoid O T₀ hav₀
  have hover₁ : CentresOver (b ⁻¹' singularLocus V) Q₀ := by
    simpa only [U, O, regularOpen, Opens.coe_mk, preimage_compl, compl_compl] using
      centresOver_compl_of_centresAvoid U Q₀ hav₁
  have hSM₁ : IsClosedSubmanifold m (strictTransform m Q₀.proj (b ⁻¹' V.carrier)) := by
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion h.isSubmersion hSM₀
  have hreg₁ : ∀ z ∈ strictTransform m Q₀.proj (b ⁻¹' V.carrier),
      RegularAtDim (n := m) (strictTransform m Q₀.proj (b ⁻¹' V.carrier)) z (V.dim + (m-n)) := by
    rw [hstrict]
    intro z hz
    exact regularAtDim_preimage_submersion (h.isSubmersion.isSubmersionAt z) (hreg₀ (g z) hz)
  have hSNC₁ : IsSNCDivisor m (geoTransformAlong N Q₀).E := by
    rw [hE]
    exact isSNCDivisor_preimage_submersion h.isSubmersion _ hSNC₀
  have hNC₁ : HasNormalCrossings m (strictTransform m Q₀.proj (b ⁻¹' V.carrier))
      (geoTransformAlong N Q₀).E := by
    rw [hstrict, hE]
    exact hasNormalCrossings_preimage_submersion h.isSubmersion hNC₀
  have hExc₀ : T₀.proj '' exceptionalLocus n T₀.proj ⊆ singularLocus V := by
    simpa only [O, regularOpen, Opens.coe_mk, compl_compl] using
      image_exceptionalLocus_subset_compl O T₀ hav₀
  have hExc₁ : Q₀.proj '' exceptionalLocus m Q₀.proj ⊆ b ⁻¹' singularLocus V := by
    simpa only [U, O, regularOpen, Opens.coe_mk, preimage_compl, compl_compl] using
      image_exceptionalLocus_subset_compl U Q₀ hav₁
  have hiso₀ : IsIsomorphismOver n T₀.proj (O : Set X) :=
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T₀.isBlowupSequence hExc₀
  have hiso₁ : IsIsomorphismOver m Q₀.proj (U : Set Y) := by
    simpa only [U, O, regularOpen, Opens.coe_mk, preimage_compl] using
      HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        Q₀.isBlowupSequence hExc₁
  exact ⟨D₀, T₀, R, C₀, Q₀, g, hTR, hc₀, ht₀, hav₀, ⟨c, hc, hcO⟩,
    h, h.isSubmersion, h.length_eq, h.proj_comm, h.universal, hc₁, ht₁, hrecord, hE, hav₁,
    hover₀, hover₁, isAdmissibleBlowupSequence_proj M _ T₀ ht₀ hover₀,
    isAdmissibleBlowupSequence_proj N _ Q₀ ht₁ hover₁,
    hSNC₀, hSNC₁, hstrict, hSM₀, hSM₁, hreg₀, hreg₁, hNC₀, hNC₁,
    T₀.contMDiff_proj, Q₀.contMDiff_proj,
    HironakaLocalPrincipalization.isProperMap_proj T₀,
    HironakaLocalPrincipalization.isProperMap_proj Q₀,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T₀.isBlowupSequence,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective Q₀.isBlowupSequence,
    hExc₀, hExc₁, hiso₀, hiso₁⟩

end

end Hironaka.HironakaOriginalStoppedPrefixSmoothComparison
