/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureBoundaryTerminalPrefix
import Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace

/-! # Original local pure boundary resolution with one target before every source

Only the original globally analytic pure carrier, original ordered SNC boundary
and prescribed open inside a compact set are input. The actual local canonical
terminal history is produced internally; its intrinsic whole original ideal
and every first-meeting prefix field are proved for that SAME history.
No compactness of the carrier or smooth source is imposed.
Blueprint: `hironaka-original-local-pure-boundary-canonical-prefix-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalPureBoundaryCanonicalPrefix
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  MarkedIdealBiholomorphism RestrictEmptyTower CanonicalCentres HironakaAdmissibleSequence
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalPureBoundaryTerminalPrefix
  HironakaOriginalPureBoundaryIndependentSource HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual WHOLE original local ideal record, including the literal list. -/
theorem original_open_record (U : Opens X) (W : Set X) (E₀ : List (Set X)) :
    MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ,E₀,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) =
      (⟨univ,E₀.map ((Subtype.val : U → X) ⁻¹' ·),
        vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' W),1⟩ : MarkedIdeal n U) := by
  change (⟨(Subtype.val : U → X) ⁻¹' univ,E₀.map ((Subtype.val : U → X) ⁻¹' ·),
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) W),1⟩ :
      MarkedIdeal n U) = _
  rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
    (isSubmersion_val U) W]

/-- Analyticity, actual unchanged pure dimension, literal SNC boundary and
original boundary-density all hold on the SAME prescribed open, even empty. -/
theorem original_open_data (U : Opens X) (W : Set X)
    (hWa : IsComplexAnalyticSubset (n := n) W) (d : ℕ)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
    IsComplexAnalyticSubset (n := n) WU ∧
      WU ⊆ closure (regularLocus (n := n) WU d) ∧
      IsSNCDivisor n EU ∧ WU ⊆ closure (WU \ ⋃ H ∈ EU, H) := by
  dsimp only
  have hb := isSubmersion_val U
  refine ⟨AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa,
    ?_,isSNCDivisor_preimage_submersion hb E₀ hE₀,boundary_density_preimage (Y := CMfd.of (n := n) U) (b := (Subtype.val : U → X)) hb W E₀ hE₀W⟩
  simpa only [Nat.sub_self,Nat.add_zero] using pure_regular_density_preimage (Y := CMfd.of (n := n) U) (b := (Subtype.val : U → X)) hb W d hpure

/-- ORIGINAL-ONLY local data internally produce actual terminal P and its
literal SAME first-meeting prefix/tail, with the complete elementary geometry. -/
theorem exists_local_original_pure_boundary_canonical_prefix
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
    let hWaU := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
    let hEU := isSNCDivisor_preimage_submersion (isSubmersion_val U) E₀ hE₀
    let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
    let O := boundaryGoodOpen (X := CMfd.of (n := n) U) WU hWaU d EU hEU
    let F := WU \ regularLocus (n := n) WU d ∪ WU ∩ ⋃ H ∈ EU, H
    ∃ (Z : CMfd.{u} n) (P : BlowupTower (CMfd.of (n := n) U) Z),
      IsCanonical M ((canonicalInvariant n).inv M) P ∧ IsGeoResolution M P ∧
      ∃ (D : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) D) (R : BlowupTower D Z),
        T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
        IsGeoTestTower M T ∧ CentresAvoid O T ∧
        (WU.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T)
          (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
        (WU = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧ CentresOver F T ∧
        IsAdmissibleBlowupSequence n U EU F D T.proj (geoTransformAlong M T).E ∧
        IsSNCDivisor n (geoTransformAlong M T).E ∧
        IsClosedSubmanifold n (strictTransform n T.proj WU) ∧
        (∀ z ∈ strictTransform n T.proj WU,
          RegularAtDim (n := n) (strictTransform n T.proj WU) z d) ∧
        HasNormalCrossings n (strictTransform n T.proj WU) (geoTransformAlong M T).E ∧
        exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H ∧
        (⋃ H ∈ (geoTransformAlong M T).E.drop EU.length, H) ⊆ T.proj ⁻¹' F ∧
        T.proj ⁻¹' (WU \ regularLocus (n := n) WU d) ⊆ exceptionalLocus n T.proj ∧
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
        IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj Fᶜ := by
  dsimp only
  let M₀ : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
  have hM₀ : IsInvDomain n M₀ := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  obtain ⟨Z,P,hcP,hrP⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hM₀ hK U hUK
  have hrecord : MarkedIdeal.pullback (Subtype.val : U → X) M₀ = M :=
    original_open_record U W E₀
  rw [hrecord] at hcP hrP
  obtain ⟨hWaU,hpureU,hEU,hEUW⟩ := original_open_data U W hWa d hpure E₀ hE₀ hE₀W
  exact ⟨Z,P,hcP,hrP,exists_pure_boundary_prefix_of_terminal WU hWaU d hd hpureU EU hEU hEUW P hcP hrP⟩

/-- Fix the original-only local target FIRST. Every genuine smooth source then
has an actual pulled prefix; EVERY independently stopped intrinsic source S
compares uniquely, with whole strict carrier and explicitly filtered boundary.
This theorem does not internally select S or assume a comparison certificate. -/
theorem exists_local_original_pure_boundary_stopped_smooth_source
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
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
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧
          IsCanonical M' ((canonicalInvariant m).inv M') Q ∧ IsGeoTestTower M' Q ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj ∧
          strictTransform m Q.proj W' = g ⁻¹' strictTransform n T.proj WU ∧
          (geoTransformAlong M' Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) ∧
          ∀ (F : CMfd.{u} m) (S : BlowupTower Y F),
            IsCanonical M' ((canonicalInvariant m).inv M') S → CentresAvoid V S →
            (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
              (geoTransformAlong M' S).cosupp, S.proj z ∈ V) →
            ∃ η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C,
              (∀ z, Q.proj (η z) = S.proj z) ∧
              (∀ η' : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C,
                (∀ z, Q.proj (η' z) = S.proj z) → η' = η) ∧
              let G := g ∘ η
              Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
              (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
              IsGeoTestTower M' S ∧ IsSNCDivisor m (geoTransformAlong M' S).E ∧
              strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj WU ∧
              (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty) =
                ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
              IsClosedSubmanifold m (strictTransform m S.proj W') ∧
              (∀ z ∈ strictTransform m S.proj W',
                RegularAtDim (n := m) (strictTransform m S.proj W') z (d+(m-n))) ∧
              HasNormalCrossings m (strictTransform m S.proj W') (geoTransformAlong M' S).E := by
  dsimp only
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let M : MarkedIdeal n U := ⟨univ,EU,vanishingIdeal (n := n) WU,1⟩
  obtain ⟨hWaU,hpureU,hEU,hEUW⟩ := original_open_data U W hWa d hpure E₀ hE₀ hE₀W
  let O := boundaryGoodOpen (X := CMfd.of (n := n) U) WU hWaU d EU hEU
  have hM : IsInvDomain n M := HironakaEmbeddedBoundary.isInvDomain_boundary hWaU
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpureU) hEU
  obtain ⟨Z,P,hcP,hrP,D,T,R,hTarget⟩ :=
    exists_local_original_pure_boundary_canonical_prefix W hWa d hd hpure E₀ hE₀ hE₀W U hK hUK
  have hcopy := hTarget
  rcases hcopy with ⟨_hTR,hcT,htT,haT,hmT,_heT,_hoverT,_hadmT,_hSNCT,hSMT,hrT,hNCT,
    _hExcT,_hNewT,_hSingT,_hholT,_hproperT,_hsurjT,_hisoT⟩
  refine ⟨Z,P,D,T,R,hcP,hrP,hTarget,?_⟩
  intro m Y b hb
  let W' := b ⁻¹' WU
  let E' := EU.map (b ⁻¹' ·)
  let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
  let N := markedPullback (m := m) b M
  have hEq : N = M' := by
    change (⟨b ⁻¹' univ,EU.map (b ⁻¹' ·),
      GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) WU),1⟩ : MarkedIdeal m Y) = _
    rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb WU]
  obtain ⟨C,Q,g,hactual⟩ := exists_actual_tower hb T
  have hcQ : IsCanonical M' ((canonicalInvariant m).inv M') Q := by
    rw [← hEq]
    exact HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
      hactual M hM hcT
  have hdict := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    hactual M hM.isWellFormed htT
  have htQ : IsGeoTestTower M' Q := by rw [← hEq]; exact hdict.1
  have hEQ : (geoTransformAlong M' Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) := by
    rw [← hEq]
    exact congrArg MarkedIdeal.E hdict.2
  have hdense : WU ⊆ closure (WU ∩ (O : Set U)) :=
    HironakaEmbeddedBoundary.subset_closure_inter_compl hpureU
      (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hEU.1) hEUW
  have hstrict := HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.strictTransform_preimage_of_centresAvoid
    hb hactual O haT WU hdense
  refine ⟨C,Q,g,hactual,hcQ,htQ,hactual.isSubmersion,hactual.length_eq,
    hactual.proj_comm,hactual.universal,hstrict,hEQ,?_⟩
  intro F S hcS haS hmS
  obtain ⟨η,hη,huniq,hG,hproj,hcart,htS,hSNCS,hstrictS,hboundary,hSM,hr,hNC⟩ :=
    independent_intrinsic_source_prefix_comparison WU hWaU d hd hpureU EU hEU hEUW hb
      hactual hcT haT hmT S hcS haS hmS
  exact ⟨η,hη,huniq,hG,hproj,hcart,htS,hSNCS,hstrictS,hboundary,hSM hSMT,hr hrT,hNC hNCT⟩

end
end Hironaka.HironakaOriginalLocalPureBoundaryCanonicalPrefix
