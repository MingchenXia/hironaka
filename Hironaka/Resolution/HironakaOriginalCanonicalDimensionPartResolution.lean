/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource
import Hironaka.Resolution.HironakaOriginalLocalPureBoundaryIndependentSource

/-!
# Each original dimension part has its own canonical elementary family

The actual fixed compact pure target is selected before every smooth source.
Dimension-part inputs keep their OWN vanishing ideal, regular locus and bad set.
Blueprint: `hironaka-original-canonical-dimension-part-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCanonicalDimensionPartResolution
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  RestrictEmptyTower CanonicalCentres HironakaAdmissibleSequence
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalPureBoundaryTerminalPrefix
  HironakaOriginalPureBoundaryIndependentSource HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaOriginalLocalPureBoundaryIndependentSource
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionRelativeControlledTower HironakaOriginalIndependentStoppedSource
  HironakaEmbeddedDimensionParts
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X : CMfd.{u} n}

/-- A transparent OUTPUT containing the actual target BEFORE all independent sources. -/
def HasIndependentPureBoundaryResolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (d : ℕ)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) : Prop :=
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  let O := boundaryGoodOpen (X := X) W hWa d E₀ hE₀
  let F₀ := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
  ∃ (Z : CMfd.{u} n) (P : BlowupTower (X) Z)
    (D : CMfd.{u} n) (T : BlowupTower (X) D) (R : BlowupTower D Z),
    IsCanonical M ((canonicalInvariant n).inv M) P ∧ IsGeoResolution M P ∧
    (T.append R = P ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧
      IsGeoTestTower M T ∧ CentresAvoid O T ∧
      (W.Nonempty → ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T)
        (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      (W = ∅ → T.length = 0 ∧ IsEmptyTower P) ∧ CentresOver F₀ T ∧
      IsAdmissibleBlowupSequence n X E₀ F₀ D T.proj (geoTransformAlong M T).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ z ∈ strictTransform n T.proj W,
        RegularAtDim (n := n) (strictTransform n T.proj W) z d) ∧
      HasNormalCrossings n (strictTransform n T.proj W) (geoTransformAlong M T).E ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong M T).E.drop E₀.length, H) ⊆ T.proj ⁻¹' F₀ ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj F₀ᶜ ∧
      (E₀ = [] → exceptionalLocus n T.proj = ⋃ H ∈ (geoTransformAlong M T).E, H ∧
        (⋃ H ∈ (geoTransformAlong M T).E, H) = T.proj ⁻¹' (W \ regularLocus (n := n) W d))) ∧
    ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X)
      (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      let W' := b ⁻¹' W
      let E' := E₀.map (b ⁻¹' ·)
      let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
      let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
      let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
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
        strictTransform m S.proj W' = G ⁻¹' strictTransform n T.proj W ∧
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
        IsProperMap S.proj ∧ Surjective S.proj ∧ IsIsomorphismOver m S.proj F'ᶜ ∧
        (E₀ = [] → exceptionalLocus m S.proj = ⋃ H ∈ (geoTransformAlong M' S).E, H ∧
          (⋃ H ∈ (geoTransformAlong M' S).E, H) = S.proj ⁻¹'
            (W' \ regularLocus (n := m) W' (d+(m-n))))



private theorem empty_boundary_exact {X D : CMfd.{u} n} (W : Set X) (d : ℕ)
    (E : List (Set X)) (Ef : List (Set D)) (T : BlowupTower X D) (hE : E = [])
    (hexc : exceptionalLocus n T.proj ⊆ ⋃ H ∈ Ef.drop E.length, H)
    (hborn : (⋃ H ∈ Ef.drop E.length, H) ⊆ T.proj ⁻¹'
      (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E, H))
    (hsing : T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj) :
    exceptionalLocus n T.proj = ⋃ H ∈ Ef, H ∧
      (⋃ H ∈ Ef, H) = T.proj ⁻¹' (W \ regularLocus (n := n) W d) := by
  have hexc' : exceptionalLocus n T.proj ⊆ ⋃ H ∈ Ef, H := by simpa [hE] using hexc
  have hborn' : (⋃ H ∈ Ef, H) ⊆ T.proj ⁻¹' (W \ regularLocus (n := n) W d) := by
    simpa [hE] using hborn
  exact ⟨Set.Subset.antisymm hexc' (hborn'.trans hsing),
    Set.Subset.antisymm hborn' (hsing.trans hexc')⟩

/-- Original compact pure data choose ONE actual target BEFORE every arbitrary
smooth source and internally construct its independently stopped intrinsic source. -/
theorem exists_original_compact_pure_fixed_target_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (d : ℕ) (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    HasIndependentPureBoundaryResolution W hWa d E₀ hE₀ := by
  unfold HasIndependentPureBoundaryResolution
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E₀,vanishingIdeal (n := n) W,1⟩
  have hM : IsInvDomain n M := HironakaEmbeddedBoundary.isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let hC : IsCompact M.cosupp :=
    (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal (n := n) hWa.isClosed E₀).symm ▸ hK
  let P := compactCosupportCanonicalTower M hM hC
  let O := boundaryGoodOpen W hWa d E₀ hE₀
  let F₀ := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
  obtain ⟨D,T,R,hTarget⟩ :=
    exists_original_pure_boundary_canonical_prefix W hWa hK d hd hpure E₀ hE₀ hE₀W
  have hcopy := hTarget
  rcases hcopy with ⟨hTR,hcT,htT,haT,hmT,heT,hoverT,hadmT,hSNCT,hSMT,hrT,hNCT,
    hExcT,hNewT,hSingT,hholT,hproperT,hsurjT,hisoT⟩
  refine ⟨P.1,P.2.val,D,T,R,P.2.property.1,P.2.property.2,?_,?_⟩
  · exact ⟨hTR,hcT,htT,haT,hmT,heT,hoverT,hadmT,hSNCT,hSMT,hrT,hNCT,
      hExcT,hNewT,hSingT,hholT,hproperT,hsurjT,hisoT,
      fun he => empty_boundary_exact W d E₀ _ T he hExcT hNewT hSingT⟩
  intro m Y b hb
  let W' := b ⁻¹' W
  let E' := E₀.map (b ⁻¹' ·)
  let M' : MarkedIdeal m Y := ⟨univ,E',vanishingIdeal (n := m) W',1⟩
  let N := markedPullback (m := m) b M
  let hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
  let hEY := isSNCDivisor_preimage_submersion hb E₀ hE₀
  let V := boundaryGoodOpen W' hWaY (d+(m-n)) E' hEY
  let F' := W' \ regularLocus (n := m) W' (d+(m-n)) ∪ W' ∩ ⋃ H ∈ E', H
  have hEq : N = M' := by
    change (⟨b ⁻¹' univ,E₀.map (b ⁻¹' ·),
      GermIdeal.pullback (m := m) b (vanishingIdeal (n := n) W),1⟩ : MarkedIdeal m Y) = _
    rw [preimage_univ,HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion hb W]
  have hM' : IsInvDomain m M' := by rw [← hEq]; exact original_ambient_domain_pullback hb M hM
  have hcos : M'.cosupp = W' := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWaY.isClosed E'
  obtain ⟨ZB,B,gP,hactualB⟩ := exists_actual_tower hb P.2.val
  have hcB : IsCanonical M' ((canonicalInvariant m).inv M') B := by
    rw [← hEq]
    exact IsActualTowerPullback.original_ambient_canonical hactualB M hM P.2.property.1
  have hrB : IsGeoResolution M' B := by
    rw [← hEq]
    refine ⟨(IsActualTowerPullback.relative_marked_dictionary hactualB M hM.isWellFormed P.2.property.2.1).1,?_⟩
    rw [IsActualTowerPullback.relative_cosupport_dictionary hactualB M hM.isWellFormed P.2.property.2.1,
      P.2.property.2.2,preimage_empty]
  obtain ⟨CQ,Q,g,hactualQ⟩ := exists_actual_tower hb T
  have hSource : ∃ (C : CMfd.{u} m) (S : BlowupTower Y C) (R' : BlowupTower C ZB),
      S.append R' = B ∧ IsCanonical M' ((canonicalInvariant m).inv M') S ∧ CentresAvoid V S ∧
      (W'.Nonempty → ∃ z ∈ maxLocus ((canonicalInvariant m).inv M' S)
        (geoTransformAlong M' S).cosupp, S.proj z ∈ V) ∧
      (¬ W'.Nonempty → S.length = 0 ∧ IsEmptyTower B) := by
    by_cases hY : Nonempty Y
    · obtain ⟨y⟩ := hY
      have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hb.isSubmersionAt y)
      have hdm : d+(m-n)<m := by omega
      have hpureY := pure_regular_density_preimage (X := X) (Y := Y) hb W d hpure
      have hEYD := boundary_density_preimage (X := X) (Y := Y) hb W E₀ hE₀W
      obtain ⟨C,S,R',hSR,hcS,_htS,haS,hmS,heS,_hrest⟩ :=
        exists_pure_boundary_prefix_of_terminal W' hWaY (d+(m-n)) hdm hpureY E' hEY hEYD B hcB hrB
      exact ⟨C,S,R',hSR,hcS,haS,hmS,fun hne => heS (Set.not_nonempty_iff_eq_empty.mp hne)⟩
    · have hne : ¬ W'.Nonempty := by rintro ⟨y,_hy⟩; exact hY ⟨y⟩
      have heB := (canonical_histories_empty_of_original_cosupp_empty M' hM'
        (hcos.trans (Set.not_nonempty_iff_eq_empty.mp hne)) B hcB).1
      exact ⟨Y,.refl,B,BlowupTower.refl_append B,True.intro,True.intro,
        fun hh => False.elim (hne hh),fun _ => ⟨rfl,heB⟩⟩
  obtain ⟨C,S,R',hSR,hcS,haS,hmS,heS⟩ := hSource
  obtain ⟨η,hη,huniq,hG,hproj,hcart,htS,hSNCS,hstrict,hboundary,hSMof,hrof,hNCof⟩ :=
    independent_intrinsic_source_prefix_comparison (F := C) W hWa d hd hpure E₀ hE₀ hE₀W
      hb hactualQ hcT haT hmT S hcS haS hmS
  have hSM := hSMof hSMT
  have hr := hrof hrT
  have hNC := hNCof hNCT
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
      S.isBlowupSequence hExcF,?_⟩
  · exact (boundary_bad_set_preimage_eq (X := X) (Y := Y) hb W d E₀).symm
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF
  · intro he
    have hE' : E' = [] := by simp [E',he]
    apply empty_boundary_exact W' (d+(m-n)) E' _ S hE'
    · rw [← hsupp]; exact hexc
    · rw [← hsupp]; exact hsuppF
    · exact HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus
        S.contMDiff_proj hWaY.isClosed hr

/-- A compact original dimension part uses its OWN pure marked datum and bad set. -/
theorem exists_dimensionPart_compact_canonical_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (k : ℕ) (hk : k < n) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀A : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H)) :
    HasIndependentPureBoundaryResolution (dimensionPart (n := n) W k)
      (isComplexAnalyticSubset_dimensionPart hWa k) k E₀ hE₀ :=
  exists_original_compact_pure_fixed_target_family _ (isComplexAnalyticSubset_dimensionPart hWa k)
    (hK.of_isClosed_subset isClosed_closure (dimensionPart_subset hWa.isClosed k)) k hk
    (subset_closure_regularLocus_dimensionPart hWa.isClosed k) E₀ hE₀ hE₀A

/-- Compact ambient spaces supply the actual compactness of each own original part. -/
theorem exists_dimensionPart_compact_ambient_canonical_family [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k < n)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀A : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H)) :
    HasIndependentPureBoundaryResolution (dimensionPart (n := n) W k)
      (isComplexAnalyticSubset_dimensionPart hWa k) k E₀ hE₀ :=
  exists_dimensionPart_compact_canonical_family W hWa hWa.isClosed.isCompact k hk E₀ hE₀ hE₀A

/-- Empty initial boundary retains the SAME target/source exact full
exceptional-locus and OWN singular inverse-image equalities in the output. -/
theorem exists_dimensionPart_compact_empty_boundary_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W)
    (k : ℕ) (hk : k < n) :
    HasIndependentPureBoundaryResolution (dimensionPart (n := n) W k)
      (isComplexAnalyticSubset_dimensionPart hWa k) k [] isSNCDivisor_nil := by
  apply exists_dimensionPart_compact_canonical_family W hWa hK k hk [] isSNCDivisor_nil
  simpa using (subset_closure : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k))

/-- The original compact-ambient empty-boundary dimension-part form. -/
theorem exists_dimensionPart_compact_ambient_empty_boundary_family [CompactSpace X]
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k < n) :
    HasIndependentPureBoundaryResolution (dimensionPart (n := n) W k)
      (isComplexAnalyticSubset_dimensionPart hWa k) k [] isSNCDivisor_nil :=
  exists_dimensionPart_compact_empty_boundary_family W hWa hWa.isClosed.isCompact k hk

/-- The prescribed real domain resolves the restricted OWN part; the whole
original mixed carrier's bad set is never substituted. -/
theorem exists_dimensionPart_prescribed_local_canonical_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k < n)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀A : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H))
    (U : Opens X) {L : Set X} (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
    HasIndependentLocalPureBoundaryResolution (dimensionPart (n := n) W k)
      (isComplexAnalyticSubset_dimensionPart hWa k) k E₀ hE₀ U :=
  exists_local_original_independently_stopped_intrinsic_source _ (isComplexAnalyticSubset_dimensionPart hWa k)
    k hk (subset_closure_regularLocus_dimensionPart hWa.isClosed k) E₀ hE₀ hE₀A U hL hUL

/-- One actual neighbourhood of any compact set is fixed before every smooth
source, for THIS dimension part's own pure datum and own bad set. -/
theorem exists_dimensionPart_compact_neighbourhood_canonical_family
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) (hk : k < n)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀A : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      HasIndependentLocalPureBoundaryResolution (dimensionPart (n := n) W k)
        (isComplexAnalyticSubset_dimensionPart hWa k) k E₀ hE₀ U :=
  exists_original_pure_boundary_canonical_local _ (isComplexAnalyticSubset_dimensionPart hWa k)
    k hk (subset_closure_regularLocus_dimensionPart hWa.isClosed k) E₀ hE₀ hE₀A hK

end
end Hironaka.HironakaOriginalCanonicalDimensionPartResolution
