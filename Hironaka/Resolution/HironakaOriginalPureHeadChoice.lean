/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison

/-!
# Actual independently chosen pure-head stages across base and empty boundary

Natural whole ideal and intrinsic good-open dictionaries discharge the inputs
to the genuine terminal/first-meeting stage comparisons. Empty carriers use
actual terminality, never an invented next maximum.
Blueprint: `hironaka-original-pure-head-choice-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPureHeadChoice
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalBoundaryEmptyBaseComparison
  HironakaOriginalPureBoundaryCanonicalPrefix HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaOriginalIndependentStoppedSource RestrictEmptyTower
variable {n : ℕ} {X X' D D' : CMfd.{u} n}

private theorem boundary_union_filter {P : Type*} (E : List (Set P)) :
    (⋃ H∈E.filter (fun H => decide H.Nonempty),H) = ⋃ H∈E,H := by
  ext x
  simp only [mem_iUnion,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨H,⟨hH,_hne⟩,hx⟩
    exact ⟨H,hH,hx⟩
  · rintro ⟨H,hH,hx⟩
    exact ⟨H,⟨hH,⟨x,hx⟩⟩,hx⟩

/-- The whole intrinsic good open is the actual base inverse image after only empty positions are removed. -/
theorem pure_good_open_over_base
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (A : Set X) (hA : IsComplexAnalyticSubset (n := n) A)
    (hA' : IsComplexAnalyticSubset (n := n) (Φ ⁻¹' A)) (d : ℕ)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (E' : List (Set X')) (hE' : IsSNCDivisor n E')
    (hfilter : E'.filter (fun H => decide H.Nonempty)=
      (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty)) :
    boundaryGoodOpen (Φ ⁻¹' A) hA' d E' hE' = baseOpen Φ (boundaryGoodOpen A hA d E hE) := by
  have hreg : regularLocus (n := n) (Φ ⁻¹' A) d=Φ ⁻¹' regularLocus (n := n) A d := by
    simpa only [Nat.sub_self,Nat.add_zero] using regularLocus_preimage_eq (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) A d
  have hunion : (⋃ H∈E',H)=Φ ⁻¹' (⋃ H∈E,H) := by
    calc
      _=⋃ H∈E'.filter (fun H => decide H.Nonempty),H := (boundary_union_filter E').symm
      _=⋃ H∈(E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty),H := by rw [hfilter]
      _=⋃ H∈E.map (Φ ⁻¹' ·),H := boundary_union_filter _
      _=_ := (HironakaEmbeddedBoundary.preimage_biUnion_list Φ E).symm
  apply TopologicalSpace.Opens.ext
  change ((Φ ⁻¹' A) \ regularLocus (n := n) (Φ ⁻¹' A) d ∪ ⋃ H∈E',H)ᶜ=
    Φ ⁻¹' (A \ regularLocus (n := n) A d ∪ ⋃ H∈E,H)ᶜ
  rw [hreg,hunion,← preimage_sdiff,← preimage_union,preimage_compl]

/-- Actual pure head choices compare uniquely over the prescribed genuine base, including empty heads. -/
theorem existsUnique_pure_head_choice_over_base
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {A : Set X} {d : ℕ} {E : List (Set X)} {E' : List (Set X')}
    {T : BlowupTower X D} {S : BlowupTower X' D'}
    (hT : PureCanonicalHeadStage E A d T)
    (hS : PureCanonicalHeadStage E' (Φ ⁻¹' A) d S)
    (hfilter : E'.filter (fun H => decide H.Nonempty)=
      (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty)) :
    ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      (geoTransformAlong (partMarkedIdeal E' (Φ ⁻¹' A)) S).E.filter (fun H => decide H.Nonempty)=
        ((geoTransformAlong (partMarkedIdeal E A) T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,IsClosed P → strictTransform n S.proj (Φ ⁻¹' P)=η ⁻¹' strictTransform n T.proj P := by
  let M := partMarkedIdeal E A
  let M' := partMarkedIdeal E' (Φ ⁻¹' A)
  have hN : M'.N=Φ ⁻¹' M.N := by simp [M,M',partMarkedIdeal]
  have hI : M'.ideal=GermIdeal.pullback (m := n) Φ M.ideal := by
    exact (HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) A).symm
  have hstage : ∃! η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      (geoTransformAlong M' S).E.filter (fun H => decide H.Nonempty)=
        ((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
    by_cases hne : A.Nonempty
    · let O := boundaryGoodOpen A hT.analytic d E hT.snc
      have hO := pure_good_open_over_base Φ A hT.analytic hS.analytic d E hT.snc E' hS.snc hfilter
      have haS : CentresAvoid (baseOpen Φ O) S := by rw [← hO];exact hS.avoids
      have hmS : ∃ z∈ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv M' S)
          (geoTransformAlong M' S).cosupp,S.proj z∈baseOpen Φ O := by
        rw [← hO]
        exact hS.meets (hne.preimage Φ.surjective)
      exact first_meeting_choice_over_base_across_empty_boundaries M M' hT.domain Φ hN hI rfl hfilter
        S T hS.canonical hT.canonical O haS hT.avoids hmS (hT.meets hne)
    · have hA : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hcosT : M.cosupp=∅ :=
        (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hT.analytic.isClosed E).trans hA
      have hcosS : M'.cosupp=∅ :=
        (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hS.analytic.isClosed E').trans
          (by rw [hA,preimage_empty])
      have hrT := (canonical_histories_empty_of_original_cosupp_empty M hT.domain hcosT T hT.canonical).2
      have hrS := (canonical_histories_empty_of_original_cosupp_empty M' hS.domain hcosS S hS.canonical).2
      exact terminal_choice_over_base_across_empty_boundaries M M' hT.domain Φ hN hI rfl hfilter
        S T hS.canonical hT.canonical hrS hrT
  obtain ⟨η,hη,hu⟩ := hstage
  refine ⟨η,⟨hη.1,hη.2,?_⟩,?_⟩
  · intro P hP
    exact HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
      Φ η S.contMDiff_proj T.contMDiff_proj P hP hη.1
  · intro η' hh
    exact hu η' ⟨hh.1,hh.2.1⟩

end
end Hironaka.HironakaOriginalPureHeadChoice
