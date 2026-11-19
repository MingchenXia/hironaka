import Hironaka.Resolution.HironakaG3FirstMeetingEmptyAware
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Resolution.HironakaG3RStoppedOverlap
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BiholomorphicFirstMeeting
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism CanonicalCentres RestrictEmptyTower
  HironakaOriginalBoundaryEmptyBaseComparison HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareComposition HironakaG3InteriorEmptyAligned
  HironakaDisjointFiniteControlledHistory ResolutionInvariantExt
  HironakaG3RStoppedOverlap HironakaOriginalIndependentStoppedSource
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

/-- Histories consisting entirely of actual empty blowups align over any
prescribed biholomorphic base map. -/
theorem emptyAware_of_empty_towers
    {n : ℕ} {X X' Y Y' : CMfd.{0} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hS : IsEmptyTower S) (hT : IsEmptyTower T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso Φ S T ψ := by
  induction S with
  | refl =>
    induction T with
    | refl => exact ⟨Φ, .refl⟩
    | @step A B T C π hπ ih =>
      obtain ⟨ψ,hψ⟩ := ih hT.1
      have hC := hT.2
      subst C
      obtain ⟨φ,_hφ,h⟩ := exists_emptyAware_right hψ hπ
      exact ⟨ψ.trans φ.symm,h⟩
  | @step A B S C π hπ ih =>
    obtain ⟨ψ,hψ⟩ := ih hS.1
    have hC := hS.2
    subst C
    obtain ⟨φ,_hφ,h⟩ := exists_emptyAware_left hψ hπ
    exact ⟨φ.trans ψ,h⟩

/-- First-meeting canonical histories over a genuine base biholomorphism
admit a structural comparison allowing the actual empty stages. -/
theorem first_meeting_emptyAware_over_base
    {n : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hcS : IsCanonical (MarkedIdeal.pullback Φ M)
      ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M)) S)
    (hcT : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (haS : CentresAvoid (baseOpen Φ O) S) (haT : CentresAvoid O T)
    (hmS : ∃ c ∈ maxLocus ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M) S)
      (geoTransformAlong (MarkedIdeal.pullback Φ M) S).cosupp, S.proj c ∈ baseOpen Φ O)
    (hmT : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso Φ S T ψ := by
  let P := transport Φ T
  let J := MarkedIdeal.pullback Φ M
  obtain ⟨hJ,hcP,hi,hproj,_hrec,hmax,_hres,ha⟩ := canonical_transport_dictionary M hM Φ T hcT
  have hmP : ∃ c ∈ maxLocus ((canonicalInvariant n).inv J P.tower)
      (geoTransformAlong J P.tower).cosupp, P.tower.proj c ∈ baseOpen Φ O := by
    obtain ⟨c,hc,hcO⟩ := hmT
    refine ⟨P.back.symm c,?_,?_⟩
    · rw [hmax]
      change P.back (P.back.symm c) ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp
      rwa [P.back.apply_symm_apply]
    · change Φ (P.tower.proj (P.back.symm c)) ∈ O
      rw [← hproj,P.back.apply_symm_apply]
      exact hcO
  have hI := HironakaSmoothSubmersionOriginalAmbientCanonical.canonicalInvariant_eq_invFamily hn
  rw [hI] at hcS hcP hmS hmP
  obtain ⟨κ,hκ⟩ := original_first_meeting_emptyAware hn n J hJ S P.tower hcS hcP
    (baseOpen Φ O) haS (ha O haT) hmS hmP
  have h := HironakaG3EmptyAwareComposition.trans hκ (emptyAware_of_isTowerIso hi)
  refine ⟨κ.trans P.back, ?_⟩
  simpa only [Diffeomorph.refl_trans] using h

/-- The structural first-meeting comparison lifts to actual coupled ambient
histories when the two initial embeddings agree over the base map. -/
theorem first_meeting_ambient_over_base
    {n t : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hcS : IsCanonical (MarkedIdeal.pullback Φ M)
      ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M)) S)
    (hcT : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (haS : CentresAvoid (baseOpen Φ O) S) (haT : CentresAvoid O T)
    (hmS : ∃ c ∈ maxLocus ((canonicalInvariant n).inv (MarkedIdeal.pullback Φ M) S)
      (geoTransformAlong (MarkedIdeal.pullback Φ M) S).cosupp, S.proj c ∈ baseOpen Φ O)
    (hmT : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O)
    {P : CMfd.{0} (n+t)} {N : Set P} {B : List (Set P)} {J : GermIdeal (n+t) P}
    {ιS : X' → P} {ιT : X → P} (hι : ∀ x, ιT (Φ x) = ιS x)
    {Z₁ Z₂ : CMfd.{0} (n+t)} {U₁ : BlowupTower P Z₁} {U₂ : BlowupTower P Z₂}
    {η₁ : Y' → Z₁} {η₂ : Y → Z₂}
    (hU₁ : CoupledHistory N B J ιS (MarkedIdeal.pullback Φ M) S U₁ η₁)
    (hU₂ : CoupledHistory N B J ιT M T U₂ η₂) :
    ∃ (ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (β : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ Z₂),
      (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := first_meeting_emptyAware_over_base hn M hM Φ S T hcS hcT O haS haT hmS hmT
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories Φ hψ hι hU₁ hU₂
  exact ⟨ψ,β,hβ,hη⟩

private theorem stopped_max_of_cosupp_meets
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (O : Opens X) (T : BlowupTower X Y) (hT : IsStopped M O T)
    (hMeet : (M.cosupp ∩ O).Nonempty) :
    ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp, T.proj c ∈ O := by
  rcases hT.2.2 with hm | hr
  · exact hm
  · obtain ⟨x,hxM,hxO⟩ := hMeet
    have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hT.1
    obtain ⟨y,hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
    have hyO : T.proj y ∈ O := by rw [hy]; exact hxO
    have hyc := (mem_cosupp_iff_of_centresAvoid M hM.isWellFormed T ht O hT.2.1 y hyO).mpr (by rw [hy]; exact hxM)
    rw [hr.2] at hyc
    exact hyc.elim

/-- Stopped histories admit an actual empty-aware comparison over the base
whenever the original cosupport meets the open or is empty. -/
theorem stopped_emptyAware_over_base
    {n : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (O : Opens X) (hcases : (M.cosupp ∩ O).Nonempty ∨ M.cosupp = ∅)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hS : IsStopped (MarkedIdeal.pullback Φ M) (baseOpen Φ O) S) (hT : IsStopped M O T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso Φ S T ψ := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hmem : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  have hcos : (MarkedIdeal.pullback Φ M).cosupp = Φ ⁻¹' M.cosupp :=
    MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
      Φ.symm_apply_apply M hmem
  rcases hcases with hMeet | hEmpty
  · have hMeet' : ((MarkedIdeal.pullback Φ M).cosupp ∩ baseOpen Φ O).Nonempty := by
      obtain ⟨x,hx,hxO⟩ := hMeet
      refine ⟨Φ.symm x,?_,?_⟩
      · rw [hcos]
        simpa using hx
      · change Φ (Φ.symm x) ∈ O
        rwa [Φ.apply_symm_apply]
    exact first_meeting_emptyAware_over_base hn M hM Φ S T hS.1 hT.1 O hS.2.1 hT.2.1
      (stopped_max_of_cosupp_meets _ hM' _ _ hS hMeet')
      (stopped_max_of_cosupp_meets _ hM _ _ hT hMeet)
  · have he' : (MarkedIdeal.pullback Φ M).cosupp = ∅ := by rw [hcos,hEmpty,preimage_empty]
    exact emptyAware_of_empty_towers Φ S T
      (canonical_histories_empty_of_original_cosupp_empty _ hM' he' S hS.1).1
      (canonical_histories_empty_of_original_cosupp_empty M hM hEmpty T hT.1).1

/-- Actual coupled ambient lifts of stopped histories compare compatibly,
including when the initial cosupport is empty. -/
theorem stopped_ambient_over_base
    {n t : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (O : Opens X) (hcases : (M.cosupp ∩ O).Nonempty ∨ M.cosupp = ∅)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hS : IsStopped (MarkedIdeal.pullback Φ M) (baseOpen Φ O) S) (hT : IsStopped M O T)
    {P : CMfd.{0} (n+t)} {N : Set P} {B : List (Set P)} {J : GermIdeal (n+t) P}
    {ιS : X' → P} {ιT : X → P} (hι : ∀ x, ιT (Φ x) = ιS x)
    {Z₁ Z₂ : CMfd.{0} (n+t)} {U₁ : BlowupTower P Z₁} {U₂ : BlowupTower P Z₂}
    {η₁ : Y' → Z₁} {η₂ : Y → Z₂}
    (hU₁ : CoupledHistory N B J ιS (MarkedIdeal.pullback Φ M) S U₁ η₁)
    (hU₂ : CoupledHistory N B J ιT M T U₂ η₂) :
    ∃ (ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (β : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ Z₂),
      (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := stopped_emptyAware_over_base hn M hM Φ O hcases S T hS hT
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories Φ hψ hι hU₁ hU₂
  exact ⟨ψ,β,hβ,hη⟩

end
end Hironaka.HironakaG3BiholomorphicFirstMeeting
