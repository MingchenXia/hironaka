/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaComponentwiseCanonicalHistory

/-!
# Actual global centres from covers disjoint on the ORIGINAL cosupport

Original opens may overlap away from the original cosupport. Actual
current cosupports map into that SAME original cosupport, which forces
exact whole local-centre traces and genuine global admissibility. No
analytic centre is truncated and no compatibility certificate is assumed.
Blueprint: `hironaka-support-disjoint-canonical-centre-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaSupportDisjointCanonicalCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver HironakaComponentwiseCanonicalCentre
  StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n k : ℕ} {X Y : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Every whole local maximum lies over the SAME original cosupport. -/
theorem parallelCentre_subset_original_cosupp
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X) :
    parallelCentre R M T U ⊆ T.proj ⁻¹' M.cosupp := by
  have hc := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT).isWellFormed.isCoherent
  rintro z hz
  obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hz
  have hyc := hy.1
  rw [geoTransformAlong_restrict (U i) hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T hT,
    cosupp_pullback_val _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg)] at hyc
  exact proj_mem_cosupp_of_mem_cosupp hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T hT hyc

/-- Support disjointness, not ambient disjointness, gives exact whole centre traces. -/
theorem preimage_parallelCentre_support_disjoint
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp))) (i : J) :
    (Subtype.val : openPreimage T (U i) → Y) ⁻¹' parallelCentre R M T U=
      localMaximum R M T (U i) := by
  ext z
  constructor
  · intro hz
    have hS := parallelCentre_subset_original_cosupp R M T hM hT U hz
    obtain ⟨j,y,hy,he⟩ := mem_iUnion.mp hz
    have hij : i=j := by
      by_contra hne
      have hyU : T.proj (y : Y) ∈ U j := y.property
      rw [he] at hyU
      exact disjoint_left.mp (hdisj hne) ⟨z.property,hS⟩ ⟨hyU,hS⟩
    subst j
    have hyz : y=z := Subtype.ext he
    simpa only [hyz] using hy
  · intro hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩

/-- A genuine support-disjoint original cover gives a globally closed smooth admissible whole union. -/
theorem parallelCentre_admissible_support_disjoint
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X)
    (hcover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp)))
    (hcan : ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T)) :
    (geoTransformAlong M T).IsAdmissibleCentre (parallelCentre R M T U) := by
  have hc := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT).isWellFormed.isCoherent
  have hS := GiraudAlong.isClosed_cosupport_along hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N M.d
  have hsub := parallelCentre_subset_original_cosupp R M T hM hT U
  apply isAdmissibleCentre_of_forall_exists_opens
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg)
  intro y
  by_cases hy : T.proj y ∈ M.cosupp
  · obtain ⟨i,hi⟩ := hcover _ hy
    refine ⟨openPreimage T (U i),hi,?_⟩
    rw [preimage_parallelCentre_support_disjoint R M T hM hT U hdisj i]
    have hd := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical hd (restrict (U i) T) (hcan i)
    have ha := R.isInvValue.isAdmissibleCentre_maxLocus hd (restrict (U i) T) (hcan i) ht
    simpa only [localMaximum,geoTransformAlong_restrict (U i) hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent T hT] using ha
  · let W : Opens X := ⟨M.cosuppᶜ,hS.isOpen_compl⟩
    refine ⟨openPreimage T W,hy,?_⟩
    have he : (Subtype.val : openPreimage T W → Y) ⁻¹' parallelCentre R M T U=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact z.property (hsub hz)
    rw [he]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- Genuine global blowup geometry advances every actual support-local canonical prefix. -/
theorem exists_support_disjoint_canonical_refinement
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X)
    (hcover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp)))
    (hcan : ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T)) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n (parallelCentre R M T U) π),
      IsProperMap π ∧ IsGeoTestTower M (.step T (parallelCentre R M T U) π hπ) ∧
      ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M))
        (restrict (U i) (.step T (parallelCentre R M T U) π hπ)) := by
  have ha := parallelCentre_admissible_support_disjoint R M T hM hT U hcover hdisj hcan
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hint : interior (parallelCentre R M T U)=∅ :=
    eq_empty_of_subset_empty ((interior_mono ha.2.1).trans (interior_cosupp_eq_empty hd).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup (parallelCentre R M T U) ha.1 hint
  refine ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,⟨hT,ha⟩,?_⟩
  intro i
  change IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
    (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T) ∧ _
  exact ⟨hcan i,Or.inr (preimage_parallelCentre_support_disjoint R M T hM hT U hdisj i)⟩

end
end Hironaka.HironakaSupportDisjointCanonicalCentre
