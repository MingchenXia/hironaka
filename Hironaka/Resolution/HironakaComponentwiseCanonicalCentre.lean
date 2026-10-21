/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Analytic.GrowingSeqTail
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Actual parallel canonical centres on disjoint open components

The whole local maximum centres of actual restricted canonical prefixes
have a globally closed smooth admissible union on a disjoint open cover.
Its genuine blowup advances every restricted original history without
assuming a whole-space maximum. The original-only first-step consumer
uses the internally constructed ambient connected components and assumes
only compactness of the original cosupport on each component.

This does not assert the unrestricted noncompact scheduler or termination.
Blueprint: `hironaka-componentwise-canonical-centre-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaComponentwiseCanonicalCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

section Parallel
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
  {X Y : CMfd.{u} n} (M : MarkedIdeal n X) (T : BlowupTower X Y)

/-- The whole local canonical maximum uses the actual unchanged restricted original history. -/
def localMaximum (U : Opens X) : Set (openPreimage T U) :=
  maxLocus (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T))
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp

/-- The whole union of actual local maximum centres, without cutting any component centre. -/
def parallelCentre {J : Type w} (U : J → Opens X) : Set Y :=
  ⋃ i, (Subtype.val : openPreimage T (U i) → Y) '' localMaximum R M T (U i)

/-- Disjoint base opens give the exact whole local centre as every original preimage. -/
theorem preimage_parallelCentre {J : Type w} (U : J → Opens X)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) (i : J) :
    (Subtype.val : openPreimage T (U i) → Y) ⁻¹' parallelCentre R M T U=
      localMaximum R M T (U i) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j,y,hy,he⟩ := mem_iUnion.mp hz
    have hij : i=j := by
      by_contra hne
      have hyU : T.proj (y : Y) ∈ U j := y.property
      rw [he] at hyU
      exact disjoint_left.mp (hdisj hne) z.property hyU
    subst j
    have hyz : y=z := Subtype.ext he
    simpa only [hyz] using hy
  · intro hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩

/-- Genuine local canonical maxima descend to a globally closed smooth admissible centre. -/
theorem parallelCentre_admissible (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (hcan : ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T)) :
    (geoTransformAlong M T).IsAdmissibleCentre (parallelCentre R M T U) := by
  have hcoh := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT).isWellFormed.isCoherent
  apply isAdmissibleCentre_of_forall_exists_opens
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)
  intro y
  obtain ⟨i,hi⟩ := hcover (T.proj y)
  refine ⟨openPreimage T (U i),hi,?_⟩
  rw [preimage_parallelCentre R M T U hdisj i]
  have hd := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hd (restrict (U i) T) (hcan i)
  have ha := R.isInvValue.isAdmissibleCentre_maxLocus hd (restrict (U i) T) (hcan i) ht
  simpa only [localMaximum,geoTransformAlong_restrict (U i) hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent T hT] using ha

/-- A true global blowup advances all actual restricted canonical prefixes at once. -/
theorem exists_parallel_canonical_refinement (hM : IsInvDomain k M) (hT : IsGeoTestTower M T)
    {J : Type w} (U : J → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (hcan : ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T)) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n (parallelCentre R M T U) π),
      IsProperMap π ∧ IsGeoTestTower M (.step T (parallelCentre R M T U) π hπ) ∧
      ∀ i, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M))
        (restrict (U i) (.step T (parallelCentre R M T U) π hπ)) := by
  have ha := parallelCentre_admissible R M T hM hT U hcover hdisj hcan
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hint : interior (parallelCentre R M T U)=∅ :=
    eq_empty_of_subset_empty ((interior_mono ha.2.1).trans (interior_cosupp_eq_empty hd).subset)
  obtain ⟨Z,π,hπ⟩ := exists_blowup (parallelCentre R M T U) ha.1 hint
  refine ⟨Z,π,hπ,HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,⟨hT,ha⟩,?_⟩
  intro i
  change IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) T) ∧ _
  exact ⟨hcan i,Or.inr (preimage_parallelCentre R M T U hdisj i)⟩

end Parallel

section Original
variable {n : ℕ} {X : CMfd.{u} n}
local instance : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel n) X

/-- The literal clopen ambient components, without choosing representatives. -/
def componentOpen (i : ConnectedComponents X) : Opens X :=
  ⟨ConnectedComponents.mk ⁻¹' {i},(isOpen_discrete _).preimage ConnectedComponents.continuous_coe⟩

theorem componentOpen_cover (x : X) : ∃ i : ConnectedComponents X, x ∈ componentOpen i :=
  ⟨ConnectedComponents.mk x,rfl⟩

theorem componentOpen_pairwise :
    Pairwise (fun i j : ConnectedComponents X => Disjoint (componentOpen i : Set X) (componentOpen j : Set X)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  exact hij (hi.symm.trans hj)

/-- Original componentwise compact cosupport internally gives an actual noncompact global first canonical refinement. -/
theorem exists_original_componentwise_canonical_first_blowup
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hK : ∀ i : ConnectedComponents X,
      IsCompact ((Subtype.val : componentOpen i → X) ⁻¹' M.cosupp)) :
    ∃ (C : Set X) (Z : CMfd.{u} n) (π : Z → X) (hπ : IsBlowupAlong n C π),
      M.IsAdmissibleCentre C ∧ IsProperMap π ∧ IsGeoTestTower M (.step .refl C π hπ) ∧
      (C.Nonempty ↔ M.cosupp.Nonempty) ∧
      ∀ i : ConnectedComponents X,
        (Subtype.val : componentOpen i → X) ⁻¹' C=
          localMaximum (canonicalInvariant n) M .refl (componentOpen i) ∧
        IsCanonical (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M)
          ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M))
          (restrict (componentOpen i) (.step .refl C π hπ)) := by
  let U : ConnectedComponents X → Opens X := componentOpen
  let C := parallelCentre (canonicalInvariant n) M (.refl : BlowupTower X X) U
  have hcan : ∀ i : ConnectedComponents X,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : U i → X) M))
        (restrict (U i) (.refl : BlowupTower X X)) := fun _ => trivial
  have ha := parallelCentre_admissible (canonicalInvariant n) M .refl hM trivial U
    componentOpen_cover componentOpen_pairwise hcan
  obtain ⟨Z,π,hπ,hproper,hTest,hNext⟩ :=
    exists_parallel_canonical_refinement (canonicalInvariant n) M .refl hM trivial U
      componentOpen_cover componentOpen_pairwise hcan
  refine ⟨C,Z,π,hπ,ha,hproper,hTest,?_,?_⟩
  · constructor
    · exact fun hC => hC.mono ha.2.1
    · rintro ⟨x,hx⟩
      let i : ConnectedComponents X := ConnectedComponents.mk x
      let z : U i := ⟨x,rfl⟩
      let Mi := MarkedIdeal.pullback (Subtype.val : U i → X) M
      have hd : IsInvDomain n Mi := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
      have hhol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
        fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
      have hk : IsCompact Mi.cosupp := by
        rw [cosupp_pullback_val M hhol (U i)]
        exact hK i
      have hne : Mi.cosupp.Nonempty := by
        refine ⟨z,?_⟩
        rw [cosupp_pullback_val M hhol (U i)]
        exact hx
      have husc := (canonicalInvariant n).isInvValue.usc Mi hd (.refl : BlowupTower (CMfd.of (n := n) (U i)) (CMfd.of (n := n) (U i))) trivial
      rw [geoTransformAlong_refl] at husc
      obtain ⟨y,hy,hmax⟩ := husc.exists_isMaxOn hk hne
      refine ⟨y.val,mem_iUnion.mpr ⟨i,y,?_,rfl⟩⟩
      exact ⟨hy,hmax⟩
  · intro i
    exact ⟨preimage_parallelCentre (canonicalInvariant n) M .refl U componentOpen_pairwise i,hNext i⟩

end Original
end
end Hironaka.HironakaComponentwiseCanonicalCentre
