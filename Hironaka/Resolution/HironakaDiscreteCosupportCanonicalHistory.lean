/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSupportDisjointCanonicalCentre
import Mathlib.Topology.DiscreteSubset

/-!
# Actual noncompact elementary histories from discrete ORIGINAL cosupport

The original discrete cosupport internally supplies isolating opens, whose
literal original restricted cosupports are compact singletons. These opens
may overlap away from the ORIGINAL support. Exact support-disjoint centre
traces construct one actual global GrowingSeq, locally terminal on the same
opens, with closed locally finite actual centre images and real empty tails.
The ambient manifold may be connected and noncompact. Arbitrary coherent
positive-dimensional original cosupports are not asserted discrete.
Blueprint: `hironaka-discrete-cosupport-canonical-history-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaDiscreteCosupportCanonicalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver CanonicalCentres
  HironakaComponentwiseCanonicalCentre HironakaComponentwiseCanonicalHistory
  HironakaSupportDisjointCanonicalCentre HironakaLocallyFiniteResolutionSequence
  TowerPreimageCompact
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n k : ℕ} {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- A genuine original ambient isolating open, chosen only from the original discrete cosupport. -/
def isolatingOpen (M : MarkedIdeal n X) [DiscreteTopology M.cosupp] (a : M.cosupp) : Opens X :=
  ⟨(discreteTopology_subtype_iff'.mp inferInstance a.1 a.2).choose,
    (discreteTopology_subtype_iff'.mp inferInstance a.1 a.2).choose_spec.1⟩

theorem isolatingOpen_inter_cosupp (M : MarkedIdeal n X) [DiscreteTopology M.cosupp] (a : M.cosupp) :
    (isolatingOpen M a : Set X) ∩ M.cosupp={a.val} :=
  (discreteTopology_subtype_iff'.mp inferInstance a.1 a.2).choose_spec.2

theorem mem_isolatingOpen (M : MarkedIdeal n X) [DiscreteTopology M.cosupp] (a : M.cosupp) :
    a.val ∈ isolatingOpen M a := by
  have hh : a.val ∈ (isolatingOpen M a : Set X) ∩ M.cosupp := by
    rw [isolatingOpen_inter_cosupp]
    exact mem_singleton _
  exact hh.1

theorem isolatingOpen_cover (M : MarkedIdeal n X) [DiscreteTopology M.cosupp] :
    ∀ x ∈ M.cosupp, ∃ a : M.cosupp, x ∈ isolatingOpen M a :=
  fun x hx => ⟨⟨x,hx⟩,mem_isolatingOpen M ⟨x,hx⟩⟩

theorem isolatingOpen_support_disjoint (M : MarkedIdeal n X) [DiscreteTopology M.cosupp] :
    Pairwise (fun a b : M.cosupp =>
      Disjoint ((isolatingOpen M a : Set X) ∩ M.cosupp)
        ((isolatingOpen M b : Set X) ∩ M.cosupp)) := by
  intro a b hab
  rw [isolatingOpen_inter_cosupp,isolatingOpen_inter_cosupp]
  exact disjoint_left.mpr (fun _ ha hb => hab (Subtype.ext (ha.symm.trans hb)))

/-- The entire actual original restricted cosupport is a compact literal singleton. -/
theorem isCompact_isolating_cosupp (M : MarkedIdeal n X) (hc : M.ideal.IsCoherent)
    [DiscreteTopology M.cosupp] (a : M.cosupp) :
    IsCompact (MarkedIdeal.pullback (Subtype.val : isolatingOpen M a → X) M).cosupp := by
  have he : (Subtype.val : isolatingOpen M a → X) ⁻¹' M.cosupp=
      {⟨a.val,mem_isolatingOpen M a⟩} := by
    ext z
    constructor
    · intro hz
      change z=⟨a.val,mem_isolatingOpen M a⟩
      apply Subtype.ext
      have hz' : (z : X) ∈ (isolatingOpen M a : Set X) ∩ M.cosupp := ⟨z.property,hz⟩
      rw [isolatingOpen_inter_cosupp] at hz'
      exact hz'
    · rintro rfl
      exact a.property
  rw [cosupp_pullback_val M
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg),he]
  exact isCompact_singleton

/-- Actual support-disjoint refinements are internally iterated before any terminal time is known. -/
theorem exists_support_disjoint_canonical_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {J : Type w} (U : J → Opens X) (hcover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp))) :
    ∃ s : GrowingSeq X,
      (∀ j, IsGeoTestTower M (s.stage j).2) ∧
      (∀ i j, IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M))
        (restrict (U i) (s.stage j).2)) ∧ ParallelSteps R M U s := by
  let A := {p : Σ Y : CMfd.{u} n, BlowupTower X Y //
    IsGeoTestTower M p.2 ∧ ∀ i,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)) (restrict (U i) p.2)}
  have hext : ∀ p : A, ∃ q : A, ∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π), q.1.2=.step p.1.2 C π hπ ∧
        C=parallelCentre R M p.1.2 U := by
    intro p
    obtain ⟨Z,π,hπ,_hproper,hTest,hCan⟩ :=
      exists_support_disjoint_canonical_refinement R M p.1.2 hM p.2.1 U hcover hdisj p.2.2
    exact ⟨⟨⟨Z,.step p.1.2 (parallelCentre R M p.1.2 U) π hπ⟩,hTest,hCan⟩,
      _,π,hπ,rfl,rfl⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X,.refl⟩,trivial,fun _ => trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_hC⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  refine ⟨s,(fun j => (next^[j] a0).2.1),(fun i j => (next^[j] a0).2.2 i),?_⟩
  intro j
  change ∃ (C : Set (next^[j] a0).1.1)
    (π : (next^[j+1] a0).1.1 → (next^[j] a0).1.1) (hπ : IsBlowupAlong n C π),
    (next^[j+1] a0).1.2=.step (next^[j] a0).1.2 C π hπ ∧ _
  rw [Function.iterate_succ_apply']
  exact hnext (next^[j] a0)

/-- The SAME actual restricted sequences retain their entire genuine maximum steps. -/
theorem restricted_steps_are_support_maxima
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {J : Type w} (U : J → Opens X)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp)))
    (s : GrowingSeq X) (hTest : ∀ j, IsGeoTestTower M (s.stage j).2)
    (hsteps : ParallelSteps R M U s) (i : J) :
    ∀ j, ∃ (C : Set ((s.restrict (U i)).stage j).1)
      (π : ((s.restrict (U i)).stage (j+1)).1 → ((s.restrict (U i)).stage j).1)
      (hπ : IsBlowupAlong n C π),
      ((s.restrict (U i)).stage (j+1)).2=
        .step ((s.restrict (U i)).stage j).2 C π hπ ∧
      C=maxLocus (R.inv (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        ((s.restrict (U i)).stage j).2)
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U i → X) M)
          ((s.restrict (U i)).stage j).2).cosupp := by
  intro j
  obtain ⟨C,π,hπ,he,hC⟩ := hsteps j
  change ∃ (D : Set (openPreimage (s.stage j).2 (U i)))
    (ρ : openPreimage (s.stage (j+1)).2 (U i) → openPreimage (s.stage j).2 (U i))
    (hρ : IsBlowupAlong n D ρ),
    restrict (U i) (s.stage (j+1)).2=.step (restrict (U i) (s.stage j).2) D ρ hρ ∧ _
  rw [he]
  obtain ⟨ρ,hρ,hr⟩ := exists_restrict_step (U i) (s.stage j).2 C π hπ
  refine ⟨_,ρ,hρ,hr,?_⟩
  rw [hC,preimage_parallelCentre_support_disjoint R M (s.stage j).2 hM (hTest j) U hdisj i]
  rfl

/-- Local terminality on the ORIGINAL support cover gives actual local empty/isomorphic tails everywhere. -/
theorem locally_finite_empty_tails_support_disjoint
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {J : Type w} (U : J → Opens X) (hcover : ∀ x ∈ M.cosupp, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j =>
      Disjoint ((U i : Set X) ∩ M.cosupp) ((U j : Set X) ∩ M.cosupp)))
    (s : GrowingSeq X) (hTest : ∀ j, IsGeoTestTower M (s.stage j).2)
    (hsteps : ParallelSteps R M U s)
    (hterminal : ∀ i, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (restrict (U i) (s.stage j).2)) :
    LocallyFinite (centreImage s) ∧ (∀ j, IsClosed (centreImage s j)) ∧
    ∀ x : X, ∃ (N : ℕ) (W : Opens X), x ∈ W ∧
      (∀ j, N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
        (hπ : IsBlowupAlong n (stepCentre s j) π),
        (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
        IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (W : Set X))) ∧
      ∀ a, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 W)
          (HironakaLocallyFiniteResolutionSequence.tailTower s N a)) := by
  have hS := GiraudAlong.isClosed_cosupport_along hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N M.d
  have himage : ∀ j, centreImage s j ⊆ M.cosupp := by
    intro j
    rw [centreImage_parallel_sequence R M U s hsteps j]
    rintro x ⟨y,hy,rfl⟩
    exact parallelCentre_subset_original_cosupp R M (s.stage j).2 hM (hTest j) U hy
  have havoid : ∀ x : X, ∃ (N : ℕ) (W : Opens X), x ∈ W ∧
      ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (W : Set X)) := by
    intro x
    by_cases hx : x ∈ M.cosupp
    · obtain ⟨i,hi⟩ := hcover x hx
      obtain ⟨N,hN⟩ := hterminal i
      refine ⟨N,U i,hi,fun j hj => disjoint_left.mpr (fun y hyC hyU => ?_)⟩
      have hy : (s.stage j).2.proj y ∈ centreImage s j := ⟨y,hyC,rfl⟩
      rw [centreImage_parallel_sequence R M U s hsteps j] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      have hzU : (s.stage j).2.proj z ∈ U i := hzy.symm ▸ hyU
      let z' : openPreimage (s.stage j).2 (U i) := ⟨z,hzU⟩
      have hm : z' ∈ localMaximum R M (s.stage j).2 (U i) :=
        (Set.ext_iff.mp (preimage_parallelCentre_support_disjoint R M (s.stage j).2
          hM (hTest j) U hdisj i) z').mp hz
      have hmem := hm.1
      rw [(hN j hj).2] at hmem
      exact hmem
    · let W : Opens X := ⟨M.cosuppᶜ,hS.isOpen_compl⟩
      refine ⟨0,W,hx,fun j _ => disjoint_left.mpr (fun y hyC hyW => ?_)⟩
      exact hyW (himage j ⟨y,hyC,rfl⟩)
  have hfinite : LocallyFinite (centreImage s) := by
    intro x
    obtain ⟨N,W,hx,hN⟩ := havoid x
    refine ⟨W,W.isOpen.mem_nhds hx,(finite_Iio N).subset ?_⟩
    rintro j ⟨y,⟨z,hz,rfl⟩,hy⟩
    exact lt_of_not_ge (fun hge => disjoint_left.mp (hN j hge) hz hy)
  refine ⟨hfinite,isClosed_centreImage s,?_⟩
  intro x
  obtain ⟨N,W,hx,hN⟩ := havoid x
  refine ⟨N,W,hx,fun j hj => isIsomorphismOver_step_of_disjoint s j W (hN j hj),?_⟩
  intro a
  exact (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s N W hN a)

section Original
variable {n : ℕ} {X : CMfd.{u} n}

/-- Only ORIGINAL domain plus discrete ORIGINAL cosupport supplies the entire actual global history. -/
theorem exists_original_discrete_cosupport_locally_terminal_history
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) [DiscreteTopology M.cosupp] :
    ∃ s : GrowingSeq X,
      (∀ j, IsGeoTestTower M (s.stage j).2) ∧
      (∀ (a : M.cosupp) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : isolatingOpen M a → X) M)
          ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : isolatingOpen M a → X) M))
          (restrict (isolatingOpen M a) (s.stage j).2)) ∧
      ParallelSteps (canonicalInvariant n) M (isolatingOpen M) s ∧
      (∀ a : M.cosupp, ∃ N, ∀ j, N ≤ j →
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : isolatingOpen M a → X) M)
          (restrict (isolatingOpen M a) (s.stage j).2)) ∧
      LocallyFinite (centreImage s) ∧ (∀ j, IsClosed (centreImage s j)) ∧
      ∀ x : X, ∃ (N : ℕ) (W : Opens X), x ∈ W ∧
        (∀ j, N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
          (hπ : IsBlowupAlong n (stepCentre s j) π),
          (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
          IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (W : Set X))) ∧
        ∀ a, ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 W)
            (HironakaLocallyFiniteResolutionSequence.tailTower s N a)) := by
  let U : M.cosupp → Opens X := isolatingOpen M
  obtain ⟨s,hTest,hCan,hSteps⟩ := exists_support_disjoint_canonical_sequence
    (canonicalInvariant n) M hM U (isolatingOpen_cover M) (isolatingOpen_support_disjoint M)
  have hterminal : ∀ a, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U a → X) M)
        (restrict (U a) (s.stage j).2) := by
    intro a
    let Ma := MarkedIdeal.pullback (Subtype.val : U a → X) M
    have hd : IsInvDomain n Ma := InvDomainTowerAlong.isInvDomain_pullback_val (U a) hM
    have hk : IsCompact Ma.cosupp := isCompact_isolating_cosupp M hM.isWellFormed.isCoherent a
    exact eventually_resolves_maximum_sequence (canonicalInvariant n) Ma hd hk
      (s.restrict (U a)) (hCan a)
      (restricted_steps_are_support_maxima (canonicalInvariant n) M hM U
        (isolatingOpen_support_disjoint M) s hTest hSteps a)
  exact ⟨s,hTest,hCan,hSteps,hterminal,
    locally_finite_empty_tails_support_disjoint (canonicalInvariant n) M hM U
      (isolatingOpen_cover M) (isolatingOpen_support_disjoint M) s hTest hSteps hterminal⟩

end Original
end
end Hironaka.HironakaDiscreteCosupportCanonicalHistory
