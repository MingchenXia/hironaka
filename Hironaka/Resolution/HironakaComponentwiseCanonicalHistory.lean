/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaComponentwiseCanonicalCentre
import Hironaka.Resolution.HironakaLocallyFiniteResolutionSequence

/-!
# Internally constructed componentwise canonical actual histories

Parallel whole maxima on fixed original clopen components construct actual
global test histories. Compactness of the ORIGINAL component cosupports
then gives local terminal times for this SAME history, locally finite actual
centre images, and actual empty/isomorphic tails. No global maximum or
caller-supplied history is required. The unrestricted connected noncompact
scheduler is not asserted.
Blueprint: `hironaka-componentwise-canonical-history-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaComponentwiseCanonicalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver CanonicalCentres
  HironakaComponentwiseCanonicalCentre HironakaLocallyFiniteResolutionSequence
  TowerPreimageCompact StepOneLowerDomain
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)

variable {n k : ℕ} {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Whole parallel centres are recorded with their actual next maps and tower equalities. -/
def ParallelSteps (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) {J : Type w} (U : J → Opens X) (s : GrowingSeq X) : Prop :=
  ∀ j, ∃ (C : Set (s.stage j).1) (π : (s.stage (j+1)).1 → (s.stage j).1)
    (hπ : IsBlowupAlong n C π),
    (s.stage (j+1)).2=.step (s.stage j).2 C π hπ ∧
      C=parallelCentre R M (s.stage j).2 U

/-- Iterate genuine global refinements while retaining every actual restricted canonical prefix. -/
theorem exists_parallel_canonical_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {J : Type w} (U : J → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) :
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
      exists_parallel_canonical_refinement R M p.1.2 hM p.2.1 U hcover hdisj p.2.2
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

/-- Restriction of the constructed global steps has the exact whole local maximum centre. -/
theorem restricted_steps_are_maxima
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) {J : Type w} (U : J → Opens X)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (s : GrowingSeq X) (hsteps : ParallelSteps R M U s) (i : J) :
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
  rw [hC,preimage_parallelCentre R M (s.stage j).2 U hdisj i]
  rfl

/-- Compact ORIGINAL cosupport forces termination of any actual whole-maximum sequence. -/
theorem eventually_resolves_maximum_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (hK : IsCompact M.cosupp)
    (s : GrowingSeq X) (hcan : ∀ j, IsCanonical M (R.inv M) (s.stage j).2)
    (hsteps : ∀ j, ∃ (C : Set (s.stage j).1)
      (π : (s.stage (j+1)).1 → (s.stage j).1) (hπ : IsBlowupAlong n C π),
      (s.stage (j+1)).2=.step (s.stage j).2 C π hπ ∧
      C=maxLocus (R.inv M (s.stage j).2) (geoTransformAlong M (s.stage j).2).cosupp) :
    ∃ N, ∀ j, N ≤ j → IsGeoResolution M (s.stage j).2 := by
  have hterminal : ∃ N, (geoTransformAlong M (s.stage N).2).cosupp=∅ := by
    by_contra hno
    have hne : ∀ j, (geoTransformAlong M (s.stage j).2).cosupp.Nonempty :=
      fun j => Set.nonempty_iff_ne_empty.mpr (fun he => hno ⟨j,he⟩)
    obtain ⟨bound,hbound⟩ := R.seqLocallyFinite M hM M.cosupp hK s hcan
    have hcount : ∀ j, countCentresMeeting M.cosupp (s.stage j).2=j := by
      intro j
      induction j with
      | zero => rw [s.zero]; rfl
      | succ j ih =>
        obtain ⟨C,π,hπ,he,hC⟩ := hsteps j
        have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage j).2 (hcan j)
        obtain ⟨hc,hs⟩ := HironakaOriginalCompactCosupportGlobalScheduler.current_cosupport_compact
          M hM hK (s.stage j).2 ht
        obtain ⟨x,hx,hm⟩ := (R.isInvValue.usc M hM _ (hcan j)).exists_isMaxOn hc (hne j)
        have hhit : (C ∩ (s.stage j).2.proj ⁻¹' M.cosupp).Nonempty :=
          ⟨x,hC.symm ▸ ⟨hx,hm⟩,hs hx⟩
        rw [he]
        simp only [countCentresMeeting,if_pos hhit,ih]
    have hh := hbound (bound+1)
    rw [hcount] at hh
    omega
  obtain ⟨N,hN⟩ := hterminal
  have htail : ∀ a, (geoTransformAlong M (s.stage (N+a)).2).cosupp=∅ := by
    intro a
    induction a with
    | zero => exact hN
    | succ a ih =>
      rw [← Nat.add_assoc]
      obtain ⟨C,π,hπ,he,_hC⟩ := hsteps (N+a)
      have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage (N+a)).2 (hcan (N+a))
      have hnxt := R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage (N+a+1)).2 (hcan (N+a+1))
      rw [he] at hnxt
      have ha := ((isGeoTestTower_step_iff M (s.stage (N+a)).2 C π hπ).mp hnxt).2
      have hw := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (s.stage (N+a)).2 ht).isWellFormed
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' : z ∈ (geoTransformAlong (geoTransformAlong M (s.stage (N+a)).2)
          (.step .refl C π hπ)).cosupp := by
        change z ∈ (geoTransform (geoTransformAlong M (s.stage (N+a)).2) C π).cosupp
        simpa only [he,geoTransformAlong_step] using hz
      have hh := proj_mem_cosupp_of_mem_cosupp hw.isClosedSubmanifold_N hw.isCoherent
        (.step .refl C π hπ) ⟨trivial,ha⟩ hz'
      rw [ih] at hh
      exact hh
  refine ⟨N,fun j hj => ?_⟩
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hj
  exact ⟨R.isInvValue.isGeoTestTower_of_isCanonical hM _ (hcan _),htail a⟩

private def lastCentreImage : {Y : CMfd.{u} n} → BlowupTower X Y → Set X
  | _,.refl => ∅
  | _,.step T C _ _ => T.proj '' C

/-- The API's actual chosen next centre has precisely the constructed whole-union image. -/
theorem centreImage_parallel_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) {J : Type w} (U : J → Opens X)
    (s : GrowingSeq X) (hsteps : ParallelSteps R M U s) (j : ℕ) :
    centreImage s j=(s.stage j).2.proj '' parallelCentre R M (s.stage j).2 U := by
  obtain ⟨π,hπ,hread⟩ := exists_step_map s j
  have hr := congrArg (lastCentreImage (X := X)) hread
  change lastCentreImage (s.stage (j+1)).2=centreImage s j at hr
  rw [← hr]
  obtain ⟨C,ρ,hρ,he,hC⟩ := hsteps j
  rw [he]
  change (s.stage j).2.proj '' C=_
  rw [hC]

/-- Actual local terminal stages force locally finite closed images and actual empty/isomorphic tails. -/
theorem locally_finite_empty_tails_of_component_terminal
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) {J : Type w} (U : J → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdisj : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (s : GrowingSeq X) (hsteps : ParallelSteps R M U s)
    (hterminal : ∀ i, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (restrict (U i) (s.stage j).2)) :
    LocallyFinite (centreImage s) ∧ (∀ j, IsClosed (centreImage s j)) ∧
    ∀ i, ∃ N,
      (∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U i : Set X))) ∧
      (∀ j, N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
        (hπ : IsBlowupAlong n (stepCentre s j) π),
        (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
        IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (U i : Set X))) ∧
      ∀ a, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 (U i))
          (HironakaLocallyFiniteResolutionSequence.tailTower s N a)) := by
  have havoid : ∀ i, ∃ N, ∀ j, N ≤ j →
      Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U i : Set X)) := by
    intro i
    obtain ⟨N,hN⟩ := hterminal i
    refine ⟨N,fun j hj => disjoint_left.mpr (fun y hyC hyU => ?_)⟩
    have hy : (s.stage j).2.proj y ∈ centreImage s j := ⟨y,hyC,rfl⟩
    rw [centreImage_parallel_sequence R M U s hsteps j] at hy
    obtain ⟨z,hz,hzy⟩ := hy
    have hzU : (s.stage j).2.proj z ∈ U i := hzy.symm ▸ hyU
    let z' : openPreimage (s.stage j).2 (U i) := ⟨z,hzU⟩
    have hm : z' ∈ localMaximum R M (s.stage j).2 (U i) :=
      (Set.ext_iff.mp (preimage_parallelCentre R M (s.stage j).2 U hdisj i) z').mp hz
    have hempty := (hN j hj).2
    have hmem := hm.1
    rw [hempty] at hmem
    exact hmem
  have hfinite : LocallyFinite (centreImage s) := by
    intro x
    obtain ⟨i,hx⟩ := hcover x
    obtain ⟨N,hN⟩ := havoid i
    refine ⟨U i,(U i).isOpen.mem_nhds hx,(finite_Iio N).subset ?_⟩
    rintro j ⟨y,⟨z,hz,rfl⟩,hy⟩
    exact lt_of_not_ge (fun hge => disjoint_left.mp (hN j hge) hz hy)
  refine ⟨hfinite,isClosed_centreImage s,?_⟩
  intro i
  obtain ⟨N,hN⟩ := havoid i
  refine ⟨N,hN,fun j hj => isIsomorphismOver_step_of_disjoint s j (U i) (hN j hj),?_⟩
  intro a
  exact (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s N (U i) hN a)

section Original
variable {n : ℕ} {X : CMfd.{u} n}

/-- ORIGINAL componentwise compact cosupport internally constructs one actual locally terminal global history. -/
theorem exists_original_componentwise_locally_terminal_history
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hK : ∀ i : ConnectedComponents X,
      IsCompact ((Subtype.val : componentOpen i → X) ⁻¹' M.cosupp)) :
    ∃ s : GrowingSeq X,
      (∀ j, IsGeoTestTower M (s.stage j).2) ∧
      (∀ (i : ConnectedComponents X) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M)
          ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M))
          (restrict (componentOpen i) (s.stage j).2)) ∧
      ParallelSteps (canonicalInvariant n) M componentOpen s ∧
      (∀ i : ConnectedComponents X, ∃ N, ∀ j, N ≤ j →
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : componentOpen i → X) M)
          (restrict (componentOpen i) (s.stage j).2)) ∧
      LocallyFinite (centreImage s) ∧ (∀ j, IsClosed (centreImage s j)) ∧
      ∀ i : ConnectedComponents X, ∃ N,
        (∀ j, N ≤ j → Disjoint (stepCentre s j)
          ((s.stage j).2.proj ⁻¹' (componentOpen i : Set X))) ∧
        (∀ j, N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
          (hπ : IsBlowupAlong n (stepCentre s j) π),
          (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
          IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (componentOpen i : Set X))) ∧
        ∀ a, ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 (componentOpen i))
            (HironakaLocallyFiniteResolutionSequence.tailTower s N a)) := by
  let U : ConnectedComponents X → Opens X := componentOpen
  obtain ⟨s,hTest,hCan,hSteps⟩ := exists_parallel_canonical_sequence
    (canonicalInvariant n) M hM U componentOpen_cover componentOpen_pairwise
  have hterminal : ∀ i, ∃ N, ∀ j, N ≤ j →
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U i → X) M)
        (restrict (U i) (s.stage j).2) := by
    intro i
    let Mi := MarkedIdeal.pullback (Subtype.val : U i → X) M
    have hd : IsInvDomain n Mi := InvDomainTowerAlong.isInvDomain_pullback_val (U i) hM
    have hhol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
    have hk : IsCompact Mi.cosupp := by
      rw [cosupp_pullback_val M hhol (U i)]
      exact hK i
    exact eventually_resolves_maximum_sequence (canonicalInvariant n) Mi hd hk
      (s.restrict (U i)) (hCan i)
      (restricted_steps_are_maxima (canonicalInvariant n) M U componentOpen_pairwise s hSteps i)
  exact ⟨s,hTest,hCan,hSteps,hterminal,
    locally_finite_empty_tails_of_component_terminal (canonicalInvariant n) M U
      componentOpen_cover componentOpen_pairwise s hSteps hterminal⟩

end Original
end
end Hironaka.HironakaComponentwiseCanonicalHistory
