/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalDiscreteFullCutCentres
import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryComparison

/-!
# An actual relative cleanup of a discrete initial strict full-value cut

The whole original cosupport need not be compact or discrete. Actual local
canonical histories erase the HIGH cut with all empty positions retained.
Blueprint: `hironaka-original-discrete-full-cut-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalDiscreteFullCutHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantDriver CanonicalCentres InvDomainTowerAlong
  HironakaOriginalDiscreteFullCutCentres HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryComparison TowerPreimageCompact
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n k : ℕ} {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- Genuine actual next maps retain the whole selected original-cut centre. -/
def CutParallelSteps (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (threshold : Λ) [DiscreteTopology (strictCut R M .refl threshold)]
    (s : GrowingSeq X) : Prop :=
  ∀ j,∃ (C : Set (s.stage j).1) (π : (s.stage (j+1)).1 → (s.stage j).1)
    (hπ : IsBlowupAlong n C π),
    (s.stage (j+1)).2=.step (s.stage j).2 C π hπ ∧ C=parallelCutCentre R M (s.stage j).2 threshold

/-- All state/history data are constructed before any local terminal time. -/
theorem exists_discrete_cut_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] :
    ∃ s : GrowingSeq X,
      (∀ j,IsGeoTestTower M (s.stage j).2) ∧
      (∀ (a : strictCut R M .refl threshold) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
          (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
          (restrict (cutWindow R M threshold a) (s.stage j).2)) ∧ CutParallelSteps R M threshold s := by
  let A := {p : Σ Y : CMfd.{u} n,BlowupTower X Y //
    IsGeoTestTower M p.2 ∧ ∀ a : strictCut R M .refl threshold,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) p.2)}
  have hext : ∀ p : A,∃ q : A,∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π),q.1.2=.step p.1.2 C π hπ ∧ C=parallelCutCentre R M p.1.2 threshold := by
    intro p
    obtain ⟨Z,π,hπ,_hProper,hTest,hCan⟩ :=
      exists_discrete_cut_refinement R M hM p.1.2 p.2.1 threshold p.2.2
    exact ⟨⟨⟨Z,.step p.1.2 (parallelCutCentre R M p.1.2 threshold) π hπ⟩,hTest,hCan⟩,
      _,π,hπ,rfl,rfl⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X,.refl⟩,trivial,fun _ => trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  refine ⟨s,(fun j => (next^[j] a0).2.1),(fun a j => (next^[j] a0).2.2 a),?_⟩
  intro j
  change ∃ (C : Set (next^[j] a0).1.1)
    (π : (next^[j+1] a0).1.1 → (next^[j] a0).1.1) (hπ : IsBlowupAlong n C π),
    (next^[j+1] a0).1.2=.step (next^[j] a0).1.2 C π hπ ∧ _
  rw [Function.iterate_succ_apply']
  exact hnext (next^[j] a0)

private theorem restricted_cut_step
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] (s : GrowingSeq X)
    (hcan : ∀ (a : strictCut R M .refl threshold) j,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) (s.stage j).2))
    (hSteps : CutParallelSteps R M threshold s) (a : strictCut R M .refl threshold) (j : ℕ) :
    let U := cutWindow R M threshold a
    let N := MarkedIdeal.pullback (Subtype.val : U → X) M
    ∃ (C : Set ((s.restrict U).stage j).1)
      (π : ((s.restrict U).stage (j+1)).1 → ((s.restrict U).stage j).1)
      (hπ : IsBlowupAlong n C π),
      ((s.restrict U).stage (j+1)).2=.step ((s.restrict U).stage j).2 C π hπ ∧
        C=selectedMaximum R N ((s.restrict U).stage j).2 threshold := by
  dsimp only
  obtain ⟨C,π,hπ,he,hC⟩ := hSteps j
  let U := cutWindow R M threshold a
  change ∃ (D : Set (openPreimage (s.stage j).2 U))
    (ρ : openPreimage (s.stage (j+1)).2 U → openPreimage (s.stage j).2 U)
    (hρ : IsBlowupAlong n D ρ),restrict U (s.stage (j+1)).2=.step (restrict U (s.stage j).2) D ρ hρ ∧ _
  rw [he]
  obtain ⟨ρ,hρ,hr⟩ := exists_restrict_step U (s.stage j).2 C π hπ
  refine ⟨_,ρ,hρ,hr,?_⟩
  rw [hC,preimage_parallelCutCentre R M hM (s.stage j).2 threshold (fun b => hcan b j) a]
  rfl

/-- Compactness of the actual HIGH cut, not of the whole cosupport, drives erasure. -/
private theorem eventually_erases_cut
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] (s : GrowingSeq X)
    (hcan : ∀ (a : strictCut R M .refl threshold) j,
      IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
        (restrict (cutWindow R M threshold a) (s.stage j).2))
    (hSteps : CutParallelSteps R M threshold s) (a : strictCut R M .refl threshold) :
    ∃ N,∀ j,N ≤ j → strictCut R
      (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
      (restrict (cutWindow R M threshold a) (s.stage j).2) threshold=∅ := by
  let U := cutWindow R M threshold a
  let M0 := MarkedIdeal.pullback (Subtype.val : U → X) M
  let t := s.restrict U
  let K : Set U := {⟨a.val,mem_cutWindow R M threshold a⟩}
  have hd : IsInvDomain k M0 := isInvDomain_pullback_val U hM
  have hct : ∀ j,IsCanonical M0 (R.inv M0) (t.stage j).2 := hcan a
  obtain ⟨m,hm⟩ := R.seqLocallyFinite M0 hd K isCompact_singleton t hct
  have hback (j : ℕ) : (strictCut R M0 (t.stage (j+1)).2 threshold).Nonempty →
      (strictCut R M0 (t.stage j).2 threshold).Nonempty := by
    rintro ⟨z,hz⟩
    obtain ⟨C,π,hπ,he,_⟩ := restricted_cut_step R M hM threshold s hcan hSteps a j
    have hcnext := hct (j+1)
    rw [he] at hcnext hz
    dsimp only [strictCut] at hz
    have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hd (.step (t.stage j).2 C π hπ) hcnext
    have hOldD := isInvDomain_geoTransformAlong hd (t.stage j).2 hTest.1
    have hzOld : π z∈(geoTransformAlong M0 (t.stage j).2).cosupp :=
      TransformOffCentre.cosupp_geoTransform_subset_preimage _ hOldD.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hOldD.isWellFormed.isCoherent hg) hπ hTest.2.2.1 hz.1
    have hval : R.inv M0 (.step (t.stage j).2 C π hπ) z≤R.inv M0 (t.stage j).2 (π z) :=
      canonical_step_value_le (X := CMfd.of (n := n) U)
        (Y := (t.stage j).1) (Z := (t.stage (j+1)).1) R M0 hd (t.stage j).2 C π hπ hcnext z hz.1
    exact ⟨π z,hzOld,lt_of_lt_of_le hz.2 hval⟩
  have hinc (j : ℕ) (hne : (strictCut R M0 (t.stage j).2 threshold).Nonempty) :
      countCentresMeeting K (t.stage (j+1)).2=countCentresMeeting K (t.stage j).2+1 := by
    obtain ⟨C,π,hπ,he,hC⟩ := restricted_cut_step R M hM threshold s hcan hSteps a j
    have hK := isCompact_current_high_cut R M hM threshold a (s.stage j).2 (hcan a j)
    have hneC : C.Nonempty := by
      rw [hC]
      exact selectedMaximum_nonempty_of_compact_high_cut (X := CMfd.of (n := n) U)
        (Y := (t.stage j).1) R M0 hd (t.stage j).2 (hct j) threshold hK hne
    obtain ⟨z,hz⟩ := hneC
    have hfibre : z∈(t.stage j).2.proj ⁻¹' K := by
      apply current_high_cut_subset_fibre R M hM threshold a (s.stage j).2 (hcan a j)
      exact selectedMaximum_subset_strictCut R M0 (t.stage j).2 threshold (hC ▸ hz)
    rw [he,countCentresMeeting,if_pos (show (C∩(t.stage j).2.proj ⁻¹' K).Nonempty from ⟨z,hz,hfibre⟩)]
  have hcount : ∀ j,(strictCut R M0 (t.stage j).2 threshold).Nonempty → j ≤ countCentresMeeting K (t.stage j).2 := by
    intro j
    induction j with
    | zero => intro _;exact Nat.zero_le _
    | succ j ih =>
      intro hne
      have hprev := hback j hne
      rw [hinc j hprev]
      exact Nat.succ_le_succ (ih hprev)
  refine ⟨m+1,?_⟩
  intro j hj
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := hcount j ⟨z,hz⟩
  have hb := hm j
  omega

private def lastCutCentreImage : {Y : CMfd.{u} n} → BlowupTower X Y → Set X
  | _,.refl => ∅
  | _,.step T C _ _ => T.proj '' C

private theorem centreImage_cut_sequence
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (threshold : Λ) [DiscreteTopology (strictCut R M .refl threshold)]
    (s : GrowingSeq X) (hSteps : CutParallelSteps R M threshold s) (j : ℕ) :
    centreImage s j=(s.stage j).2.proj '' parallelCutCentre R M (s.stage j).2 threshold := by
  obtain ⟨π,hπ,hread⟩ := exists_step_map s j
  have hr := congrArg (lastCutCentreImage (X := X)) hread
  change lastCutCentreImage (s.stage (j+1)).2=centreImage s j at hr
  rw [←hr]
  obtain ⟨C,ρ,hρ,he,hC⟩ := hSteps j
  rw [he]
  change (s.stage j).2.proj '' C=_
  rw [hC]

/-- The SAME internally constructed global history locally erases the high cut. -/
theorem exists_discrete_cut_locally_finite_history
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (threshold : Λ)
    [DiscreteTopology (strictCut R M .refl threshold)] :
    ∃ s : GrowingSeq X,
      (∀ j,IsGeoTestTower M (s.stage j).2) ∧
      (∀ (a : strictCut R M .refl threshold) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
          (R.inv (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M))
          (restrict (cutWindow R M threshold a) (s.stage j).2)) ∧
      CutParallelSteps R M threshold s ∧
      (∀ a : strictCut R M .refl threshold,∃ N,∀ j,N ≤ j → strictCut R
        (MarkedIdeal.pullback (Subtype.val : cutWindow R M threshold a → X) M)
        (restrict (cutWindow R M threshold a) (s.stage j).2) threshold=∅) ∧
      (∀ j,centreImage s j ⊆ strictCut R M .refl threshold) ∧
      LocallyFinite (centreImage s) ∧ (∀ j,IsClosed (centreImage s j)) ∧
      ∀ x : X,∃ (N : ℕ) (W : Opens X),x∈W ∧
        (∀ j,N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
          (hπ : IsBlowupAlong n (stepCentre s j) π),
          (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
          IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (W : Set X))) ∧
        ∀ r,ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 W) (tailTower s N r)) := by
  obtain ⟨s,hTest,hCan,hSteps⟩ := exists_discrete_cut_sequence R M hM threshold
  have hClear := eventually_erases_cut R M hM threshold s hCan hSteps
  have himage : ∀ j,centreImage s j ⊆ strictCut R M .refl threshold := by
    intro j
    rw [centreImage_cut_sequence R M threshold s hSteps j]
    rintro x ⟨y,hy,rfl⟩
    exact parallelCutCentre_subset_initial_cut R M hM (s.stage j).2 threshold (fun a => hCan a j) hy
  have havoid : ∀ x : X,∃ (N : ℕ) (W : Opens X),x∈W ∧
      ∀ j,N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (W : Set X)) := by
    intro x
    by_cases hx : x∈strictCut R M .refl threshold
    · let a : strictCut R M .refl threshold := ⟨x,hx⟩
      obtain ⟨N,hN⟩ := hClear a
      let U := cutWindow R M threshold a
      refine ⟨N,U,mem_cutWindow R M threshold a,fun j hj => disjoint_left.mpr (fun y hyC hyU => ?_)⟩
      have hy : (s.stage j).2.proj y∈centreImage s j := ⟨y,hyC,rfl⟩
      rw [centreImage_cut_sequence R M threshold s hSteps j] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      have hzU : (s.stage j).2.proj z∈U := hzy.symm ▸ hyU
      let zp : openPreimage (s.stage j).2 U := ⟨z,hzU⟩
      have hSel : zp∈selectedMaximum R (MarkedIdeal.pullback (Subtype.val : U → X) M)
          (restrict U (s.stage j).2) threshold :=
        (Set.ext_iff.mp (preimage_parallelCutCentre R M hM (s.stage j).2 threshold (fun b => hCan b j) a) zp).mp hz
      have hHigh := selectedMaximum_subset_strictCut R _ _ threshold hSel
      rw [hN j hj] at hHigh
      exact hHigh
    · let W : Opens X := ⟨(strictCut R M .refl threshold)ᶜ,
        (isClosed_strictCut R M hM .refl trivial threshold).isOpen_compl⟩
      refine ⟨0,W,hx,fun j _ => disjoint_left.mpr (fun y hyC hyW => ?_)⟩
      exact hyW (himage j ⟨y,hyC,rfl⟩)
  have hfinite : LocallyFinite (centreImage s) := by
    intro x
    obtain ⟨N,W,hx,hN⟩ := havoid x
    refine ⟨W,W.isOpen.mem_nhds hx,(finite_Iio N).subset ?_⟩
    rintro j ⟨y,⟨z,hz,rfl⟩,hy⟩
    exact lt_of_not_ge (fun hge => disjoint_left.mp (hN j hge) hz hy)
  refine ⟨s,hTest,hCan,hSteps,hClear,himage,hfinite,isClosed_centreImage s,?_⟩
  intro x
  obtain ⟨N,W,hx,hN⟩ := havoid x
  refine ⟨N,W,hx,fun j hj => isIsomorphismOver_step_of_disjoint s j W (hN j hj),?_⟩
  intro r
  exact (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s N W hN r)

/-- ONLY original full invariant data supply the actual relative LF cleanup. -/
theorem exists_original_discrete_full_cut_cleanup
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (threshold : ValTy n)
    [DiscreteTopology (strictCut (canonicalInvariant n) M .refl threshold)] :
    ∃ s : GrowingSeq X,
      (∀ j,IsGeoTestTower M (s.stage j).2) ∧
      (∀ (a : strictCut (canonicalInvariant n) M .refl threshold) j,
        IsCanonical (MarkedIdeal.pullback (Subtype.val : cutWindow (canonicalInvariant n) M threshold a → X) M)
          ((canonicalInvariant n).inv (MarkedIdeal.pullback
            (Subtype.val : cutWindow (canonicalInvariant n) M threshold a → X) M))
          (restrict (cutWindow (canonicalInvariant n) M threshold a) (s.stage j).2)) ∧
      CutParallelSteps (canonicalInvariant n) M threshold s ∧
      (∀ a : strictCut (canonicalInvariant n) M .refl threshold,∃ N,∀ j,N ≤ j →
        strictCut (canonicalInvariant n) (MarkedIdeal.pullback
          (Subtype.val : cutWindow (canonicalInvariant n) M threshold a → X) M)
          (restrict (cutWindow (canonicalInvariant n) M threshold a) (s.stage j).2) threshold=∅) ∧
      (∀ j,centreImage s j ⊆ strictCut (canonicalInvariant n) M .refl threshold) ∧
      LocallyFinite (centreImage s) ∧ (∀ j,IsClosed (centreImage s j)) ∧
      ∀ x : X,∃ (N : ℕ) (W : Opens X),x∈W ∧
        (∀ j,N ≤ j → ∃ (π : (s.stage (j+1)).1 → (s.stage j).1)
          (hπ : IsBlowupAlong n (stepCentre s j) π),
          (s.stage (j+1)).2=.step (s.stage j).2 (stepCentre s j) π hπ ∧
          IsIsomorphismOver n π ((s.stage j).2.proj ⁻¹' (W : Set X))) ∧
        ∀ r,ResolutionInvariantExt.IsEmptyTower
          (restrict (openPreimage (s.stage N).2 W) (tailTower s N r)) :=
  exists_discrete_cut_locally_finite_history (canonicalInvariant n) M hM threshold

end
end Hironaka.HironakaOriginalDiscreteFullCutHistory
