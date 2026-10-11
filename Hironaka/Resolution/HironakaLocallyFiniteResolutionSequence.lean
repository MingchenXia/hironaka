/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Invariant.RestrictEmptyTower
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false

/-!
# Actual stabilization of growing canonical sequences

Blueprint `hironaka-locally-finite-resolution-extension.tex`.
The actual next-centre images are closed and locally finite, and every compact
set has an open neighbourhood over which all later actual blowups are
isomorphisms. These are gluing producers for an existing genuine canonical
sequence. Constructing a globally resolving sequence on a general noncompact
manifold remains a separate, open existence obligation.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaLocallyFiniteResolutionSequence

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers BlowupTowerTransforms MarkedIdeals
open ResolutionInvariantSeq ResolutionInvariantSpec
open RestrictEmptyTower

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual centre in a chosen one-step witness for the growing sequence. -/
def stepCentre (s : GrowingSeq X) (i : ℕ) : Set (s.stage i).1 :=
  (s.succ i).choose

/-- The image of the actual next centre under its actual prefix projection. -/
def centreImage (s : GrowingSeq X) (i : ℕ) : Set X :=
  (s.stage i).2.proj '' stepCentre s i

/-- Choice of the next centre retains an actual map, blowup proof and exact
one-step equality of recorded towers. -/
theorem exists_step_map (s : GrowingSeq X) (i : ℕ) :
    ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
      (hπ : IsBlowupAlong n (stepCentre s i) π),
      (s.stage (i + 1)).2 = .step (s.stage i).2 (stepCentre s i) π hπ :=
  (s.succ i).choose_spec

private def chosenStep (s : GrowingSeq X) (i : ℕ) :
    Σ π : (s.stage (i + 1)).1 → (s.stage i).1,
      {hπ : IsBlowupAlong n (stepCentre s i) π //
        (s.stage (i + 1)).2 = .step (s.stage i).2 (stepCentre s i) π hπ} :=
  ⟨(exists_step_map s i).choose, (exists_step_map s i).choose_spec.choose,
    (exists_step_map s i).choose_spec.choose_spec⟩

/-- The finite tail is built from the actual next maps and actual blowup
proofs, retaining every genuine intermediate stage. -/
def tailTower (s : GrowingSeq X) (N : ℕ) :
    (j : ℕ) → BlowupTower (s.stage N).1 (s.stage (N + j)).1
  | 0 => .refl
  | j + 1 => .step (tailTower s N j) (stepCentre s (N + j))
      (chosenStep s (N + j)).1 (chosenStep s (N + j)).2.1

/-- Appending the actual constructed tail recovers the exact original
recorded stage, and hence its actual projection. -/
theorem append_tailTower (s : GrowingSeq X) (N j : ℕ) :
    (s.stage N).2.append (tailTower s N j) = (s.stage (N + j)).2 := by
  induction j with
  | zero => exact BlowupTower.append_refl _
  | succ j ih =>
    rw [tailTower, BlowupTower.append_step, ih]
    exact (chosenStep s (N + j)).2.2.symm

open Classical in
/-- The actual recursive centre count increments exactly when this next
centre image meets the base set. -/
theorem countCentresMeeting_step (s : GrowingSeq X) (K : Set X) (i : ℕ) :
    countCentresMeeting K (s.stage (i + 1)).2 =
      countCentresMeeting K (s.stage i).2 +
        if (centreImage s i ∩ K).Nonempty then 1 else 0 := by
  classical
  obtain ⟨π, hπ, hstep⟩ := exists_step_map s i
  have hiff : (stepCentre s i ∩ (s.stage i).2.proj ⁻¹' K).Nonempty ↔
      (centreImage s i ∩ K).Nonempty := by
    constructor
    · rintro ⟨y, hyC, hyK⟩
      exact ⟨(s.stage i).2.proj y, ⟨y, hyC, rfl⟩, hyK⟩
    · rintro ⟨x, ⟨y, hyC, rfl⟩, hyK⟩
      exact ⟨y, hyC, hyK⟩
  rw [hstep]
  simp only [countCentresMeeting, hiff]

/-- Recorded counts along a genuine growing sequence are nondecreasing. -/
theorem monotone_countCentresMeeting (s : GrowingSeq X) (K : Set X) :
    Monotone (fun i => countCentresMeeting K (s.stage i).2) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [countCentresMeeting_step]
  exact Nat.le_add_right _ _

private theorem exists_constant_tail_of_bounded_monotone {f : ℕ → ℕ}
    (hmono : Monotone f) {m : ℕ} (hbound : ∀ i, f i ≤ m) :
    ∃ N, ∀ i, N ≤ i → f i = f N := by
  have hfin : (range f).Finite := (finite_Iic m).subset fun _ ⟨i, hi⟩ => hi ▸ hbound i
  obtain ⟨a, ⟨N, rfl⟩, hmax⟩ :=
    Set.exists_max_image (range f) id hfin ⟨f 0, mem_range_self 0⟩
  exact ⟨N, fun i hi => le_antisymm (hmax (f i) (mem_range_self i)) (hmono hi)⟩

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- Per-sequence local finiteness genuinely forces all later actual centre
images to miss a fixed compact set. -/
theorem exists_no_later_centres_meet_compact
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2)
    {K : Set X} (hK : IsCompact K) :
    ∃ N, ∀ i, N ≤ i → ¬ (centreImage s i ∩ K).Nonempty := by
  classical
  obtain ⟨m, hm⟩ := R.seqLocallyFinite 𝔪 hdom K hK s hcan
  obtain ⟨N, hconstant⟩ :=
    exists_constant_tail_of_bounded_monotone (monotone_countCentresMeeting s K) hm
  refine ⟨N, fun i hi hhit => ?_⟩
  have hcur := hconstant i hi
  have hnext := hconstant (i + 1) (by omega)
  rw [countCentresMeeting_step, if_pos hhit] at hnext
  omega

/-- Only finitely many actual step indices meet a compact base set. -/
theorem finite_centres_meeting_compact
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2)
    {K : Set X} (hK : IsCompact K) :
    {i | (centreImage s i ∩ K).Nonempty}.Finite := by
  obtain ⟨N, hN⟩ := exists_no_later_centres_meet_compact R hdom s hcan hK
  apply (finite_Iio N).subset
  intro i hi
  exact lt_of_not_ge fun hge => hN i hge hi

omit [LinearOrder Λ] in
/-- Actual smooth centres have closed images under the proper tower projection. -/
theorem isClosed_centreImage (s : GrowingSeq X) (i : ℕ) :
    IsClosed (centreImage s i) := by
  obtain ⟨π, hπ, -⟩ := exists_step_map s i
  exact (HironakaLocalPrincipalization.isProperMap_proj (s.stage i).2).isClosedMap _ hπ.1.1

/-- The indexed actual centre images, including possible empty images or
repetitions, are genuinely locally finite on the base. -/
theorem locallyFinite_centreImages
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2) :
    LocallyFinite (centreImage s) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  intro x
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  exact ⟨K, hxK, finite_centres_meeting_compact R hdom s hcan hK⟩

/-- A compact base set has a genuine open neighbourhood avoiding every
later actual centre, using closedness of the entire locally finite tail union. -/
theorem exists_open_no_later_centres
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2)
    {K : Set X} (hK : IsCompact K) :
    ∃ (N : ℕ) (U : Opens X), K ⊆ U ∧
      ∀ i, N ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)) := by
  obtain ⟨N, hN⟩ := exists_no_later_centres_meet_compact R hdom s hcan hK
  have hclosed : IsClosed (⋃ i : {i : ℕ // N ≤ i}, centreImage s i) :=
    ((locallyFinite_centreImages R hdom s hcan).comp_injective Subtype.val_injective).isClosed_iUnion
      (fun i => isClosed_centreImage s i)
  let U : Opens X := ⟨(⋃ i : {i : ℕ // N ≤ i}, centreImage s i)ᶜ, hclosed.isOpen_compl⟩
  refine ⟨N, U, ?_, ?_⟩
  · intro x hxK hxU
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    exact hN i i.2 ⟨x, hxi, hxK⟩
  · intro i hi
    apply disjoint_left.mpr
    intro y hyC hyU
    exact hyU (mem_iUnion.mpr ⟨⟨i, hi⟩, y, hyC, rfl⟩)

omit [LinearOrder Λ] in
/-- A genuine next blowup is an isomorphism over any open base preimage
that its actual centre misses. -/
theorem isIsomorphismOver_step_of_disjoint (s : GrowingSeq X) (i : ℕ) (U : Opens X)
    (hdisj : Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X))) :
    ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
      (hπ : IsBlowupAlong n (stepCentre s i) π),
      (s.stage (i + 1)).2 = .step (s.stage i).2 (stepCentre s i) π hπ ∧
        IsIsomorphismOver n π ((s.stage i).2.proj ⁻¹' (U : Set X)) := by
  obtain ⟨π, hπ, hstep⟩ := exists_step_map s i
  have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hsub : (s.stage i).2.proj ⁻¹' (U : Set X) ⊆ (stepCentre s i)ᶜ := by
    intro y hy hyC
    exact disjoint_left.mp hdisj hyC hy
  refine ⟨π, hπ, hstep, ⟨⟨fun _ hy => hy, ?_, ?_⟩, ?_⟩⟩
  · exact hiso.1.2.1.mono (preimage_mono hsub)
  · intro x hx
    obtain ⟨y, -, hyx⟩ := hiso.1.2.2 (hsub hx)
    exact ⟨y, by simpa only [mem_preimage, hyx] using hx, hyx⟩
  · exact hiso.2.mono (preimage_mono hsub) Subset.rfl

/-- Per-sequence finiteness produces an actual open neighbourhood on which
all later actual blowup maps are isomorphisms, with their full step witnesses. -/
theorem exists_open_isomorphism_tail
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2)
    {K : Set X} (hK : IsCompact K) :
    ∃ (N : ℕ) (U : Opens X), K ⊆ U ∧
      ∀ i, N ≤ i →
        ∃ (π : (s.stage (i + 1)).1 → (s.stage i).1)
          (hπ : IsBlowupAlong n (stepCentre s i) π),
          (s.stage (i + 1)).2 = .step (s.stage i).2 (stepCentre s i) π hπ ∧
            IsIsomorphismOver n π ((s.stage i).2.proj ⁻¹' (U : Set X)) := by
  obtain ⟨N, U, hKU, htail⟩ := exists_open_no_later_centres R hdom s hcan hK
  exact ⟨N, U, hKU, fun i hi => isIsomorphismOver_step_of_disjoint s i U (htail i hi)⟩

omit [LinearOrder Λ] in
/-- Open avoidance of all actual later centres gives avoidance for every
actual finite tail, via the proved equality of the appended prefix and tail. -/
theorem centresAvoid_tailTower (s : GrowingSeq X) (N : ℕ) (U : Opens X)
    (havoid : ∀ i, N ≤ i →
      Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X))) :
    ∀ j, CentresAvoid (openPreimage (s.stage N).2 U) (tailTower s N j) := by
  intro j
  induction j with
  | zero => trivial
  | succ j ih =>
    change CentresAvoid (openPreimage (s.stage N).2 U) (tailTower s N j) ∧
      Disjoint (stepCentre s (N + j))
        ((tailTower s N j).proj ⁻¹' (openPreimage (s.stage N).2 U : Set (s.stage N).1))
    refine ⟨ih, ?_⟩
    have heq : (tailTower s N j).proj ⁻¹'
        (openPreimage (s.stage N).2 U : Set (s.stage N).1) =
        (s.stage (N + j)).2.proj ⁻¹' (U : Set X) := by
      change ((s.stage N).2.proj ∘ (tailTower s N j).proj) ⁻¹' (U : Set X) = _
      rw [← BlowupTower.proj_append, append_tailTower]
    rw [heq]
    exact havoid (N + j) (Nat.le_add_right N j)

/-- Every entire actual finite later tail restricts to an empty-centre tower
on one genuine open neighbourhood of the prescribed compact base set. -/
theorem exists_open_empty_restricted_tails
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hcan : ∀ i, IsCanonical 𝔪 (R.inv 𝔪) (s.stage i).2)
    {K : Set X} (hK : IsCompact K) :
    ∃ (N : ℕ) (U : Opens X), K ⊆ U ∧
      ∀ j, ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage N).2 U) (tailTower s N j)) := by
  obtain ⟨N, U, hKU, havoid⟩ := exists_open_no_later_centres R hdom s hcan hK
  exact ⟨N, U, hKU, fun j =>
    (isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s N U havoid j)⟩

end

end Hironaka.HironakaLocallyFiniteResolutionSequence
