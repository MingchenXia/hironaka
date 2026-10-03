/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution invariants with local finiteness along growing sequences

Property (8) of a resolution invariant ("local finiteness") is replaced by its **per-sequence** form, in a NEW
structure in a NEW module; `ResolutionInvariantExt` and its predecessor `ResolutionInvariantSpec` stay unchanged
(kept); no new invariance property is added.

The uniform form of (8) (`ResolutionInvariantExt.ResolutionInvariant.locallyFinite`: one bound `m`, for each compact
`K`, valid for every canonical segment) cannot be derived for the inductive step from the other properties:
canonical segments branch at every step (a centre may be empty or the maximum locus), and inserting an empty step in
the middle of a segment changes the values of the general step. What the inductive step proves is the per-sequence
form: **along every growing sequence of canonical segments** (each extending the previous one by one blowup) **only
finitely many nonempty centres meet a compact set `K`**. This suffices for the resolution
(`exists_isGeoResolution_isCanonicalSegment`): iterate the blowup of the maximum locus; if no stage were a
resolution, the iteration (by dependent choice) would be a growing sequence of canonical segments with infinitely
many nonempty centres, meeting the compact base.

## Main definitions

* `GrowingSeq X`: a growing sequence of towers over `X` -- stage `0` is the empty tower, stage `i + 1` is stage `i`
  followed by one blowup;
* `IsInvValue n k inv`: properties (1)--(7) and (4') of `hir:centre-function` for a value function `inv`, in the shape of the
  fields of `ResolutionInvariantExt.ResolutionInvariant` (no data, no (8));
* `SeqLocallyFinite n k inv`: property (8), per-sequence form;
* `ResolutionInvariant n k Λ`: the structure (`inv`, `isInvValue`, `seqLocallyFinite`).

## Main results

* `ResolutionInvariant.ofExt`: the uniform form of (8) implies the per-sequence form (every resolution invariant of
  `ResolutionInvariantExt` is one here); `ResolutionInvariant.ofDimZero`: the base case;
* `IsInvValue.isAdmissibleCentre_maxLocus`, `IsInvValue.isGeoTestTower_of_isCanonical`: canonical segments are multiple test
  blow-ups;
* `exists_isGeoResolution_of_seqFinite`: the abstract driver with per-sequence finiteness (dependent choice);
* **`exists_isGeoResolution_isCanonicalSegment`**: over a compact base every marked ideal of the domain is resolved
  by a canonical segment.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantSeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism.MarkedIdeal Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantOrder Hironaka.ResolutionDriver
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

/-! ### Growing sequences -/

/-- **A growing sequence of towers over `X`**: stage `0` is the empty tower, and stage `i + 1` is stage `i` followed by one
blowup. -/
structure GrowingSeq (X : CMfd.{u} n) where
  /-- The stages: the last stage of the `i`-th tower and the tower. -/
  stage : ℕ → Σ Y : CMfd.{u} n, BlowupTower X Y
  /-- Stage `0` is the empty tower. -/
  zero : stage 0 = ⟨X, .refl⟩
  /-- Stage `i + 1` extends stage `i` by one blowup. -/
  succ : ∀ i, ∃ (C : Set (stage i).1) (π : (stage (i + 1)).1 → (stage i).1) (hπ : IsBlowupAlong n C π),
    (stage (i + 1)).2 = .step (stage i).2 C π hπ

/-! ### The properties without (8), and (8) along growing sequences -/

variable (n) in
/-- **Properties (1)--(7) and (4') of `hir:centre-function`** for a value function `inv`, for the marked ideals of the domain
`IsInvDomain k` and along their canonical segments, in the shape of the fields of `ResolutionInvariantExt.ResolutionInvariant`
(no data, no property (8)). -/
structure IsInvValue (k : ℕ) {Λ : Type v} [LinearOrder Λ]
    (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop where
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → inv 𝔪 T y ≤ l) →
      (pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv 𝔪 T y = l})
  /-- (2) Upper semicontinuity on the cosupport, along canonical segments. -/
  usc : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
      IsInvUSCOn (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp
  /-- (3) Decrease under the blowup of the maximum locus. -/
  decrease : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsCanonical 𝔪 (inv 𝔪) T → C.Nonempty →
      C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp →
      ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        (π z ∈ C → inv 𝔪 (.step T C π hπ) z < inv 𝔪 T (π z)) ∧
        (π z ∉ C → inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z))
  /-- (4) Empty steps, after a canonical segment. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π), C = ∅ →
      IsCanonical 𝔪 (inv 𝔪) T → ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z)
  /-- (4') Empty prefixes: re-basing a canonical segment after a part with only empty centres. -/
  emptyPrefix : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y), IsEmptyTower T₀ →
      IsCanonical 𝔪 (inv 𝔪) (T₀.append T₁) → ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp,
        inv 𝔪 (T₀.append T₁) z = inv (geoTransformAlong 𝔪 T₀) T₁ z
  /-- (5) Restriction to open sets, along canonical segments. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      inv (pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = inv 𝔪 T p
  /-- (6) Isomorphisms of towers over biholomorphisms, along canonical segments. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      IsTowerIso Φ T' T χ → IsCanonical 𝔪 (inv 𝔪) T → ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp →
        inv (pullback Φ 𝔪) T' p = inv 𝔪 T (χ p)
  /-- (7) Independence of the representative, along canonical segments. -/
  representative : ∀ {X : CMfd.{u} n} (𝔪 𝔫 : MarkedIdeal n X), IsInvDomain k 𝔪 → IsInvDomain k 𝔫 →
    RestrictEquiv 𝔪 𝔫 → ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
      ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv 𝔪 T y = inv 𝔫 T y

variable (n) in
/-- **Property (8), per-sequence form**: for every marked ideal of the domain and every compact `K ⊆ X`, along every
growing sequence of canonical segments only finitely many nonempty centres meet (the preimage of) `K` -- the numbers
of centres meeting `K` of the stages are bounded. -/
def SeqLocallyFinite (k : ℕ) {Λ : Type v} [LinearOrder Λ]
    (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ K : Set X, IsCompact K →
    ∀ s : GrowingSeq X, (∀ i, IsCanonical 𝔪 (inv 𝔪) (s.stage i).2) →
      ∃ m : ℕ, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m

variable (n) in
/-- **A resolution invariant in dimension `≤ k`** (`hir:centre-function-seq`): a value function with properties (1)--(7),
(4') of `hir:centre-function` and property (8) in its per-sequence form. -/
structure ResolutionInvariant (k : ℕ) (Λ : Type v) [LinearOrder Λ] where
  /-- The invariant. -/
  inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ
  /-- Properties (1)--(7) and (4'). -/
  isInvValue : IsInvValue n k inv
  /-- Property (8), per-sequence form. -/
  seqLocallyFinite : SeqLocallyFinite n k inv

/-! ### From the uniform form of (8) -/

section Ext

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- The properties (1)--(7), (4') of a resolution invariant of `ResolutionInvariantExt`. -/
theorem isInvValue_ext (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) : IsInvValue n k R.inv :=
  ⟨R.admissible, R.usc, R.decrease, R.emptyStep, R.emptyPrefix, R.restrictOpen, R.towerIso, R.representative⟩

/-- **The uniform form of (8) implies the per-sequence form**: one bound for all canonical segments bounds the counts along
every growing sequence of them. -/
theorem seqLocallyFinite_ext (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) :
    SeqLocallyFinite n k R.inv := by
  intro X 𝔪 h K hK s hcan
  obtain ⟨m, hm⟩ := R.locallyFinite 𝔪 h K hK
  exact ⟨m, fun i => hm _ (hcan i)⟩

/-- **Every resolution invariant of `ResolutionInvariantExt` is a resolution invariant here.** -/
def ResolutionInvariant.ofExt (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) :
    ResolutionInvariant.{u, v} n k Λ :=
  ⟨R.inv, isInvValue_ext R, seqLocallyFinite_ext R⟩

/-- **The base case** (`hir:canonical-centres-zero`): in dimension `≤ 0` every constant function is a resolution
invariant. -/
def ResolutionInvariant.ofDimZero (Λ : Type v) [LinearOrder Λ] (l₀ : Λ) : ResolutionInvariant.{u, v} n 0 Λ :=
  ResolutionInvariant.ofExt (ResolutionInvariantExt.ResolutionInvariant.ofDimZero Λ l₀)

end Ext

/-! ### Canonical segments are multiple test blow-ups -/

namespace IsInvValue

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
  {X : CMfd.{u} n}

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up. -/
theorem isAdmissibleCentre_maxLocus (hI : IsInvValue n k inv) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (inv 𝔪) T) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := hI.admissible 𝔪 h T hcan ⊤ (inv 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups.** -/
theorem isGeoTestTower_of_isCanonical (hI : IsInvValue n k inv) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical hI h T hT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus hI h T hT hTt

end IsInvValue

/-! ### The driver -/

section Driver

variable {X : CMfd.{u} n}

/-- **A growing sequence from an iterated one-step extension**: for a set `S` of towers over `X` with a map `next : S → S`
extending each tower by one blowup, the iterates of `next` from the empty tower form a growing sequence. -/
def GrowingSeq.ofIterate {S : Type*} (toTower : S → Σ Y : CMfd.{u} n, BlowupTower X Y) (next : S → S) (s₀ : S)
    (h₀ : toTower s₀ = ⟨X, .refl⟩)
    (hnext : ∀ s, ∃ (C : Set (toTower s).1) (π : (toTower (next s)).1 → (toTower s).1) (hπ : IsBlowupAlong n C π),
      (toTower (next s)).2 = .step (toTower s).2 C π hπ) : GrowingSeq X where
  stage i := toTower (next^[i] s₀)
  zero := h₀
  succ i := by
    show ∃ (C : Set (toTower (next^[i] s₀)).1) (π : (toTower (next^[i + 1] s₀)).1 → (toTower (next^[i] s₀)).1)
      (hπ : IsBlowupAlong n C π), (toTower (next^[i + 1] s₀)).2 = .step (toTower (next^[i] s₀)).2 C π hπ
    rw [Function.iterate_succ_apply']
    exact hnext _

/-- **The abstract driver with per-sequence finiteness** (`hir:invariant-driver-seq`): over a compact base, let `P` be a class
of towers over `X` containing the empty tower such that every multiple test blow-up `T ∈ P` with nonempty cosupport has a
nonempty admissible centre `C` with empty interior all of whose blowups extend `T` inside `P`.  If along every growing
sequence of multiple test blow-ups in `P` the numbers of centres meeting `X` are bounded, some tower of `P` is a resolution.
Proof by contradiction with dependent choice: otherwise iterating the blowup of the chosen centres gives a growing sequence
whose `i`-th stage has `i` centres meeting `X`. -/
theorem exists_isGeoResolution_of_seqFinite [CompactSpace X] (𝔪 : MarkedIdeal n X)
    (P : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop) (hP : P (BlowupTower.refl : BlowupTower X X))
    (hstep : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), P T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      ∃ C : Set Y, (geoTransformAlong 𝔪 T).IsAdmissibleCentre C ∧ interior C = ∅ ∧ C.Nonempty ∧
        ∀ {Z : CMfd.{u} n} (π : Z → Y) (hπ : IsBlowupAlong n C π), P (BlowupTower.step T C π hπ))
    (hfin : ∀ s : GrowingSeq X, (∀ i, P (s.stage i).2) → (∀ i, IsGeoTestTower 𝔪 (s.stage i).2) →
      ∃ m : ℕ, ∀ i, countCentresMeeting (univ : Set X) (s.stage i).2 ≤ m) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), P T ∧ IsGeoResolution 𝔪 T := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- every tower of `P` which is a multiple test blow-up has nonempty cosupport
  have hne : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), P T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty := by
    intro Y T hPT hT
    by_contra hc
    exact hno Y T hPT ⟨hT, not_nonempty_iff_eq_empty.mp hc⟩
  -- the towers of `P` which are multiple test blow-ups, and one step of the iteration
  let S := {p : Σ Y : CMfd.{u} n, BlowupTower X Y // P p.2 ∧ IsGeoTestTower 𝔪 p.2}
  have hext : ∀ p : S, ∃ q : S, ∃ (C : Set p.1.1) (π : q.1.1 → p.1.1) (hπ : IsBlowupAlong n C π),
      q.1.2 = .step p.1.2 C π hπ ∧ C.Nonempty := by
    intro p
    obtain ⟨C, hC, hint, hCne, hPstep⟩ := hstep p.1.2 p.2.1 p.2.2 (hne p.1.2 p.2.1 p.2.2)
    obtain ⟨Z, π, hπ⟩ := exists_blowup C hC.1 hint
    exact ⟨⟨⟨Z, .step p.1.2 C π hπ⟩, hPstep π hπ, (isGeoTestTower_step_iff 𝔪 p.1.2 C π hπ).mpr ⟨p.2.2, hC⟩⟩,
      C, π, hπ, rfl, hCne⟩
  choose next hnext using hext
  let s₀ : S := ⟨⟨X, .refl⟩, hP, trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : S => p.1) next s₀ rfl
    fun p => by
      obtain ⟨C, π, hπ, he, -⟩ := hnext p
      exact ⟨C, π, hπ, he⟩
  obtain ⟨m, hm⟩ := hfin s (fun i => (next^[i] s₀).2.1) (fun i => (next^[i] s₀).2.2)
  -- the `i`-th stage has `i` centres meeting `X`
  have hcount : ∀ i, countCentresMeeting (univ : Set X) (next^[i] s₀).1.2 = i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨C, π, hπ, he, hCne⟩ := hnext (next^[i] s₀)
      rw [he]
      have h1 : (C ∩ (next^[i] s₀).1.2.proj ⁻¹' (univ : Set X)).Nonempty := by
        rw [preimage_univ, inter_univ]; exact hCne
      simp only [countCentresMeeting, if_pos h1, ih]
  have := hm (m + 1)
  rw [show countCentresMeeting (univ : Set X) (s.stage (m + 1)).2 = m + 1 from hcount (m + 1)] at this
  omega

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **A resolution invariant resolves every marked ideal of its domain over a compact base, by a canonical segment**
(`hir:invariant-driver-seq`): iterate the blowup of the maximum locus of the invariant on the cosupport.  The cosupports are
closed, the invariant is upper semicontinuous on them (2), so the maximum locus is nonempty; it is an admissible centre (1)
with empty interior; along the iteration only finitely many nonempty centres meet the compact base (8), so the iteration
stops (`exists_isGeoResolution_of_seqFinite`). -/
theorem exists_isGeoResolution_isCanonicalSegment [CompactSpace X] (R : ResolutionInvariant.{u, v} n k Λ)
    {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  refine exists_isGeoResolution_of_seqFinite 𝔪 (fun T => IsCanonicalSegment 𝔪 (R.inv 𝔪) T) trivial ?_ ?_
  · intro Y T hPT hT hne
    have := compactSpace_of_tower T
    have hcan := isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) T hPT
    have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
    have hclosed : IsClosed (geoTransformAlong 𝔪 T).cosupp :=
      GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
    have hCne := maxLocus_nonempty hclosed (R.isInvValue.usc 𝔪 h T hcan) hne
    exact ⟨_, R.isInvValue.isAdmissibleCentre_maxLocus h T hcan hT, interior_maxLocus_eq_empty h T hT _, hCne,
      fun π hπ => ⟨hPT, hCne, rfl⟩⟩
  · intro s hP _
    exact R.seqLocallyFinite 𝔪 h univ isCompact_univ s fun i =>
      isCanonical_of_isCanonicalSegment (𝔪 := 𝔪) (R.inv 𝔪) _ (hP i)

end Driver

end

end Hironaka.ResolutionInvariantSeq
