import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Analytic.TowerPreimageCompact

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Growing sequences of towers: restriction to open sets, tails, and counting centres

Hironaka phase H2 (TN3), for the per-sequence local finiteness of the resolution invariant (human decision I-1139 (b));
claim I-0977 C-0213 (`GrowingSeq.restrict` assigned to TN3 by TN-CLASSICAL, I-0981 C-0163).  Blueprint
`bcalc:growing-seq-tail` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the proof of
Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), local finiteness.

TN-CLASSICAL's `ResolutionInvariantSeq.GrowingSeq X` is a sequence of towers over `X`, starting with the empty tower, each
extending the previous one by one blowup; property (8) in its per-sequence form (`ResolutionInvariantSeq.SeqLocallyFinite`)
asks for a bound on the numbers of nonempty centres meeting a compact `K`.  The phase argument passes, at a stage `a`, to the
part of the sequence after `a`, restricted to open sets of the stage `a` on which lower-dimensional invariants live.  This module
provides the sequences and the counting:

* **`GrowingSeq.restrict s U`**: the restriction of a growing sequence to an open set `U ⊆ X` is a growing sequence over `U`;
  `count_restrict`: for `K ⊆ U` it has the same numbers of centres meeting `K`;
* **`GrowingSeq.tail s a`**: the stages after `a`, as towers over the last stage of the `a`-th tower, form a growing sequence;
  `stage_add_eq_append`: the `(a + i)`-th tower is the `a`-th one followed by the `i`-th tower of the tail; `count_add`: the
  count splits accordingly;
* `count_mono`: counts never decrease along a growing sequence;
* **`exists_bound_of_tail_restrict`**: for a growing sequence of multiple test blow-ups of a marked ideal of the domain, if at a
  stage `a` finitely many sets `L j ⊆ W j` (`W j` open) cover the part of the cosupport over `K`, and the counts of `L j` along the
  restricted tails `(s.tail a).restrict (W j)` are bounded, then the counts of `K` along `s` are bounded.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ResolutionInvariantSeq.GrowingSeq

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.TowerPreimageCompact
open Hironaka.ResolutionInvariantSpec (IsInvDomain countCentresMeeting)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-! ### Restriction to an open set -/

/-- **The restriction of a growing sequence to an open set `U` of the base**: the `i`-th tower is the restriction of the
`i`-th tower (`BlowupTowerTransforms.restrict`); it is again a growing sequence. -/
def restrict (s : GrowingSeq X) (U : Opens X) : GrowingSeq (CMfd.of (n := n) U) where
  stage i := ⟨CMfd.of (n := n) (openPreimage (s.stage i).2 U), BlowupTowerTransforms.restrict U (s.stage i).2⟩
  zero := by
    rw [s.zero]
    rfl
  succ i := by
    obtain ⟨C, π, hπ, heq⟩ := s.succ i
    show ∃ (C' : Set (openPreimage (s.stage i).2 U))
      (π' : openPreimage (s.stage (i + 1)).2 U → openPreimage (s.stage i).2 U)
      (hπ' : IsBlowupAlong n C' π'),
      BlowupTowerTransforms.restrict U (s.stage (i + 1)).2 =
        .step (BlowupTowerTransforms.restrict U (s.stage i).2) C' π' hπ'
    rw [heq]
    obtain ⟨π', hπ', h⟩ := exists_restrict_step U (s.stage i).2 C π hπ
    exact ⟨_, π', hπ', h⟩

theorem restrict_stage (s : GrowingSeq X) (U : Opens X) (i : ℕ) :
    (s.restrict U).stage i =
      ⟨CMfd.of (n := n) (openPreimage (s.stage i).2 U), BlowupTowerTransforms.restrict U (s.stage i).2⟩ := rfl

/-- **The counts along the restricted sequence** of a subset `K ⊆ U` are those along the sequence
(`ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset`). -/
theorem count_restrict (s : GrowingSeq X) (U : Opens X) {K : Set X} (hKU : K ⊆ U) (i : ℕ) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) ((s.restrict U).stage i).2 =
      countCentresMeeting K (s.stage i).2 :=
  ResolutionInvariantSegments.countCentresMeeting_restrict_of_subset U hKU (s.stage i).2

/-! ### Tails -/

/-- **The tower from the stage `a` to the stage `a + i`** (the blowups chosen by `s.succ`). -/
def tailTower (s : GrowingSeq X) (a : ℕ) : (i : ℕ) → BlowupTower (s.stage a).1 (s.stage (a + i)).1
  | 0 => .refl
  | i + 1 => .step (tailTower s a i) (s.succ (a + i)).choose (s.succ (a + i)).choose_spec.choose
      (s.succ (a + i)).choose_spec.choose_spec.choose

/-- **The `(a + i)`-th tower is the `a`-th tower followed by the tail tower.** -/
theorem stage_add_eq_append (s : GrowingSeq X) (a : ℕ) :
    ∀ i : ℕ, (s.stage (a + i)).2 = (s.stage a).2.append (tailTower s a i)
  | 0 => rfl
  | i + 1 => by
      have h := (s.succ (a + i)).choose_spec.choose_spec.choose_spec
      have ih := stage_add_eq_append s a i
      show (s.stage (a + i + 1)).2 = .step ((s.stage a).2.append (tailTower s a i)) (s.succ (a + i)).choose
        (s.succ (a + i)).choose_spec.choose (s.succ (a + i)).choose_spec.choose_spec.choose
      rw [← ih]
      exact h

/-- **The tail of a growing sequence from the stage `a`**: the towers from the stage `a` on, over the last stage of the `a`-th
tower; it is a growing sequence. -/
def tail (s : GrowingSeq X) (a : ℕ) : GrowingSeq (s.stage a).1 where
  stage i := ⟨(s.stage (a + i)).1, tailTower s a i⟩
  zero := rfl
  succ _ := ⟨_, _, _, rfl⟩

theorem tail_stage (s : GrowingSeq X) (a i : ℕ) : (s.tail a).stage i = ⟨(s.stage (a + i)).1, tailTower s a i⟩ := rfl

/-- **The count splits at the stage `a`**: the centres of the `(a + i)`-th tower meeting `K` are those of the `a`-th tower plus
those of the `i`-th tower of the tail meeting the preimage of `K`. -/
theorem count_add (s : GrowingSeq X) (K : Set X) (a i : ℕ) :
    countCentresMeeting K (s.stage (a + i)).2 =
      countCentresMeeting K (s.stage a).2 + countCentresMeeting ((s.stage a).2.proj ⁻¹' K) ((s.tail a).stage i).2 := by
  rw [stage_add_eq_append s a i]
  exact countCentresMeeting_append K (s.stage a).2 (tailTower s a i)

/-- **Counts never decrease along a growing sequence.** -/
theorem count_mono (s : GrowingSeq X) (K : Set X) {i j : ℕ} (hij : i ≤ j) :
    countCentresMeeting K (s.stage i).2 ≤ countCentresMeeting K (s.stage j).2 := by
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih =>
      obtain ⟨C, π, hπ, heq⟩ := s.succ j
      rw [heq]
      exact ih.trans (Nat.le_add_right _ _)

/-! ### Bounded counts from bounded counts along restricted tails -/

section Bound

variable {k : ℕ} {𝔪 : MarkedIdeal n X}

/-- **Local finiteness from the restricted tails**: let `s` be a growing sequence of multiple test blow-ups of a marked ideal of
the domain, `K` a set of the base and `a` a stage.  If finitely many sets `L j ⊆ W j` (`W j` open in the stage `a`) cover the part
`T_a⁻¹K ∩ cosupp 𝔪_{T_a}` of the cosupport over `K` (compact for `K` compact, `TowerPreimageCompact.isCompact_preimage_inter_cosupp`,
so such covers by compact `L j` exist as soon as open sets `W j` cover it), and along each restricted tail
`(s.tail a).restrict (W j)` the counts of `L j` are bounded, then the counts of `K` along `s` are bounded. -/
theorem exists_bound_of_tail_restrict (h : IsInvDomain k 𝔪) (s : GrowingSeq X)
    (hs : ∀ i, IsGeoTestTower 𝔪 (s.stage i).2) (K : Set X) (a : ℕ) {ι : Type*} (t : Finset ι)
    (W : ι → Opens (s.stage a).1) (L : ι → Set (s.stage a).1) (hLW : ∀ j ∈ t, L j ⊆ W j)
    (hcover : (s.stage a).2.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 (s.stage a).2).cosupp ⊆ ⋃ j ∈ t, L j)
    (hbound : ∀ j ∈ t, ∃ m : ℕ, ∀ i, countCentresMeeting ((Subtype.val : W j → (s.stage a).1) ⁻¹' L j)
      (((s.tail a).restrict (W j)).stage i).2 ≤ m) :
    ∃ m : ℕ, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m := by
  classical
  choose! m hm using hbound
  refine ⟨countCentresMeeting K (s.stage a).2 + ∑ j ∈ t, m j, fun i => ?_⟩
  rcases le_or_gt i a with hia | hai
  · exact (s.count_mono K hia).trans (Nat.le_add_right _ _)
  · obtain ⟨d, rfl⟩ : ∃ d, i = a + d := ⟨i - a, by omega⟩
    have hT : IsGeoTestTower 𝔪 ((s.stage a).2.append (tailTower s a d)) := by
      rw [← stage_add_eq_append s a d]
      exact hs (a + d)
    rw [count_add, Nat.add_le_add_iff_left]
    show countCentresMeeting ((s.stage a).2.proj ⁻¹' K) (tailTower s a d) ≤ ∑ j ∈ t, m j
    rw [countCentresMeeting_eq_inter_cosupp h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent K
      (s.stage a).2 (tailTower s a d) hT]
    refine (ResolutionInvariantSegments.countCentresMeeting_mono hcover _).trans
      ((ResolutionInvariantSegments.countCentresMeeting_biUnion_le t L _).trans (Finset.sum_le_sum fun j hj => ?_))
    show countCentresMeeting (L j) ((s.tail a).stage d).2 ≤ m j
    rw [← (s.tail a).count_restrict (W j) (hLW j hj) d]
    exact hm j hj d

end Bound

end

end Hironaka.ResolutionInvariantSeq.GrowingSeq
