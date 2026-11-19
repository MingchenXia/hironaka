/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The meet loci and the disjoining centers: lattice facts

`meetLocus G m` is the closed set of points on at least `m` members of the finite family `G`
(Kollár's "subset where `m` of the `E_i` intersect" [Kol07, 72]), a finite union of finite
intersections of supports; `disjoinCenter G m = ∏_{|s| = m} ∑_{i ∈ s} G_i` is the ideal sheaf of
that union with the natural scheme structure on each `m`-fold intersection. This module proves the
lattice-level facts about them, which need no smoothness or snc hypothesis:

* membership in the meet locus (`mem_meetLocus_iff`) and its antitonicity in `m`;
* `DivisorFamily.singularLocus`, the locus where two components meet, is the meet locus at
  multiplicity `2` (`sing_eq_meetLocus_two`);
* the support of the center is the meet locus (`support_disjoinCenter`): the support of a product
  is the union of the supports (`support_finset_prod`,
  `Hironaka/Resolution/Algebraic/Snc/DictionaryBoundary.lean`), the support of a sum the
  intersection;
* the loci and the centers commute with inverse images along any morphism
  (`meetLocus_comap`, `disjoinCenter_comap`): the inverse image ideal sheaf is multiplicative and
  commutes with sums (`comap_finset_prod`, `Hironaka/Resolution/Algebraic/Tuning/Transform.lean`),
  and supports pull back to preimages; this is the content of Kollár's remark that the `Z_t` are
  defined from `E` alone, on which the functoriality of the construction rests;
* the disjoining sequence has `k − 1` steps (`length_disjoinSeq`).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme IdealSheafData Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {X Y : Scheme.{u}}

section Closeds

variable {α : Type*} [TopologicalSpace α] {σ : Type*}

/-- A point lies in a finite supremum of closed sets iff it lies in one of them. -/
theorem _root_.TopologicalSpace.Closeds.mem_finset_sup {f : σ → Closeds α} {s : Finset σ} {x : α} :
    x ∈ s.sup f ↔ ∃ i ∈ s, x ∈ f i := by
  rw [← SetLike.mem_coe, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂]
  simp only [Function.comp_apply, SetLike.mem_coe, exists_prop]

/-- A point lies in a supremum of closed sets indexed by a finite set iff it lies in one of them. -/
theorem _root_.TopologicalSpace.Closeds.mem_biSup_finset {f : σ → Closeds α} {s : Finset σ}
    {x : α} : x ∈ (⨆ i ∈ s, f i) ↔ ∃ i ∈ s, x ∈ f i := by
  rw [← Finset.sup_eq_iSup]
  exact Closeds.mem_finset_sup

end Closeds

section MeetLocus

variable {ι : Type*} [Fintype ι]

/-- `x` lies in the meet locus at multiplicity `m` iff it lies on at least `m` members of `G`. -/
theorem mem_meetLocus_iff (G : ι → X.IdealSheafData) (m : ℕ) (x : X) :
    x ∈ meetLocus G m ↔ ∃ s : Finset ι, s.card = m ∧ ∀ i ∈ s, x ∈ (G i).support := by
  unfold meetLocus
  rw [Closeds.mem_biSup_finset]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, (Finset.mem_powersetCard.mp hs).2, fun i hi => ?_⟩
    simpa using Closeds.mem_iInf.mp (Closeds.mem_iInf.mp hx i) hi
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs⟩, ?_⟩
    exact Closeds.mem_iInf.mpr fun i => Closeds.mem_iInf.mpr fun hi => hx i hi

/-- Fewer members meet at higher multiplicity. -/
theorem meetLocus_antitone (G : ι → X.IdealSheafData) : Antitone (meetLocus G) := by
  intro m m' hmm' x hx
  rw [mem_meetLocus_iff] at hx ⊢
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (s := s) (n := m) (hs ▸ hmm')
  exact ⟨t, ht, fun i hi => hx i (hts hi)⟩

/-- The meet locus at multiplicity `0` is everything. -/
theorem meetLocus_zero (G : ι → X.IdealSheafData) : meetLocus G 0 = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  rw [mem_meetLocus_iff]
  exact ⟨∅, Finset.card_empty, fun i hi => absurd hi (Finset.notMem_empty i)⟩

/-- The meet locus is empty at a multiplicity exceeding the number of members. -/
theorem meetLocus_eq_bot_of_card_lt (G : ι → X.IdealSheafData) {m : ℕ} (hm : Fintype.card ι < m) :
    meetLocus G m = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  rw [mem_meetLocus_iff] at hx
  obtain ⟨s, hs, -⟩ := hx
  exact absurd (hs ▸ Finset.card_le_univ s) (not_le.mpr hm)

/-- The locus `DivisorFamily.singularLocus` where two components meet is the meet locus at
multiplicity `2`; the components are disjoint iff it is empty [Kol07, 72]. -/
theorem sing_eq_meetLocus_two (E : DivisorFamily X) : E.singularLocus = meetLocus E.component 2 :=
    by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    unfold meetLocus
    refine le_iSup₂_of_le ({i, j} : Finset E.ι)
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hij⟩) ?_
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  · unfold meetLocus
    refine iSup₂_le fun s hs => ?_
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    rw [Finset.iInf_insert, Finset.iInf_singleton]
    exact le_iSup₂_of_le i j (le_iSup_of_le hij le_rfl)

/-- The center of a disjoining step is supported on Kollár's subset `Z_t` [Kol07, 72]. -/
theorem support_disjoinCenter (G : ι → X.IdealSheafData) (m : ℕ) :
    (disjoinCenter G m).support = meetLocus G m := by
  unfold disjoinCenter meetLocus
  rw [support_finset_prod]
  simp only [support_iSup]

/-- The meet loci commute with inverse images along any morphism: the loci `Z_t` are defined from
`E` alone [Kol07, 72]. -/
theorem meetLocus_comap (h : Y ⟶ X) (G : ι → X.IdealSheafData) (m : ℕ) :
    meetLocus (fun i => (G i).comap h) m = (meetLocus G m).preimage h.continuous := by
  ext x
  rw [SetLike.mem_coe, mem_meetLocus_iff, Closeds.coe_preimage, Set.mem_preimage,
    SetLike.mem_coe, mem_meetLocus_iff]
  simp only [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage]

/-- The disjoining centers commute with inverse images along any morphism [Kol07, 72]. -/
theorem disjoinCenter_comap (h : Y ⟶ X) (G : ι → X.IdealSheafData) (m : ℕ) :
    disjoinCenter (fun i => (G i).comap h) m = (disjoinCenter G m).comap h := by
  unfold disjoinCenter
  rw [comap_finset_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [comap_iSup]

/-- The disjoining steps: unfolding lemmas. -/
@[simp] theorem disjoinSeqAux_zero (G : ι → X.IdealSheafData) :
    disjoinSeqAux 0 G = BlowUpSequence.nil X := rfl

@[simp] theorem disjoinSeqAux_one (G : ι → X.IdealSheafData) :
    disjoinSeqAux 1 G = BlowUpSequence.nil X := rfl

theorem disjoinSeqAux_succ_succ (m : ℕ) (G : ι → X.IdealSheafData) :
    disjoinSeqAux (m + 2) G = BlowUpSequence.cons X (disjoinCenter G (m + 2))
      (disjoinSeqAux (m + 1) fun i => (G i).strictTransform (disjoinCenter G (m + 2))) := rfl

/-- The steps at multiplicities `m, …, 2` number `m − 1`. -/
theorem length_disjoinSeqAux : ∀ (m : ℕ) {X : Scheme.{u}} (G : ι → X.IdealSheafData),
    (disjoinSeqAux m G).length = m - 1
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | m + 2, X, G => by
    rw [disjoinSeqAux_succ_succ]
    change (disjoinSeqAux (m + 1) _).length + 1 = _
    rw [length_disjoinSeqAux (m + 1)]
    omega

/-- "We make the `E_i` disjoint in `k − 1` steps" [Kol07, 72]. -/
theorem length_disjoinSeq (E : DivisorFamily X) :
    (disjoinSeq E).length = Fintype.card E.ι - 1 :=
  length_disjoinSeqAux _ _

end MeetLocus

end Hironaka.Sequence
