import Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat
import Hironaka.Analytic.Unibranch.HironakaG10StratumComponentFiniteness

/-!
# Hironaka's inner induction index `i` and Lemma 4.5.1 at that index (lane G10RD)

Plan items G10-03-05.b and G10-03-05.c (re-split in
`work/hironaka-run0081-20261117/G10RD/G10-03-03-sum-centre-globalization.md` §6).  Source: H. Hironaka,
*Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of `II_{n-1} ⇒ I_n`,
printed pp. 541–544: "Let i be the smallest integer ≥ 0 for which the assumption of (4.5.1) is satisfied.
Such an integer i exists because Δ is a finite set. The proof of the implication will be done by
induction on i."

For an arbitrary finite family of tracked sets (an abstract finite tracked-flattener cover) on a compact
base, under the stratification contract (analytic strata, no nonempty stratum equal to its own relative
non-flat set), this module defines that index from the ACTUAL bad component set
`HironakaG10SourceCSet.badComponents` and reads off what the inner recursion consumes:

* `topIndex`, `le_topIndex`, `topIndex_le`, `topIndex_eq_zero_iff` (`i = 0` iff `Δ = ∅`),
  `exists_badComponent_at_topIndex` (maximality: for `i > 0` some bad component has index `i`);
* `exists_topIndex_bound` — the bound exists under the stratification contract;
* `cset_subset_relNonflat` — `C_i ⊆ s_1(f/B)` (the input of the dimension drop and of permissibility (2)
  of the lower-dimensional run);
* `lemma_4_5_1_at_topIndex` — Hironaka 4.5.1 at `i`: `C_i` is closed analytic, meets every tracked support
  relatively openly, lies in `s_1(f/B)`, and `s_1(f/C_i)` misses every tracked support.

No named input is introduced.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat
  Hironaka.Analytic.Unibranch.HironakaG10StratumComponentFiniteness
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

noncomputable section

attribute [local instance] Classical.propDecidable

variable {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (B : Set X.obj.left)
  {q : ℕ} (Z : Fin q → Set X.obj.left)

/-! ### The index -/

/-- **Hironaka's `i`** (p. 543): the least integer bounding the indices of the actual bad components. -/
def topIndex (h : ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) : ℕ := Nat.find h

variable {f B Z}

theorem le_topIndex (h : ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) :
    ∀ jC ∈ badComponents f B Z, jC.1 ≤ topIndex f B Z h :=
  Nat.find_spec h

theorem topIndex_le (h : ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) {i : ℕ}
    (hi : ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) : topIndex f B Z h ≤ i :=
  Nat.find_min' h hi

/-- Every bad component has positive index, so `i = 0` exactly when `Δ` is empty. -/
theorem topIndex_eq_zero_iff (h : ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) :
    topIndex f B Z h = 0 ↔ badComponents f B Z = ∅ := by
  constructor
  · intro h0
    refine Set.eq_empty_iff_forall_notMem.mpr fun jC hjC => ?_
    have h1 : jC.1 ≤ 0 := h0 ▸ le_topIndex h jC hjC
    have h2 : 1 ≤ jC.1 := hjC.1
    omega
  · intro hempty
    refine Nat.le_zero.mp (topIndex_le h fun jC hjC => ?_)
    rw [hempty] at hjC
    exact absurd hjC (Set.notMem_empty jC)

/-- **Maximality**: for `i > 0` some actual bad component has index exactly `i`. -/
theorem exists_badComponent_at_topIndex (h : ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i)
    (hpos : 0 < topIndex f B Z h) : ∃ C, (topIndex f B Z h, C) ∈ badComponents f B Z := by
  have hnot : ¬ ∀ jC ∈ badComponents f B Z, jC.1 ≤ topIndex f B Z h - 1 := by
    intro hb
    have := topIndex_le h hb
    omega
  push Not at hnot
  obtain ⟨jC, hjC, hlt⟩ := hnot
  have hle := le_topIndex h jC hjC
  have heq : jC.1 = topIndex f B Z h := by omega
  exact ⟨jC.2, heq ▸ hjC⟩

/-- The bound exists under the stratification contract (analytic strata; no nonempty stratum equals its
own relative non-flat set) on a compact base. -/
theorem exists_topIndex_bound [CompactSpace X.obj.left]
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j))
    (hproper : ∀ n, (strata f B n).Nonempty → strata f B (n + 1) ≠ strata f B n) :
    ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i := by
  obtain ⟨_, i, _, _, _, _, hi⟩ := exists_finite_depth_component_data f B Z hA hproper
  exact ⟨i, hi⟩

/-! ### `C_i` -/

/-- The strata decrease. -/
theorem strata_antitone : Antitone (strata f B) :=
  antitone_nat_of_succ_le (strata_succ_subset f B)

/-- **`C_i ⊆ s_1(f/B)`**: every selected component has index `> i ≥ 0`. -/
theorem cset_subset_relNonflat (i : ℕ) : Cset f B Z i ⊆ relNonflat f B := by
  intro x hx
  simp only [Cset, Set.mem_iUnion] at hx
  obtain ⟨jC, hjC, hxC⟩ := hx
  have hj : 1 ≤ jC.1 := Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le i) hjC.1)
  have hmem : x ∈ strata f B jC.1 := hjC.2.1.2.1 hxC
  have h1 : x ∈ strata f B 1 := strata_antitone hj hmem
  exact h1

/-- **Hironaka Lemma 4.5.1 at the inner index** (p. 541), for a finite family of actual local
flatteners on a compact base under the stratification contract: `C_i` is a closed analytic subset of
`s_1(f/B)` meeting every tracked support relatively openly, and `s_1(f/C_i)` misses every tracked
support. -/
theorem lemma_4_5_1_at_topIndex [CompactSpace X.obj.left] (Zf : Fin q → LocalFlattener f)
    (hA : ∀ j, X.IsAnalyticSubset (strata f B j))
    (hproper : ∀ n, (strata f B n).Nonempty → strata f B (n + 1) ≠ strata f B n)
    (h : ∃ i, ∀ jC ∈ badComponents f B (fun p => (Zf p).support), jC.1 ≤ i) :
    X.IsAnalyticSubset (Cset f B (fun p => (Zf p).support)
        (topIndex f B (fun p => (Zf p).support) h)) ∧
      IsClosed (Cset f B (fun p => (Zf p).support) (topIndex f B (fun p => (Zf p).support) h)) ∧
      (∀ p, IsRelOpen (Cset f B (fun p => (Zf p).support)
        (topIndex f B (fun p => (Zf p).support) h)) (Zf p).support) ∧
      Cset f B (fun p => (Zf p).support) (topIndex f B (fun p => (Zf p).support) h) ⊆
        relNonflat f B ∧
      ∀ p, relNonflat f (Cset f B (fun p => (Zf p).support)
        (topIndex f B (fun p => (Zf p).support) h)) ∩ (Zf p).support = ∅ := by
  obtain ⟨N, _, hN, _, _, _, _⟩ :=
    exists_finite_depth_component_data f B (fun p => (Zf p).support) hA hproper
  have hfinite := selectedHigherComponents_finite f B (fun p => (Zf p).support)
    (topIndex f B (fun p => (Zf p).support) h) hA N hN
  obtain ⟨hCa, hCc, hrel, _⟩ := Cset_closed_relOpen_and_nonflat f B (fun p => (Zf p).support)
    (topIndex f B (fun p => (Zf p).support) h) hfinite (le_topIndex h)
  exact ⟨hCa, hCc, hrel, cset_subset_relNonflat _,
    cset_relNonflat_disjoint_tracked f B Zf _ hfinite (le_topIndex h)⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
