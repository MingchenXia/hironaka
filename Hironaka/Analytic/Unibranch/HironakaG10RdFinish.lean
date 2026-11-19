import Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz
import Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
import Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat

/-!
# The end of a round: open tracked supports carry no non-flat point (lane G10RD)

Plan items G10-03-16.a and (part of) G10-03-04.b (sub-ids of
`work/hironaka-run0081-20261117/G10RD/G10-03-01-double-induction-contract.md` §4, §6).  Source: H. Hironaka,
*Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of Lemma 4.6.1,
printed p. 545: "B^{(1)} ∩ Z_r^{(1)} is open and (F^{(1)}, f^{(1)})/Z_r^{(1)} is flat. Hence
s_1(F^{(1)}, f^{(1)}/B^{(1)}) ∩ Z_r^{(1)} = ∅", read with `B = X` (the base of the outer run).

* `vanishingIdealAt_univ_eq_bot` — on a reduced complex space no nonzero germ vanishes pointwise near its
  point (the native Nullstellensatz with the zero ideal family and the reducedness of the stalks);
* `relNonflat_univ_eq_nonflatImage` — the relative non-flat set over the whole base is the non-flat
  image, so Hironaka's `s_1(F, f/B)` with `B = X` is the `nonflatImage` of `RoundData`;
* `nonflatImage_inter_support_eq_empty_of_isOpen` — **the `finish` field from the conclusion of
  Theorem `I_n` with `B = X`**: an actual local flattener whose support is open carries no non-flat
  point; `nonflatImage_inter_iUnion_support_eq_empty` for a finite family.

No named input is introduced.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RdFinish

open Hironaka HironakaG10HirIdealGerms HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity
  Hironaka.Analytic.Unibranch.HironakaG10NativeNullstellensatz

noncomputable section

/-- **No nonzero germ vanishes pointwise near its point** on a reduced complex space. -/
theorem vanishingIdealAt_univ_eq_bot (X : SourceReducedComplexSpace) (x : X.obj.left) :
    vanishingIdealAt X.obj.left univ x = ⊥ := by
  have : IsReduced (X.obj.left.presheaf.stalk x).carrier := X.isReduced_stalk x
  rw [vanishingIdealAt_eq_intrinsicCentreStalkRange]
  have hle := intrinsicCentre_le_radical_of_support_subset (X := X) univ univ isOpen_univ
    (fun _ => ⊥) (isLocallyFinitelyGeneratedOn_bot (X := X.obj.left) univ) x (mem_univ x)
    (Eventually.of_forall fun y _ => mem_univ y)
  refine le_bot_iff.mp (hle.trans fun r hr => ?_)
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff (I := (⊥ : Ideal (X.obj.left.presheaf.stalk x)))).mp hr
  exact (Ideal.mem_bot.mpr (IsNilpotent.eq_zero ⟨n, Ideal.mem_bot.mp hn⟩))

variable {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)

/-- **`s_1(f/X)` is the non-flat image.** -/
theorem relNonflat_univ_eq_nonflatImage : relNonflat f univ = nonflatImage f := by
  ext x
  simp only [relNonflat, Set.mem_ofPred_eq, mem_univ, true_and]
  rw [vanishingIdealAt_univ_eq_bot X x]
  exact not_congr flatOverAt_bot_iff_not_mem_nonflatImage |>.trans not_not

/-- **The end of a round** (Hironaka p. 545, `B = X`): if the support of an actual local flattener is
open, none of its points is in the non-flat image. -/
theorem nonflatImage_inter_support_eq_empty_of_isOpen (Z : LocalFlattener f)
    (hZ : IsOpen Z.support) : nonflatImage f ∩ Z.support = ∅ := by
  have hrel : IsRelOpen (univ : Set X.obj.left) Z.support := ⟨Z.support, hZ, by simp⟩
  rw [← relNonflat_univ_eq_nonflatImage]
  exact relNonflat_disjoint_support_of_relOpen f Z univ hrel

/-- The same for the tracked set of a finite family. -/
theorem nonflatImage_inter_iUnion_support_eq_empty {q : ℕ} (Z : Fin q → LocalFlattener f)
    (hZ : ∀ p, IsOpen (Z p).support) : nonflatImage f ∩ ⋃ p, (Z p).support = ∅ := by
  rw [Set.inter_iUnion, Set.iUnion_eq_empty]
  exact fun p => nonflatImage_inter_support_eq_empty_of_isOpen f (Z p) (hZ p)

/-! ### The start of a round: the strata cover the relative non-flat set -/

/-- Once the flatness filtration reaches the empty set, `s_1(f/B)` is the union of the differences of
consecutive strata `s_r ∖ s_{r+1}`, `1 ≤ r < N` (Hironaka p. 544, the sets `E_{q+r}`). -/
theorem relNonflat_subset_iUnion_strata_diff (B : Set X.obj.left) (N : ℕ)
    (hN : strata f B N = ∅) :
    relNonflat f B ⊆ ⋃ r ∈ Finset.Ico 1 N, (strata f B r \ strata f B (r + 1)) := by
  classical
  intro x hx
  have hex : ∃ r, x ∉ strata f B r := ⟨N, by rw [hN]; exact notMem_empty x⟩
  have hB : x ∈ strata f B 0 := hx.1
  have h1 : x ∈ strata f B 1 := hx
  have hne0 : Nat.find hex ≠ 0 := fun h => (h ▸ Nat.find_spec hex) hB
  have hne1 : Nat.find hex ≠ 1 := fun h => (h ▸ Nat.find_spec hex) h1
  have hle : Nat.find hex ≤ N := Nat.find_min' hex (by rw [hN]; exact notMem_empty x)
  have hprev : x ∈ strata f B (Nat.find hex - 1) := by
    by_contra h
    exact Nat.find_min hex (by omega) h
  simp only [mem_iUnion, Finset.mem_Ico]
  refine ⟨Nat.find hex - 1, ⟨by omega, by omega⟩, hprev, ?_⟩
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
  exact Nat.find_spec hex

/-- **The start of a round** (Hironaka p. 544, `B = Y`): if every difference of consecutive strata of
`f` over the whole base lies in the support of one of finitely many actual local flatteners, these cover
the non-flat image. -/
theorem nonflatImage_subset_of_strata_cover (N : ℕ) (hN : strata f univ N = ∅) {m : ℕ}
    (Z : Fin m → LocalFlattener f)
    (hZ : ∀ r, 1 ≤ r → r < N → ∃ p, strata f univ r \ strata f univ (r + 1) ⊆ (Z p).support) :
    nonflatImage f ⊆ ⋃ p, (Z p).support := by
  rw [← relNonflat_univ_eq_nonflatImage]
  intro x hx
  obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp (relNonflat_subset_iUnion_strata_diff f univ N hN hx)
  obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
  obtain ⟨p, hp⟩ := hZ r hr1 hr2
  exact mem_iUnion.mpr ⟨p, hp hxr⟩

/-- Relative openness in the whole base is openness. -/
theorem isOpen_of_isRelOpen_univ {α : Type*} [TopologicalSpace α] {T : Set α}
    (h : IsRelOpen (univ : Set α) T) : IsOpen T := by
  obtain ⟨U, hU, hEq⟩ := h
  simp only [univ_inter] at hEq
  exact hEq ▸ hU

end

end Hironaka.Analytic.Unibranch.HironakaG10RdFinish
