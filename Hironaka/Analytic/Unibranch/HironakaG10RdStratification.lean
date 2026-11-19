import Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
import Hironaka.Analytic.Unibranch.HironakaG10RdFinish

/-!
# The stratification contract from Frisch's two theorems (lane G10RD)

Plan item G10-03-05.a (research report `work/hironaka-run0081-20261117/G10RD/G10-03-05a-stratification-contract.md`):
the inputs `hA` (analytic strata), `hproper` (no nonempty stratum equals its own relative non-flat set) and
`hdense` (dense flat locus) used by the library's `D_β` construction and by `HironakaG10RdTopIndex` all follow from
two statements about ONE proper family `f`, faithful to J. Frisch, *Points de platitude d'un morphisme d'espaces
analytiques complexes*, Invent. Math. 4 (1967): Théorème (IV,9) (p. 133: the non-flat locus is analytic) together
with Remmert's proper mapping theorem, and Proposition (IV,14) (p. 135: over a reduced base the image of the
non-flat locus is negligible).  Here they are explicit hypotheses of the lemmas (no named `Prop` is introduced):

* `hF1 : ∀ A, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A)`;
* `hF2 : ∀ A, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A)`.

Consequences: `strata_analytic`, `strata_succ_ne`, `dense_compl_nonflatImage`, `exists_topIndex_bound_of_frisch`,
`subset_closure_diff_cset` (the nowhere density of `C_i` in `B` consumed by the dimension drop D1).
-/

set_option autoImplicit false

open Set

namespace Hironaka.Analytic.Unibranch.HironakaG10RdStratification

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
  Hironaka.Analytic.Unibranch.HironakaG10RdFinish

variable {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)

/-- **All strata are analytic** (Frisch (IV,9) + Remmert, iterated). -/
theorem strata_analytic
    (hF1 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A))
    {B : Set X.obj.left} (hB : X.IsAnalyticSubset B) : ∀ j, X.IsAnalyticSubset (strata f B j)
  | 0 => hB
  | j + 1 => hF1 _ (strata_analytic hF1 hB j)

/-- **No nonempty stratum equals its own relative non-flat set** (Frisch (IV,14)). -/
theorem strata_succ_ne
    (hF1 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A))
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A))
    {B : Set X.obj.left} (hB : X.IsAnalyticSubset B) :
    ∀ n, (strata f B n).Nonempty → strata f B (n + 1) ≠ strata f B n := by
  intro n ⟨x, hx⟩ heq
  have h := hF2 _ (strata_analytic f hF1 hB n) hx
  have hempty : strata f B n \ relNonflat f (strata f B n) = ∅ := by
    change strata f B n \ strata f B (n + 1) = ∅
    rw [heq, sdiff_self]
  rw [hempty, closure_empty] at h
  exact h

/-- **The flat locus is dense** (Frisch (IV,14) over the whole base). -/
theorem dense_compl_nonflatImage
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A)) :
    Dense (nonflatImage f)ᶜ := by
  intro x
  have h := hF2 univ (X.isAnalyticSubset_univ) (mem_univ x)
  rwa [relNonflat_univ_eq_nonflatImage, ← compl_eq_univ_sdiff] at h

/-- **Hironaka's index exists** for every finite family of tracked sets, from Frisch's theorems. -/
theorem exists_topIndex_bound_of_frisch [CompactSpace X.obj.left]
    (hF1 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A))
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A))
    {B : Set X.obj.left} (hB : X.IsAnalyticSubset B) {q : ℕ} (Z : Fin q → Set X.obj.left) :
    ∃ i, ∀ jC ∈ badComponents f B Z, jC.1 ≤ i :=
  exists_topIndex_bound (strata_analytic f hF1 hB) (strata_succ_ne f hF1 hF2 hB)

/-- **`C_i` is nowhere dense in `B`** (the hypothesis of the dimension drop D1; Hironaka p. 544,
"dim C_i < n"): `C_i ⊆ s_1(f/B)` and Frisch (IV,14). -/
theorem subset_closure_diff_cset
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A))
    {B : Set X.obj.left} (hB : X.IsAnalyticSubset B) {q : ℕ} (Z : Fin q → Set X.obj.left) (i : ℕ) :
    B ⊆ closure (B \ Cset f B Z i) :=
  (hF2 B hB).trans (closure_mono (sdiff_subset_sdiff_right (cset_subset_relNonflat i)))

end Hironaka.Analytic.Unibranch.HironakaG10RdStratification
