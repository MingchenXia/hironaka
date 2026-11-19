import Hironaka.Invariant.CompanionOpen
import Hironaka.MarkedIdeal.CodimOneCentreAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Where the nonmonomial part has order zero, the marked ideal is monomial

Hironaka phase H2 (TN3), for the case `o = 0` of TN-CLASSICAL's general step (`hir:general-step`: "If `o = 0` the marked
ideal is monomial near `x`"); claim I-0977 C-0159.  Blueprint `bcalc:nonmonomial-order-zero` (chapter
`blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (the monomial
case, Step 2b, is entered where the nonmonomial part `𝓝(𝓘)` is trivial); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.A.

`𝔞|_N = 𝓜_N(𝔞) 𝓝_N(𝔞)` (`MonomialPartAlong`).  At a point `y ∈ N` where `ord_y(𝓝_N(𝔞)|_N) = 0`, some germ `c` of the
quotient `𝓝_N(𝔞) = (Res_N 𝔞 : 𝓜_N(𝔞))` does not vanish at `y`, and every germ `g` of `𝓜_N(𝔞)` satisfies
`g c ∈ Res_N 𝔞`, hence `g ∈ Res_N 𝔞` near `y`.  The points of `N` where the order is positive form a closed set
(`CompanionOpen.isClosed_cosupport_nonmonomialPartAlong`), so its complement `W` is an open neighbourhood of every point of
order zero, and on `W` the marked ideal is monomial along `N ∩ W` (`MonomialPartAlong.IsMonomialAlong`, the hypothesis of
the monomial case along `N`: `MonomialCaseAlong`, `MonomialStepAlong`).

## Main results

* `restrictLe_monomialPartAlong_of_notMem`: at `y ∈ N` with `ord_y(𝓝_N(𝔞)|_N) = 0`, `Res_N 𝓜_N(𝔞) ⊆ Res_N 𝔞` at `y`;
* **`isMonomialAlong_pullback_val`**: if `ord(𝓝_N(𝔞)|_N) = 0` at the points of `N ∩ W`, `𝔪|_W` is monomial along `N ∩ W`;
* `isOpen_compl_cosupport_one`: `W = (cosupp(𝓝_N(𝔞)|_N, 1))ᶜ` is open.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialOrderZero

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.MonomialPartEtale Hironaka.GermIdealOrder
  Hironaka.DivisorExponentAlong Hironaka.BlowupTowers
  Hironaka.DerivativeIdealAlongEtale Hironaka.RestrictedIdealWeight
  Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient
  Hironaka.RestrictedIdealExtension

noncomputable section

variable {n : ℕ}

section Point

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- **At a point of order zero of the nonmonomial part the ideal is monomial**: if `y ∈ N` and
`ord_y(𝓝_N(𝔞)|_N) = 0` (`y ∉ cosupp(𝓝_N(𝔞)|_N, 1)`), every germ of `𝓜_N(𝔞)` at `y` lies in `Res_N 𝔞` near `y`: a germ
`c ∈ 𝓝_N(𝔞)_y` with `c(y) ≠ 0` gives `g c ∈ Res_N 𝔞` for `g ∈ 𝓜_N(𝔞)_y`, and `c` is cancelled. -/
theorem restrictLe_monomialPartAlong_of_notMem {y : M} (hyN : y ∈ N)
    (hy : y ∉ cosupport n N (nonmonomialPartAlong n N 𝔞 E) 1) {g : M → ℂ}
    (hg : (monomialPartAlong n N 𝔞 E).mem y g) : IsInSpanOnAt (n := n) N (𝔞.mem y) y g := by
  have hnot : ¬ OrderGE n N (nonmonomialPartAlong n N 𝔞 E) y 1 := fun h => hy ⟨hyN, h⟩
  unfold OrderGE at hnot
  push Not at hnot
  obtain ⟨c, hc, hcv⟩ := hnot
  have hchol : HolomorphicAt n c y := hc.1
  have hcy : c y ≠ 0 := fun h0 => hcv ((vanishesToOrderOn_one_iff hyN hchol).mpr h0)
  have hgc : (restrictOn n N 𝔞).mem y (fun z => g z * c z) := hc.2 g hg
  exact RelativePrincipalizationSpan.IsInSpanOnAt.cancel_right_of_holomorphicAt_ne_zero hchol hcy hgc.2

end Point

section Open

open ResolutionInvariantSpec (IsInvDomain)

variable {X : CMfd.{u} n}

/-- **The points of positive order of the nonmonomial part form a closed set**, so its complement is an open
neighbourhood of every point of `N` where the order is `0` (and of every point off `N`). -/
theorem isOpen_compl_cosupport_one (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) :
    IsOpen (cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) 1)ᶜ :=
  (CompanionOpen.isClosed_cosupport_nonmonomialPartAlong hn h𝔪 hne 1).isOpen_compl

/-- **Where the nonmonomial part has order zero the marked ideal is monomial** (`hir:general-step`, case `o = 0`): for `𝔪`
with a coherent ideal and an open `W` on which `ord(𝓝_N(𝔞)|_N) = 0` at the points of `N`, the
restriction `𝔪|_W` is monomial along `N ∩ W`: `Res_{N ∩ W} 𝓜_{N ∩ W}(𝔞|_W) ⊆ Res_{N ∩ W} 𝔞|_W`. -/
theorem isMonomialAlong_pullback_val {𝔪 : MarkedIdeal n X} (h𝔞 : 𝔪.ideal.IsCoherent) (W : Opens X)
    (hW : ∀ y ∈ W, y ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) 1) :
    IsMonomialAlong n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).N
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → X) 𝔪).E := by
  have hloc : ∀ y : W, ∃ ψ : X → W, IsLocalInverseAt n (Subtype.val : W → X) ψ y :=
    fun y => ⟨openInv W y, isLocalInverseAt_val W y⟩
  have hle : RestrictLe (𝔪.N ∩ (W : Set X)) (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) 𝔪.ideal :=
    fun y hy g hg => CodimOneCentreAlong.isInSpanOnAt_subset inter_subset_left
      (restrictLe_monomialPartAlong_of_notMem hy.1 (hW y hy.2) hg)
  have h1 := RestrictLeCalculus.restrictLe_pullback (f := (Subtype.val : W → X)) contMDiff_subtype_val
    (V := 𝔪.N ∩ (W : Set X)) (W := (Subtype.val : W → X) ⁻¹' 𝔪.N) (fun y hy => ⟨hy, y.2⟩) h𝔞 hle
  unfold IsMonomialAlong
  show RestrictLe ((Subtype.val : W → X) ⁻¹' 𝔪.N)
    (monomialPartAlong n ((Subtype.val : W → X) ⁻¹' 𝔪.N) (GermIdeal.pullback (m := n) (Subtype.val : W → X) 𝔪.ideal)
      (𝔪.E.map ((Subtype.val : W → X) ⁻¹' ·))) (GermIdeal.pullback (m := n) (Subtype.val : W → X) 𝔪.ideal)
  rw [← pullback_monomialPartAlong hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)]
  exact h1

/-- **The monomial branch on the canonical open set**: with `W = (cosupp(𝓝_N(𝔞)|_N, 1))ᶜ`, the restriction of `𝔪` to `W`
is monomial along `N ∩ W`, and `W` contains every point of `N` where `ord(𝓝_N(𝔞)|_N) = 0`. -/
theorem isMonomialAlong_pullback_val_compl (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) :
    IsMonomialAlong n
      (MarkedIdeal.pullback (Subtype.val : (⟨_, isOpen_compl_cosupport_one hn h𝔪 hne⟩ : Opens X) → X) 𝔪).N
      (MarkedIdeal.pullback (Subtype.val : (⟨_, isOpen_compl_cosupport_one hn h𝔪 hne⟩ : Opens X) → X) 𝔪).ideal
      (MarkedIdeal.pullback (Subtype.val : (⟨_, isOpen_compl_cosupport_one hn h𝔪 hne⟩ : Opens X) → X) 𝔪).E :=
  isMonomialAlong_pullback_val h𝔪.isCoherent _ fun _ hy => hy

end Open

end

end Hironaka.NonmonomialOrderZero
