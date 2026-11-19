import Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
import Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
import Hironaka.Resolution.HironakaG10HirIdealGerms

/-!
# P2 — local flatteners, the ONE local input, and closedness of the non-flat image

Lane G10H, run 0080, round 3 (plan P2 of `work/hironaka-resume-20261111/G10H/PSEUDOFREE-ROUTE.md` §4).
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975),
Th. 2.4 (pp. 526–529), Rem. 2.4.4 (p. 529), Def. 4.4.2 (3) (p. 537).

* `LocalFlattener f` — Hironaka's `(V, Z = V(H))`: an open `V` of the base and an ideal family `H`,
  coherent (locally finitely generated) on `V`, which is the whole-fibre flattener
  (`IsGermFlattenerAt`) at every point of its support `|Z| = {x ∈ V | H x ≠ ⊤}`.
* `LocalFlattener.H_eq_of_mem`, `LocalFlattener.eventually_eq` — Rem. 2.4.4 (two local flatteners
  agree near every common support point); `eventually_eq_bot`; `isOpen_inter_eq_top` (`|Z|` is closed
  in `V`); `restrict`.
* **The named input** `PersistentLocalFlattener` (a `def … : Prop`, used only as an explicit
  hypothesis; NOT an axiom).
* `isOpen_flatOverAt_bot`, `isClosed_nonflatImage_of_persistent`, `machine_hclosed`: the input
  implies the closedness of non-flat images, i.e. the hypothesis `hclosed` of
  `HironakaG10ChowCentreMachine.exists_flattening_of_machine'`, for every centre machine.

## The named input and why it is true

`PersistentLocalFlattener`: for every proper morphism `f : Y ⟶ X` of reduced complex spaces and every
`x ∈ X` there is a local flattener whose support contains `x`.

* **Source.** Hironaka Th. 2.4 (p. 526) with `S = {x}` the reduced point (the hypothesis "`F|f⁻¹(S)` flat
  over `S`" holds for any family over a reduced point): it gives an open `V ∋ x` and a closed subspace
  `Z = V(H) ⊆ V` with (2.4.1) `x ∈ Z` and (2.4.2) for every connected `g : Z' → V` meeting `Z`, the pulled
  family is flat iff `g` factors through `Z`.  The same statement is Frisch 1968, Lemme 5 (the local
  flattener, *Invent. Math.* 4, p. 129), and it is literally the project leaf `G10.FLAT.07` ("ONE coherent
  closed flat piece near `y` with all-nearby-point universal factorization property for actual proper
  family").
* **Germ form at every support point.** For `x' ∈ Z` and a germ `V(J)` at `x'`: if `H_{x'} ≤ J`, then
  `V(J) ⊆ Z` and the family is flat over `Z` (apply (2.4.2) to `Z ↪ V`), hence over `V(J)` (base change);
  conversely, if the family is flat over `V(J)` at every point of the (compact) fibre, flatness holds on a
  neighbourhood of the fibre (openness of flatness, Frisch Th. (IV.9)) and by properness over a small
  connected representative `Z'` of `V(J)` (analytic germs have connected small representatives), which
  meets `Z` at `x'`; (2.4.2) gives `Z' ⊆ Z`, i.e. `H_{x'} ≤ J`.  So `H_{x'}` is the whole-fibre flattener
  `IsGermFlattenerAt f x' (H x')`.  Off `Z` (where `H = ⊤`) nothing is required — correctly: e.g. for the
  inclusion of a point `{0} → ℂ` the flattener near `0` is `V(𝔪_0)`, while the family is flat over every
  `y ≠ 0`.
* **Degenerate cases.** `x` outside `f(Y)`: `V = X ∖ f(Y)` (open, `f` proper), `H = ⊥`; empty `Y`: likewise.
  Zero-dimensional or nonreduced fibres are covered by Th. 2.4 (no reducedness of `Y` over `X` is used).
* **Not a restatement of its consumers.** The consumers need Th. 2.4 for compact `S` (gluing, P3), the
  transport under permissible blowups (Lemma 4.4.5, P4), Theorems `I_n`/`II_n` and `hclosed`; the last is
  DERIVED here, the others are derived in P3/P4 and the skeleton.  The reverse implication
  (`hclosed` ⇒ input) fails: closedness of non-flat images says nothing about the flattener near a
  non-flat point.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

open Hironaka HironakaG10HirIdealGerms
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds

noncomputable section

/-- **A local flattener** `(V, Z = V(H))` of `f` (Hironaka Def. 4.4.2 (3), condition (*), p. 537;
Th. 2.4, p. 526): an ideal family coherent on an open `V` which is the whole-fibre flattener at every
point of its support. -/
structure LocalFlattener {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) where
  /-- the open set of the base on which the flattener lives -/
  V : Set X.obj.left
  isOpen : IsOpen V
  /-- the ideal family of `Z` (meaningful on `V`) -/
  H : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)
  fg : IsLocallyFinitelyGeneratedOn X.obj.left V H
  flattener : ∀ x ∈ V, H x ≠ ⊤ → IsGermFlattenerAt f x (H x)

namespace LocalFlattener

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}

/-- The support `|Z| ⊆ V`. -/
def support (Z : LocalFlattener f) : Set X.obj.left := {x | x ∈ Z.V ∧ Z.H x ≠ ⊤}

theorem mem_support {Z : LocalFlattener f} {x : X.obj.left} :
    x ∈ Z.support ↔ x ∈ Z.V ∧ Z.H x ≠ ⊤ :=
  Iff.rfl

/-- On its support a local flattener is THE whole-fibre flattener. -/
theorem H_eq_germFlattener (Z : LocalFlattener f) {x : X.obj.left} (hx : x ∈ Z.support) :
    Z.H x = germFlattener f x :=
  eq_germFlattener f x (Z.H x) (Z.flattener x hx.1 hx.2)

/-- Two local flatteners agree at every common support point (Rem. 2.4.4, pointwise). -/
theorem H_eq_of_mem (Z Z' : LocalFlattener f) {x : X.obj.left} (hx : x ∈ Z.support)
    (hx' : x ∈ Z'.support) : Z.H x = Z'.H x :=
  isGermFlattenerAt_unique (Z.flattener x hx.1 hx.2) (Z'.flattener x hx'.1 hx'.2)

/-- **Rem. 2.4.4** ("unique up to its germ"): two local flatteners agree on a neighbourhood of every
common support point. -/
theorem eventually_eq (Z Z' : LocalFlattener f) {x : X.obj.left} (hx : x ∈ Z.support)
    (hx' : x ∈ Z'.support) : ∀ᶠ y in 𝓝 x, Z.H y = Z'.H y :=
  eventually_eq_of_eq Z.fg Z'.fg Z.isOpen Z'.isOpen hx.1 hx'.1 (H_eq_of_mem Z Z' hx hx')

/-- A local flattener with zero germ at `x` vanishes near `x`. -/
theorem eventually_eq_bot (Z : LocalFlattener f) {x : X.obj.left} (hx : x ∈ Z.V) (h : Z.H x = ⊥) :
    ∀ᶠ y in 𝓝 x, Z.H y = ⊥ :=
  HironakaG10HirIdealGerms.eventually_eq_bot Z.fg Z.isOpen hx h

/-- The support is closed in `V`. -/
theorem isOpen_inter_eq_top (Z : LocalFlattener f) : IsOpen (Z.V ∩ {x | Z.H x = ⊤}) :=
  HironakaG10HirIdealGerms.isOpen_inter_eq_top Z.fg Z.isOpen

/-- Restriction of a local flattener to a smaller open set. -/
def restrict (Z : LocalFlattener f) (W : Set X.obj.left) (hW : IsOpen W) : LocalFlattener f where
  V := Z.V ∩ W
  isOpen := Z.isOpen.inter hW
  H := Z.H
  fg := Z.fg.mono inter_subset_left
  flattener x hx hne := Z.flattener x hx.1 hne

@[simp] theorem restrict_V (Z : LocalFlattener f) (W : Set X.obj.left) (hW : IsOpen W) :
    (Z.restrict W hW).V = Z.V ∩ W :=
  rfl

@[simp] theorem restrict_H (Z : LocalFlattener f) (W : Set X.obj.left) (hW : IsOpen W) :
    (Z.restrict W hW).H = Z.H :=
  rfl

end LocalFlattener

/-- **The ONE local input** (named, NOT an axiom; see the module docstring for source and truth):
Hironaka Th. 2.4 with `S = {x}` (p. 526) = Frisch 1968 Lemme 5 = leaf `G10.FLAT.07`.  For every proper
morphism of reduced complex spaces and every point `x` of the base there is a local flattener whose
support contains `x`. -/
def PersistentLocalFlattener : Prop :=
  ∀ (X Y : SourceReducedComplexSpace) (f : Y ⟶ X), IsProperMap f.hom.left.base →
    ∀ x : X.obj.left, ∃ Z : LocalFlattener f, x ∈ Z.support

/-- **Openness of the flat locus over the base**, from the local input. -/
theorem isOpen_flatOverAt_bot (hP : PersistentLocalFlattener) {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) :
    IsOpen {x : X.obj.left | FlatOverAt f x ⊥} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨Z, hZV, hZtop⟩ := hP X Y f hf x
  have hbot : Z.H x = ⊥ :=
    isGermFlattenerAt_unique (Z.flattener x hZV hZtop) (isGermFlattenerAt_bot_iff.2 hx)
  filter_upwards [Z.eventually_eq_bot hZV hbot, Z.isOpen.mem_nhds hZV] with y hy hyV
  have hne : Z.H y ≠ ⊤ := by
    rw [hy]
    exact bot_ne_top
  have h := Z.flattener y hyV hne
  rw [hy] at h
  exact isGermFlattenerAt_bot_iff.1 h

/-- **`hclosed` from the local input**: the non-flat image of a proper morphism is closed. -/
theorem isClosed_nonflatImage_of_persistent (hP : PersistentLocalFlattener)
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) :
    IsClosed (nonflatImage f) := by
  have hc : (nonflatImage f)ᶜ = {x : X.obj.left | FlatOverAt f x ⊥} := by
    ext x
    rw [mem_compl_iff, mem_ofPred_eq, flatOverAt_bot_iff_not_mem_nonflatImage]
  rw [← isOpen_compl_iff, hc]
  exact isOpen_flatOverAt_bot hP f hf

/-- **`hclosed` for every centre machine** (the hypothesis of
`HironakaG10ChowCentreMachine.exists_flattening_of_machine'`). -/
theorem machine_hclosed (hP : PersistentLocalFlattener) (M : CentreMachine) (s₀ : Stage)
    (d₀ : M.St s₀) (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ) :
    IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n) :=
  isClosed_nonflatImage_of_persistent hP _ (run_proper M s₀ d₀ hf n)

end

end Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
