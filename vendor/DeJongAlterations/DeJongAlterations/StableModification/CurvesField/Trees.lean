import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

/-!
# Exceptional `ℙ¹`-trees and the stable blow-down (combinatorial core)

This file formalizes the combinatorial part of Appendix B of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`,
`semi-stable.tex`, lines 4428–4486): `ℙ¹_k`-trees, exceptional trees, Temkin's claim that two
intersecting exceptional trees have an exceptional union (proof of Lemma B.3 = `stabblowdown`),
and the uniqueness of the stable blow-down (Lemma B.3) in its combinatorial form.

## The incidence data

Let `f : (C', D') → (C, D)` be a proper surjective morphism of connected reduced multipointed
curves over an algebraically closed field (Temkin, App. B, l. 4458). Its *incidence data*
`G : IncidenceGraph V E M` consists of

* the finite set `V` of irreducible components of `C'`;
* the finite set `E` of ordinary double points of `C'`, each with the unordered pair
  `G.ends e : Sym2 V` of components carrying its two branches (a diagonal pair `s(v, v)` is a
  double point of the component `v` itself);
* the geometric genus `G.genus v` of (the normalization of) each component;
* the finite set `M` of marked points (the points of `D'`), with a component `G.mark μ` through
  each of them;
* the set `G.eligible` of components which lie in the semi-stable locus of `(C', D')` and are
  contracted to a point by `f`.

For a component in the semi-stable locus every point is smooth or an ordinary double point, and a
marked point on it is a smooth point lying on no other component, so all intersections of eligible
components with other components are recorded by `E`, and `G.mark` is unambiguous on them. Only
the data along eligible components enter the definitions below.

For a set `Y` of components (a closed reduced subcurve of `C'`), `G.inner Y` is the set of double
points with both branches on `Y`, `G.boundary Y` the set of double points with exactly one branch
on `Y` (if `Y` consists of eligible components this is Temkin's boundary
`∂_{C'}(Y) = Y ∩ (C' ∖ Y)⁻`), and `G.marks Y` the marked points on `Y`. Connectedness of `Y` is
expressed by cuts (`IsConnected`); `Y` is a *tree* if moreover it has exactly `#Y - 1` inner double
points; a *`ℙ¹`-tree* (`IsP1Tree`) is a tree all of whose components have genus zero; this is the
combinatorial side of Temkin's definition `p_a(Y) = 0` (l. 4428–4432), the comparison being the
genus formula (Lemma B.1), see `combGenus`. An *exceptional tree* (`IsExceptionalTree`,
l. 4473–4474) is a `ℙ¹`-tree of eligible components with `|Y ∩ D'| + |∂Y| ≤ 2`; an *exceptional
component* (`IsExceptional`, l. 4459–4462) is an exceptional tree with one component.

## Main results

* `IsConnected.card_le_card_inner_add_one`, `IsTree.card_inner_add_one_le`: a connected curve has
  at least `#Y - 1` inner double points; a subcurve of a tree has at most `#Y - 1`.
* `isP1Tree_iff_combGenus_eq_zero`, `combGenus_nonneg`: the combinatorial arithmetic genus
  `#inner - #Y + 1 + ∑ genus` of a connected curve is nonnegative and vanishes exactly for
  `ℙ¹`-trees; `card_boundary_sub_one_le` is the inequality `g(x) ≥ n - 1` of Corollary B.2
  (`stabdowncor`) in combinatorial form.
* `IsExceptionalTree.union`: two exceptional trees which meet have an exceptional union (the
  claim in the proof of Lemma B.3), under the hypothesis `IsAnchored` that no nonempty set of
  eligible components is a connected component of `C'`.
* `eq_of_meets_of_maximal`, `IsExceptionalTree.exists_maximal`,
  `IsExceptionalTree.eq_of_maximal`: maximal exceptional trees are pairwise separated and every
  exceptional tree lies in a unique maximal one.
* `sum_star_le`, `IsExceptionalTree.exists_isExceptionalTree_star`,
  `IsExceptionalTree.exists_isExceptional`: an exceptional tree contains an exceptional
  component, also after contracting a separated family of exceptional trees inside it (a
  counting argument based on the handshake identity `sum_card_boundary_singleton`).
* `IsStableFamily.mem_iff`, `isStableFamily_maximal`, `IsStableFamily.eq`: **uniqueness of the
  stable blow-down** (Lemma B.3): a separated family of exceptional trees whose contraction has
  no exceptional component consists exactly of the maximal exceptional trees.

## Contraction and stability

Contracting a separated family `𝒯` of exceptional trees (pairwise disjoint, no double point
joining two of them) produces a curve `C̄'` whose components are the components `v` not in
`⋃ 𝒯`; the preimage in `C'` of the component `v̄` is `G.star 𝒯 v`, the union of `v` with the
trees of `𝒯` meeting it, and `v̄` is an exceptional component of `C̄'` exactly when
`G.star 𝒯 v` is an exceptional tree of `C'` (the special points of `v̄` are the images of the
marked points and boundary points of the star; `v̄ ≅ ℙ¹` exactly when the star is a tree). This
is how the geometric statement "the stable blow-down has no exceptional component" enters
`IsStableFamily.stable`.

## Literature note

In the proof of Lemma B.3 (l. 4476–4479) Temkin asserts that if neither of two intersecting
exceptional trees `Y₁, Y₂` contains the other, there is a double point with one branch in
`Y₁ ∖ Y₂` and the other in `Y₂ ∖ Y₁`. This fails, e.g., for three components `a, b, c` with
double points `a ∩ b`, `a ∩ c` and `Y₁ = a ∪ b`, `Y₂ = a ∪ c`. The inequality
`|∂(Y₁ ∪ Y₂)| ≤ |∂Y₁| + |∂Y₂| - 2` he derives from it still holds, by the submodularity identity
`|∂(Y₁ ∪ Y₂)| + |∂(Y₁ ∩ Y₂)| + 2 x = |∂Y₁| + |∂Y₂|`, where `x` is the number of double points
joining `Y₁ ∖ Y₂` to `Y₂ ∖ Y₁` (`card_boundary_union_add`), and the bound `|∂(Y₁ ∩ Y₂)| ≥ 2` for a
nonempty common part when neither tree contains the other (`two_mul_le_card_boundary_inter`).
That the union is again a tree also needs the connectedness of `C'` and the surjectivity of `f`
(which exclude, e.g., a cycle of four contracted rational components covered by two
exceptional paths); this is the hypothesis `IsAnchored`. Finally, the last sentence of the proof
("by Corollary B.2 any semi-stable blow down contracts few disjoint exceptional trees, hence the
stable blow down factors through it") uses that the image of a maximal exceptional tree in a
blow-down without exceptional components is a point; this is the counting lemma `sum_star_le`.
-/

namespace DeJongAlterations.StableModification.CurvesField

open Finset

universe u v w

/-- The incidence data of a proper reduced multipointed curve `(C', D')` mapping to a curve `C`
(Temkin, App. B): components `V`, ordinary double points `E` with the components `ends e` of their
two branches, the geometric genera of the components, the marked points `M` with their components,
and the set of *eligible* components (in the semi-stable locus of `(C', D')` and contracted to a
point of `C`). -/
structure IncidenceGraph (V : Type u) (E : Type v) (M : Type w) where
  /-- The components carrying the two branches of a double point. -/
  ends : E → Sym2 V
  /-- The geometric genus of a component (the genus of its normalization). -/
  genus : V → ℕ
  /-- The component through a marked point. -/
  mark : M → V
  /-- The components lying in the semi-stable locus of `(C', D')` and contracted to points. -/
  eligible : Set V

namespace IncidenceGraph

variable {V : Type u} {E : Type v} {M : Type w} (G : IncidenceGraph V E M)

/-- Every double point has two (possibly equal) branch components. -/
theorem exists_ends (e : E) : ∃ a b, G.ends e = s(a, b) :=
  Sym2.ind (f := fun z ↦ ∃ a b, z = s(a, b)) (fun a b ↦ ⟨a, b, rfl⟩) (G.ends e)

variable [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

set_option linter.unusedSectionVars false

section Basic

/-- The double points with both branches on `Y`. -/
def inner (Y : Finset V) : Finset E :=
  univ.filter fun e ↦ G.ends e ∈ Y.sym2

open scoped Classical in
/-- The double points with exactly one branch on `Y` (Temkin's `∂_{C'}(Y)` for `Y` inside the
semi-stable locus). -/
noncomputable def boundary (Y : Finset V) : Finset E :=
  univ.filter fun e ↦ (∃ v ∈ G.ends e, v ∈ Y) ∧ ∃ v ∈ G.ends e, v ∉ Y

/-- The marked points on `Y`. -/
def marks (Y : Finset V) : Finset M :=
  univ.filter fun μ ↦ G.mark μ ∈ Y

variable {G}

theorem mem_inner {Y : Finset V} {e : E} : e ∈ G.inner Y ↔ ∀ v ∈ G.ends e, v ∈ Y := by
  simp [inner, Finset.mem_sym2_iff]

theorem mem_inner_of_ends {Y : Finset V} {e : E} {a b : V} (h : G.ends e = s(a, b)) :
    e ∈ G.inner Y ↔ a ∈ Y ∧ b ∈ Y := by
  rw [mem_inner, h]
  simp

theorem mem_boundary {Y : Finset V} {e : E} :
    e ∈ G.boundary Y ↔ (∃ v ∈ G.ends e, v ∈ Y) ∧ ∃ v ∈ G.ends e, v ∉ Y := by
  classical
  simp [boundary]

theorem mem_boundary_of_ends {Y : Finset V} {e : E} {a b : V} (h : G.ends e = s(a, b)) :
    e ∈ G.boundary Y ↔ (a ∈ Y ∧ b ∉ Y) ∨ (a ∉ Y ∧ b ∈ Y) := by
  rw [mem_boundary, h]
  by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y <;> simp [ha, hb]

theorem mem_marks {Y : Finset V} {μ : M} : μ ∈ G.marks Y ↔ G.mark μ ∈ Y := by
  simp [marks]

theorem inner_mono {X Y : Finset V} (h : X ⊆ Y) : G.inner X ⊆ G.inner Y := fun _ he ↦
  mem_inner.2 fun v hv ↦ h (mem_inner.1 he v hv)

theorem marks_mono {X Y : Finset V} (h : X ⊆ Y) : G.marks X ⊆ G.marks Y := fun _ hμ ↦
  mem_marks.2 (h (mem_marks.1 hμ))

@[simp] theorem inner_empty : G.inner ∅ = ∅ := by
  ext e
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  simp [mem_inner_of_ends h]

@[simp] theorem boundary_empty : G.boundary ∅ = ∅ := by
  ext e
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  simp [mem_boundary_of_ends h]

@[simp] theorem marks_empty : G.marks ∅ = ∅ := by
  ext μ
  simp [mem_marks]

theorem inner_inter (X Y : Finset V) : G.inner (X ∩ Y) = G.inner X ∩ G.inner Y := by
  ext e
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  simp only [mem_inter, mem_inner_of_ends h]
  tauto

theorem marks_union (X Y : Finset V) : G.marks (X ∪ Y) = G.marks X ∪ G.marks Y := by
  ext μ
  simp [mem_marks]

theorem marks_inter (X Y : Finset V) : G.marks (X ∩ Y) = G.marks X ∩ G.marks Y := by
  ext μ
  simp [mem_marks]

omit [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M] in
/-- Cardinalities of finite sets as sums of indicator functions. -/
theorem card_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) :
    (s.card : ℤ) = ∑ i, if i ∈ s then 1 else 0 := by
  simp

end Basic

section Meets

/-- Two subcurves *meet* if they share a component or a double point joins them (as closed
subsets of `C'` they have a common point; for subcurves in the semi-stable locus every common
point not on a common component is a double point with one branch on each). -/
def Meets (X Y : Finset V) : Prop :=
  (X ∩ Y).Nonempty ∨ ∃ e, (∃ v ∈ G.ends e, v ∈ X) ∧ ∃ v ∈ G.ends e, v ∈ Y

variable {G}

theorem Meets.symm {X Y : Finset V} (h : G.Meets X Y) : G.Meets Y X := by
  rcases h with h | ⟨e, h₁, h₂⟩
  · exact Or.inl (by rwa [inter_comm])
  · exact Or.inr ⟨e, h₂, h₁⟩

theorem meets_comm {X Y : Finset V} : G.Meets X Y ↔ G.Meets Y X :=
  ⟨Meets.symm, Meets.symm⟩

theorem Meets.mono {X X' Y Y' : Finset V} (h : G.Meets X Y) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    G.Meets X' Y' := by
  rcases h with ⟨v, hv⟩ | ⟨e, ⟨a, ha, haX⟩, ⟨b, hb, hbY⟩⟩
  · rw [mem_inter] at hv
    exact Or.inl ⟨v, mem_inter.2 ⟨hX hv.1, hY hv.2⟩⟩
  · exact Or.inr ⟨e, ⟨a, ha, hX haX⟩, ⟨b, hb, hY hbY⟩⟩

theorem meets_of_mem {X Y : Finset V} {v : V} (hX : v ∈ X) (hY : v ∈ Y) : G.Meets X Y :=
  Or.inl ⟨v, mem_inter.2 ⟨hX, hY⟩⟩

/-- An edge with an end in `X` and an end in `Y` makes them meet. -/
theorem meets_of_ends {X Y : Finset V} {e : E} {a b : V} (h : G.ends e = s(a, b)) (ha : a ∈ X)
    (hb : b ∈ Y) : G.Meets X Y :=
  Or.inr ⟨e, ⟨a, by simp [h], ha⟩, ⟨b, by simp [h], hb⟩⟩

/-- If `X` and `Y` meet and are disjoint, some double point has one branch on each. -/
theorem Meets.exists_ends_of_disjoint {X Y : Finset V} (h : G.Meets X Y) (hXY : Disjoint X Y) :
    ∃ e a b, G.ends e = s(a, b) ∧ a ∈ X ∧ b ∈ Y := by
  rcases h with ⟨v, hv⟩ | ⟨e, ⟨a, ha, haX⟩, ⟨b, hb, hbY⟩⟩
  · exact absurd hv (by simp [disjoint_iff_inter_eq_empty.1 hXY])
  · have hab : a ≠ b := by
      rintro rfl
      exact disjoint_left.1 hXY haX hbY
    exact ⟨e, a, b, (Sym2.mem_and_mem_iff hab).1 ⟨ha, hb⟩, haX, hbY⟩

end Meets

section Trees

/-- `Y` is *connected*: it is nonempty and every nonempty proper part `X ⊊ Y` is joined to
`Y ∖ X` by a double point of `Y`. -/
def IsConnected (Y : Finset V) : Prop :=
  Y.Nonempty ∧ ∀ X ⊆ Y, X.Nonempty → X ≠ Y → ∃ e ∈ G.inner Y, e ∈ G.boundary X

/-- `Y` is a *tree*: connected with exactly `#Y - 1` inner double points (so its incidence graph
— a vertex per component, an edge per double point — is a tree: no cycles, no double point of a
single component, no two double points joining the same two components). -/
def IsTree (Y : Finset V) : Prop :=
  G.IsConnected Y ∧ (G.inner Y).card + 1 = Y.card

/-- A *`ℙ¹`-tree* (combinatorial form of Temkin's `ℙ¹_k`-tree, App. B l. 4428–4432): a tree whose
components have geometric genus zero. -/
def IsP1Tree (Y : Finset V) : Prop :=
  G.IsTree Y ∧ ∀ v ∈ Y, G.genus v = 0

/-- The *combinatorial arithmetic genus* `h¹(Γ_Y) + ∑_{v ∈ Y} g(v)` of a connected subcurve `Y`,
where `h¹(Γ_Y) = #inner - #Y + 1` is the first Betti number of its incidence graph; by the genus
formula (Lemma B.1) this is `p_a(Y)` when `Y` is a proper connected curve with only ordinary
double points. -/
def combGenus (Y : Finset V) : ℤ :=
  (G.inner Y).card - Y.card + 1 + ∑ v ∈ Y, (G.genus v : ℤ)

variable {G}

theorem IsConnected.nonempty {Y : Finset V} (h : G.IsConnected Y) : Y.Nonempty := h.1

theorem IsTree.isConnected {Y : Finset V} (h : G.IsTree Y) : G.IsConnected Y := h.1

theorem IsTree.card_inner_add_one {Y : Finset V} (h : G.IsTree Y) :
    (G.inner Y).card + 1 = Y.card := h.2

theorem IsP1Tree.isTree {Y : Finset V} (h : G.IsP1Tree Y) : G.IsTree Y := h.1

theorem IsP1Tree.genus_eq_zero {Y : Finset V} (h : G.IsP1Tree Y) {v : V} (hv : v ∈ Y) :
    G.genus v = 0 := h.2 v hv

theorem isConnected_singleton (v : V) : G.IsConnected {v} := by
  refine ⟨singleton_nonempty v, fun X hX hXne hne ↦ ?_⟩
  exact absurd ((subset_singleton_iff.1 hX).resolve_left hXne.ne_empty) hne

/-- **Growth.** If `Y` is connected and `X ⊆ Y` is nonempty, adding the components of `Y ∖ X` one
at a time adds at least one inner double point each time. -/
theorem IsConnected.card_inner_add_card_le {Y X : Finset V} (hY : G.IsConnected Y) (hXY : X ⊆ Y)
    (hX : X.Nonempty) : (G.inner X).card + Y.card ≤ (G.inner Y).card + X.card := by
  obtain ⟨n, hn⟩ : ∃ n, Y.card - X.card = n := ⟨_, rfl⟩
  induction n generalizing X with
  | zero =>
    have : X = Y := eq_of_subset_of_card_le hXY (by omega)
    subst this
    omega
  | succ n ih =>
    have hne : X ≠ Y := by
      rintro rfl
      simp at hn
    obtain ⟨e, heY, heX⟩ := hY.2 X hXY hX hne
    obtain ⟨a, b, hab⟩ := exists_ends (G := G) e
    rw [mem_boundary_of_ends hab] at heX
    rw [mem_inner_of_ends hab] at heY
    obtain ⟨c, hcY, hcX, hce, hceX⟩ :
        ∃ c ∈ Y, c ∉ X ∧ e ∈ G.inner (insert c X) ∧ e ∉ G.inner X := by
      rcases heX with ⟨haX, hbX⟩ | ⟨haX, hbX⟩
      · exact ⟨b, heY.2, hbX, (mem_inner_of_ends hab).2 ⟨mem_insert_of_mem haX,
          mem_insert_self _ _⟩, fun h ↦ hbX ((mem_inner_of_ends hab).1 h).2⟩
      · exact ⟨a, heY.1, haX, (mem_inner_of_ends hab).2 ⟨mem_insert_self _ _,
          mem_insert_of_mem hbX⟩, fun h ↦ haX ((mem_inner_of_ends hab).1 h).1⟩
    have hcard : (insert c X).card = X.card + 1 := card_insert_of_notMem hcX
    have h2 := ih (insert_subset hcY hXY) (insert_nonempty _ _) (by omega)
    have h3 : (G.inner X).card + 1 ≤ (G.inner (insert c X)).card := by
      rw [← card_insert_of_notMem hceX]
      exact card_le_card (insert_subset hce (inner_mono (subset_insert _ _)))
    omega

/-- A connected curve with `#Y` components has at least `#Y - 1` double points. -/
theorem IsConnected.card_le_card_inner_add_one {Y : Finset V} (hY : G.IsConnected Y) :
    Y.card ≤ (G.inner Y).card + 1 := by
  obtain ⟨v, hv⟩ := hY.nonempty
  have := hY.card_inner_add_card_le (singleton_subset_iff.2 hv) (singleton_nonempty v)
  simp only [card_singleton] at this
  omega

/-- A nonempty subcurve of a tree has at most `#X - 1` inner double points. -/
theorem IsTree.card_inner_add_one_le {Y X : Finset V} (hY : G.IsTree Y) (hXY : X ⊆ Y)
    (hX : X.Nonempty) : (G.inner X).card + 1 ≤ X.card := by
  have := hY.isConnected.card_inner_add_card_le hXY hX
  have := hY.card_inner_add_one
  omega

/-- A connected subcurve of a tree is a tree. -/
theorem IsTree.isTree_of_subset {Y X : Finset V} (hY : G.IsTree Y) (hXY : X ⊆ Y)
    (hX : G.IsConnected X) : G.IsTree X :=
  ⟨hX, le_antisymm (hY.card_inner_add_one_le hXY hX.nonempty)
    hX.card_le_card_inner_add_one⟩

/-- A tree has no double point on a single component. -/
theorem IsTree.inner_singleton {Y : Finset V} (hY : G.IsTree Y) {v : V} (hv : v ∈ Y) :
    G.inner {v} = ∅ := by
  have := hY.card_inner_add_one_le (singleton_subset_iff.2 hv) (singleton_nonempty v)
  simp only [card_singleton] at this
  exact card_eq_zero.1 (by omega)

/-- A double point of a tree joins two distinct components. -/
theorem IsTree.ne_of_mem_inner {Y : Finset V} (hY : G.IsTree Y) {e : E} (he : e ∈ G.inner Y)
    {a b : V} (h : G.ends e = s(a, b)) : a ≠ b := by
  rintro rfl
  have ha := ((mem_inner_of_ends h).1 he).1
  have : e ∈ G.inner {a} := (mem_inner_of_ends h).2 ⟨mem_singleton_self a, mem_singleton_self a⟩
  simp [hY.inner_singleton ha] at this

theorem combGenus_nonneg {Y : Finset V} (hY : G.IsConnected Y) : 0 ≤ G.combGenus Y := by
  have h1 := hY.card_le_card_inner_add_one
  have h2 : (0 : ℤ) ≤ ∑ v ∈ Y, (G.genus v : ℤ) := sum_nonneg fun v _ ↦ Int.natCast_nonneg _
  unfold combGenus
  omega

/-- `Y` is a `ℙ¹`-tree if and only if it is connected of combinatorial arithmetic genus zero (the
combinatorial half of Temkin's characterization of `ℙ¹_k`-trees, App. B l. 4429–4431). -/
theorem isP1Tree_iff_combGenus_eq_zero {Y : Finset V} :
    G.IsP1Tree Y ↔ G.IsConnected Y ∧ G.combGenus Y = 0 := by
  constructor
  · rintro ⟨⟨hc, hcard⟩, hg⟩
    refine ⟨hc, ?_⟩
    have : ∑ v ∈ Y, (G.genus v : ℤ) = 0 := sum_eq_zero fun v hv ↦ by simp [hg v hv]
    unfold combGenus
    omega
  · rintro ⟨hc, h0⟩
    have h1 := hc.card_le_card_inner_add_one
    have h2 : ∀ v ∈ Y, (0 : ℤ) ≤ G.genus v := fun v _ ↦ Int.natCast_nonneg _
    have h3 := sum_nonneg h2
    unfold combGenus at h0
    have hsum : ∑ v ∈ Y, (G.genus v : ℤ) = 0 := by omega
    refine ⟨⟨hc, by omega⟩, fun v hv ↦ ?_⟩
    have := (sum_eq_zero_iff_of_nonneg h2).1 hsum v hv
    exact_mod_cast this

/-- **Corollary B.2, combinatorial core** (`stabdowncor`, l. 4443–4449). For a connected subcurve
`Y` with `n = #∂Y` boundary points, the number `g = #∂Y + #inner Y + ∑ g(v) - #Y` (the right side
of the genus formula for the contraction of `Y` to a point) satisfies `g ≥ n - 1`, with equality
exactly when `Y` is a `ℙ¹`-tree. -/
theorem card_boundary_sub_one_le {Y : Finset V} (hY : G.IsConnected Y) :
    ((G.boundary Y).card : ℤ) - 1 ≤
      (G.boundary Y).card + (G.inner Y).card + ∑ v ∈ Y, (G.genus v : ℤ) - Y.card := by
  have := combGenus_nonneg hY
  unfold combGenus at this
  omega

theorem card_boundary_sub_one_eq_iff {Y : Finset V} (hY : G.IsConnected Y) :
    ((G.boundary Y).card : ℤ) - 1 =
        (G.boundary Y).card + (G.inner Y).card + ∑ v ∈ Y, (G.genus v : ℤ) - Y.card ↔
      G.IsP1Tree Y := by
  rw [isP1Tree_iff_combGenus_eq_zero]
  unfold combGenus
  constructor
  · intro h
    exact ⟨hY, by omega⟩
  · rintro ⟨-, h⟩
    omega

end Trees

section Union

variable {G}

/-- A double point with one branch in `X` and the other outside, both on `S`. -/
theorem exists_inner_boundary_of_ends {S X : Finset V} {e : E} {a b : V} (h : G.ends e = s(a, b))
    (ha : a ∈ S) (hb : b ∈ S) (haX : a ∈ X) (hbX : b ∉ X) :
    ∃ e ∈ G.inner S, e ∈ G.boundary X :=
  ⟨e, (mem_inner_of_ends h).2 ⟨ha, hb⟩, (mem_boundary_of_ends h).2 (Or.inl ⟨haX, hbX⟩)⟩

/-- If a connected `T ⊆ S` is cut by `X`, some double point of `S` crosses `X`. -/
theorem IsConnected.exists_inner_boundary {S T X : Finset V} (hT : G.IsConnected T) (hTS : T ⊆ S)
    (h₁ : (X ∩ T).Nonempty) (h₂ : ¬T ⊆ X) : ∃ e ∈ G.inner S, e ∈ G.boundary X := by
  have hne : X ∩ T ≠ T := fun h ↦ h₂ (inter_eq_right.1 h)
  obtain ⟨e, he, heb⟩ := hT.2 (X ∩ T) inter_subset_right h₁ hne
  refine ⟨e, inner_mono hTS he, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_ends (G := G) e
  rw [mem_inner_of_ends hab] at he
  rw [mem_boundary_of_ends hab, mem_inter, mem_inter] at heb
  rw [mem_boundary_of_ends hab]
  tauto

/-- If `Y ⊆ X` and `Z` (disjoint from `X`) meet and both lie in `S`, a double point of `S`
crosses `X`. -/
theorem Meets.exists_inner_boundary {S X Y Z : Finset V} (hm : G.Meets Y Z) (hYZ : Disjoint Y Z)
    (hYS : Y ⊆ S) (hZS : Z ⊆ S) (hYX : Y ⊆ X) (hZX : Disjoint Z X) :
    ∃ e ∈ G.inner S, e ∈ G.boundary X := by
  obtain ⟨e, a, b, hab, ha, hb⟩ := hm.exists_ends_of_disjoint hYZ
  exact exists_inner_boundary_of_ends hab (hYS ha) (hZS hb) (hYX ha) (disjoint_left.1 hZX hb)

/-- The union of two connected subcurves which meet is connected. -/
theorem IsConnected.union {A B : Finset V} (hA : G.IsConnected A) (hB : G.IsConnected B)
    (hm : G.Meets A B) : G.IsConnected (A ∪ B) := by
  refine ⟨hA.nonempty.mono subset_union_left, fun X hX hXne hne ↦ ?_⟩
  by_cases hA₁ : (X ∩ A).Nonempty
  · by_cases hA₂ : A ⊆ X
    · by_cases hB₁ : (X ∩ B).Nonempty
      · by_cases hB₂ : B ⊆ X
        · exact absurd (subset_antisymm hX (union_subset hA₂ hB₂)) hne
        · exact hB.exists_inner_boundary subset_union_right hB₁ hB₂
      · have hBX : Disjoint B X := by
          rw [disjoint_left]
          intro v hvB hvX
          exact hB₁ ⟨v, mem_inter.2 ⟨hvX, hvB⟩⟩
        have hAB : Disjoint A B := by
          rw [disjoint_left]
          intro v hvA hvB
          exact disjoint_left.1 hBX hvB (hA₂ hvA)
        exact hm.exists_inner_boundary hAB subset_union_left subset_union_right hA₂ hBX
    · exact hA.exists_inner_boundary subset_union_left hA₁ hA₂
  · have hAX : Disjoint A X := by
      rw [disjoint_left]
      intro v hvA hvX
      exact hA₁ ⟨v, mem_inter.2 ⟨hvX, hvA⟩⟩
    have hXB : X ⊆ B := fun v hv ↦ by
      rcases mem_union.1 (hX hv) with h | h
      · exact absurd hv (disjoint_left.1 hAX h)
      · exact h
    have hB₁ : (X ∩ B).Nonempty := by rwa [inter_eq_left.2 hXB]
    by_cases hB₂ : B ⊆ X
    · have hAB : Disjoint B A := by
        rw [disjoint_left]
        intro v hvB hvA
        exact disjoint_left.1 hAX hvA (hB₂ hvB)
      exact hm.symm.exists_inner_boundary hAB subset_union_right subset_union_left hB₂ hAX
    · exact hB.exists_inner_boundary subset_union_right hB₁ hB₂

variable (G) in
/-- The double points joining `A ∖ B` to `B ∖ A`: inner double points of `A ∪ B` which are inner
neither to `A` nor to `B`. -/
def cross (A B : Finset V) : Finset E :=
  G.inner (A ∪ B) \ (G.inner A ∪ G.inner B)

theorem card_inner_union_add (A B : Finset V) :
    ((G.inner (A ∪ B)).card : ℤ) + (G.inner (A ∩ B)).card =
      (G.inner A).card + (G.inner B).card + (G.cross A B).card := by
  have h₁ : G.inner A ∪ G.inner B ⊆ G.inner (A ∪ B) :=
    union_subset (inner_mono subset_union_left) (inner_mono subset_union_right)
  have h₂ := card_sdiff_add_card_eq_card h₁
  have h₃ := card_union_add_card_inter (G.inner A) (G.inner B)
  rw [← inner_inter] at h₃
  unfold cross
  omega

/-- **Submodularity of the boundary** with defect `2 #cross`:
`|∂(A ∪ B)| + |∂(A ∩ B)| + 2 #cross(A, B) = |∂A| + |∂B|`. -/
theorem card_boundary_union_add (A B : Finset V) :
    ((G.boundary (A ∪ B)).card : ℤ) + (G.boundary (A ∩ B)).card + 2 * (G.cross A B).card =
      (G.boundary A).card + (G.boundary B).card := by
  simp only [card_eq_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e _ ↦ ?_
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  simp only [cross, mem_sdiff, mem_union, mem_boundary_of_ends h, mem_inner_of_ends h, mem_inter]
  by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> by_cases ha' : a ∈ B <;>
    by_cases hb' : b ∈ B <;> simp [ha, hb, ha', hb']

/-- A nonempty proper common part `Q = A ∩ B` of two trees, neither containing the other, has
`|∂Q| ≥ 2 (#Q - #inner Q)`: each of `A ∖ B` and `B ∖ A` is joined to `Q` by at least
`#Q - #inner Q` double points (the number of connected components of `Q`). -/
theorem two_mul_le_card_boundary_inter {A B : Finset V} (hA : G.IsTree A) (hB : G.IsTree B)
    (hAB : ¬A ⊆ B) (hBA : ¬B ⊆ A) :
    2 * (((A ∩ B).card : ℤ) - (G.inner (A ∩ B)).card) ≤ (G.boundary (A ∩ B)).card := by
  have cut : ∀ {A' B' : Finset V}, G.IsTree A' → ¬A' ⊆ B' →
      ((A' ∩ B').card : ℤ) - (G.inner (A' ∩ B')).card ≤
        (G.inner A' \ (G.inner (A' ∩ B') ∪ G.inner (A' \ B'))).card := by
    intro A' B' hA' hA'B'
    have hsub : G.inner (A' ∩ B') ∪ G.inner (A' \ B') ⊆ G.inner A' :=
      union_subset (inner_mono inter_subset_left) (inner_mono sdiff_subset)
    have h₁ := card_sdiff_add_card_eq_card hsub
    have h₂ : Disjoint (G.inner (A' ∩ B')) (G.inner (A' \ B')) := by
      rw [disjoint_iff_inter_eq_empty, ← inner_inter]
      have : A' ∩ B' ∩ (A' \ B') = ∅ := by
        ext v
        simp only [mem_inter, mem_sdiff, notMem_empty, iff_false]
        tauto
      rw [this, inner_empty]
    have h₃ := card_union_of_disjoint h₂
    have h₄ := hA'.card_inner_add_one_le sdiff_subset (sdiff_nonempty.2 hA'B')
    have h₅ := hA'.card_inner_add_one
    have h₆ := card_inter_add_card_sdiff A' B'
    omega
  have cA := cut hA hAB
  have cB := cut (B' := A) hB hBA
  rw [inter_comm B A] at cB
  -- both cut sets lie in `∂Q` and are disjoint
  have hsubA : G.inner A \ (G.inner (A ∩ B) ∪ G.inner (A \ B)) ⊆ G.boundary (A ∩ B) := by
    intro e he
    obtain ⟨a, b, h⟩ := exists_ends (G := G) e
    simp only [mem_sdiff, mem_union, mem_inner_of_ends h, mem_inter] at he
    rw [mem_boundary_of_ends h, mem_inter, mem_inter]
    tauto
  have hsubB : G.inner B \ (G.inner (A ∩ B) ∪ G.inner (B \ A)) ⊆ G.boundary (A ∩ B) := by
    intro e he
    obtain ⟨a, b, h⟩ := exists_ends (G := G) e
    simp only [mem_sdiff, mem_union, mem_inner_of_ends h, mem_inter] at he
    rw [mem_boundary_of_ends h, mem_inter, mem_inter]
    tauto
  have hdAB : Disjoint (G.inner A \ (G.inner (A ∩ B) ∪ G.inner (A \ B)))
      (G.inner B \ (G.inner (A ∩ B) ∪ G.inner (B \ A))) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨a, b, h⟩ := exists_ends (G := G) e
    simp only [mem_sdiff, mem_union, mem_inner_of_ends h, mem_inter] at he he'
    tauto
  have := card_le_card (union_subset hsubA hsubB)
  rw [card_union_of_disjoint hdAB] at this
  omega

end Union

section Exceptional

/-- An *exceptional tree* (Temkin, proof of Lemma B.3, l. 4473–4474): a `ℙ¹`-tree of eligible
components (in the semi-stable locus of `(C', D')` and contracted to a point of `C`) carrying at
most two special points, `|Y ∩ D'| + |∂Y| ≤ 2`. -/
def IsExceptionalTree (Y : Finset V) : Prop :=
  G.IsP1Tree Y ∧ (↑Y : Set V) ⊆ G.eligible ∧ (G.marks Y).card + (G.boundary Y).card ≤ 2

/-- An *exceptional component* (Temkin, App. B l. 4459–4462 and §1.2 l. 1687–1689): an eligible
component isomorphic to `ℙ¹` (genus zero, no double point of its own) with at most two points
of `D' ∪ C'_sing`. -/
def IsExceptional (v : V) : Prop :=
  G.IsExceptionalTree {v}

/-- `G` is *anchored* if no nonempty set of eligible components is closed and open in `C'`, i.e.
every such set has a boundary double point. This holds when `C'` is connected and `f` is
surjective onto a curve: a union of eligible components without boundary would be all of `C'`
and would be contracted to a point. -/
def IsAnchored : Prop :=
  ∀ Y : Finset V, Y.Nonempty → (↑Y : Set V) ⊆ G.eligible → (G.boundary Y).Nonempty

variable {G}

theorem IsExceptionalTree.isP1Tree {Y : Finset V} (h : G.IsExceptionalTree Y) : G.IsP1Tree Y :=
  h.1

theorem IsExceptionalTree.isTree {Y : Finset V} (h : G.IsExceptionalTree Y) : G.IsTree Y :=
  h.1.1

theorem IsExceptionalTree.subset_eligible {Y : Finset V} (h : G.IsExceptionalTree Y) :
    (↑Y : Set V) ⊆ G.eligible :=
  h.2.1

theorem IsExceptionalTree.card_marks_add_card_boundary_le {Y : Finset V}
    (h : G.IsExceptionalTree Y) : (G.marks Y).card + (G.boundary Y).card ≤ 2 :=
  h.2.2

theorem IsExceptionalTree.nonempty {Y : Finset V} (h : G.IsExceptionalTree Y) : Y.Nonempty :=
  h.isTree.isConnected.nonempty

/-- An exceptional component in elementary terms: eligible, of genus zero, without a double
point of its own, and with at most two marked or double points. -/
theorem isExceptional_iff {v : V} :
    G.IsExceptional v ↔ v ∈ G.eligible ∧ G.genus v = 0 ∧ G.inner {v} = ∅ ∧
      (G.marks {v}).card + (G.boundary {v}).card ≤ 2 := by
  unfold IsExceptional IsExceptionalTree IsP1Tree IsTree
  simp only [coe_singleton, Set.singleton_subset_iff, mem_singleton, forall_eq, card_singleton,
    Nat.add_eq_right, card_eq_zero]
  constructor
  · rintro ⟨⟨⟨-, h₁⟩, h₂⟩, h₃, h₄⟩
    exact ⟨h₃, h₂, h₁, h₄⟩
  · rintro ⟨h₃, h₂, h₁, h₄⟩
    exact ⟨⟨⟨isConnected_singleton v, h₁⟩, h₂⟩, h₃, h₄⟩

/-- **Temkin's claim in the proof of Lemma B.3** (l. 4474–4479): two exceptional trees which
meet have an exceptional union. -/
theorem IsExceptionalTree.union (hG : G.IsAnchored) {A B : Finset V}
    (hA : G.IsExceptionalTree A) (hB : G.IsExceptionalTree B) (hm : G.Meets A B) :
    G.IsExceptionalTree (A ∪ B) := by
  by_cases hAB : A ⊆ B
  · rwa [union_eq_right.2 hAB]
  by_cases hBA : B ⊆ A
  · rwa [union_eq_left.2 hBA]
  obtain ⟨⟨hAt, hAg⟩, hAe, hAm⟩ := hA
  obtain ⟨⟨hBt, hBg⟩, hBe, hBm⟩ := hB
  have hconn := hAt.isConnected.union hBt.isConnected hm
  have hel : (↑(A ∪ B) : Set V) ⊆ G.eligible := by
    rw [coe_union]
    exact Set.union_subset hAe hBe
  have h₁ : 1 ≤ (G.boundary (A ∪ B)).card := card_pos.2 (hG _ hconn.nonempty hel)
  have hI := card_inner_union_add (G := G) A B
  have hD := card_boundary_union_add (G := G) A B
  have hM : (G.marks (A ∪ B)).card + (G.marks (A ∩ B)).card =
      (G.marks A).card + (G.marks B).card := by
    rw [marks_union, marks_inter]
    exact card_union_add_card_inter _ _
  have hQ := two_mul_le_card_boundary_inter hAt hBt hAB hBA
  have hcx : 1 ≤ ((A ∩ B).card : ℤ) - (G.inner (A ∩ B)).card + (G.cross A B).card := by
    by_cases hne : (A ∩ B).Nonempty
    · have := hAt.card_inner_add_one_le inter_subset_left hne
      omega
    · have hdisj : Disjoint A B := by
        rw [disjoint_iff_inter_eq_empty]
        exact not_nonempty_iff_eq_empty.1 hne
      obtain ⟨e, a, b, hab, ha, hb⟩ := hm.exists_ends_of_disjoint hdisj
      have he : e ∈ G.cross A B := by
        simp only [cross, mem_sdiff, mem_union, mem_inner_of_ends hab]
        refine ⟨⟨Or.inl ha, Or.inr hb⟩, ?_⟩
        have hbA : b ∉ A := fun h ↦ disjoint_left.1 hdisj h hb
        have haB : a ∉ B := fun h ↦ disjoint_left.1 hdisj ha h
        tauto
      have := card_pos.2 ⟨e, he⟩
      rw [not_nonempty_iff_eq_empty.1 hne]
      simp only [inner_empty, card_empty, Nat.cast_zero]
      omega
  have hcardU := card_union_add_card_inter A B
  have hAc := hAt.card_inner_add_one
  have hBc := hBt.card_inner_add_one
  refine ⟨⟨⟨hconn, ?_⟩, ?_⟩, hel, ?_⟩
  · omega
  · intro v hv
    rcases mem_union.1 hv with h | h
    exacts [hAg v h, hBg v h]
  · omega

end Exceptional

section Maximal

variable {G}

/-- A maximal exceptional tree contains every exceptional tree meeting it. -/
theorem subset_of_meets_of_maximal (hG : G.IsAnchored) {T Y : Finset V}
    (hT : Maximal G.IsExceptionalTree T) (hY : G.IsExceptionalTree Y) (hm : G.Meets Y T) :
    Y ⊆ T :=
  subset_union_left.trans (hT.2 (hY.union hG hT.1 hm) subset_union_right)

/-- **Lemma B.3, first step** (l. 4479–4481): two maximal exceptional trees which meet are
equal; distinct maximal exceptional trees are disjoint and not joined by a double point. -/
theorem eq_of_meets_of_maximal (hG : G.IsAnchored) {T T' : Finset V}
    (hT : Maximal G.IsExceptionalTree T) (hT' : Maximal G.IsExceptionalTree T')
    (hm : G.Meets T T') : T = T' :=
  subset_antisymm (subset_of_meets_of_maximal hG hT' hT.1 hm)
    (subset_of_meets_of_maximal hG hT hT'.1 hm.symm)

/-- Every exceptional tree is contained in a maximal one. -/
theorem IsExceptionalTree.exists_maximal [Fintype V] {Y : Finset V} (hY : G.IsExceptionalTree Y) :
    ∃ T, Y ⊆ T ∧ Maximal G.IsExceptionalTree T :=
  (Set.toFinite {Z : Finset V | G.IsExceptionalTree Z}).exists_le_maximal hY

/-- The maximal exceptional tree containing an exceptional tree is unique. -/
theorem IsExceptionalTree.eq_of_maximal (hG : G.IsAnchored) {Y T T' : Finset V}
    (hY : G.IsExceptionalTree Y) (hT : Maximal G.IsExceptionalTree T)
    (hT' : Maximal G.IsExceptionalTree T') (hYT : Y ⊆ T) (hYT' : Y ⊆ T') : T = T' := by
  obtain ⟨v, hv⟩ := hY.nonempty
  exact eq_of_meets_of_maximal hG hT hT' (meets_of_mem (hYT hv) (hYT' hv))

end Maximal

section Stable

open scoped Classical

/-- A family of subcurves is *separated* if any two distinct members neither share a component
nor are joined by a double point. -/
def IsSeparated (𝒯 : Finset (Finset V)) : Prop :=
  ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ¬G.Meets T T'

/-- The *star* of a component `v` with respect to a family `𝒯`: `v` together with the members of
`𝒯` meeting it. For `v` outside `⋃ 𝒯`, it is the preimage in `C'` of the image of `v` in the
curve obtained by contracting the members of `𝒯`. -/
noncomputable def star (𝒯 : Finset (Finset V)) (v : V) : Finset V :=
  insert v ((𝒯.filter fun T ↦ G.Meets {v} T).biUnion id)

/-- The *defect* `#(marks on v) + #(double points through v, other than those of v itself) - 2`
of a component. A subcurve without double points of its own components (e.g. inside a tree)
satisfies `∑ defect = #marks + 2 #inner + #∂ - 2 #Y` (`sum_defect`). -/
noncomputable def defect (w : V) : ℤ :=
  (G.marks {w}).card + (G.boundary {w}).card - 2

/-- A *stable family*: the combinatorial shadow of a stable blow-down `C' → C̄` of `f`
(Temkin, App. B l. 4463–4467). The members are the subcurves contracted to points; they are
exceptional trees (Corollary B.2, since the image points lie in the semi-stable locus of
`(C̄, D̄)`), pairwise separated (they are fibres over distinct points), and `C̄` has no exceptional
component, i.e. no star of a component outside `⋃ 𝒯` is an exceptional tree. -/
structure IsStableFamily (𝒯 : Finset (Finset V)) : Prop where
  exceptional : ∀ T ∈ 𝒯, G.IsExceptionalTree T
  separated : G.IsSeparated 𝒯
  stable : ∀ v, (∀ T ∈ 𝒯, v ∉ T) → ¬G.IsExceptionalTree (G.star 𝒯 v)

variable {G}

theorem mem_star {𝒯 : Finset (Finset V)} {v w : V} :
    w ∈ G.star 𝒯 v ↔ w = v ∨ ∃ T ∈ 𝒯, G.Meets {v} T ∧ w ∈ T := by
  simp [star, and_assoc]

theorem self_mem_star (𝒯 : Finset (Finset V)) (v : V) : v ∈ G.star 𝒯 v :=
  mem_star.2 (Or.inl rfl)

theorem subset_star {𝒯 : Finset (Finset V)} {v : V} {T : Finset V} (hT : T ∈ 𝒯)
    (hm : G.Meets {v} T) : T ⊆ G.star 𝒯 v :=
  fun _ hw ↦ mem_star.2 (Or.inr ⟨T, hT, hm, hw⟩)

@[simp] theorem star_empty (v : V) : G.star ∅ v = {v} := by
  ext w
  simp [mem_star]

theorem IsSeparated.disjoint {𝒯 : Finset (Finset V)} (h : G.IsSeparated 𝒯) {T T' : Finset V}
    (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯) (hne : T ≠ T') : Disjoint T T' := by
  rw [disjoint_left]
  intro v hv hv'
  exact h T hT T' hT' hne (meets_of_mem hv hv')

theorem IsSeparated.pairwiseDisjoint {𝒯 𝒮 : Finset (Finset V)} (h : G.IsSeparated 𝒯)
    (h𝒮 : 𝒮 ⊆ 𝒯) : Set.PairwiseDisjoint (↑𝒮 : Set (Finset V)) id :=
  fun _ hT _ hT' hne ↦ h.disjoint (h𝒮 hT) (h𝒮 hT') hne

/-- A star of connected subcurves is connected. -/
theorem isConnected_star {𝒯 : Finset (Finset V)} (h𝒯 : ∀ T ∈ 𝒯, G.IsConnected T) (v : V) :
    G.IsConnected (G.star 𝒯 v) := by
  refine ⟨⟨v, self_mem_star 𝒯 v⟩, fun X hX hXne hne ↦ ?_⟩
  have hvS : {v} ⊆ G.star 𝒯 v := singleton_subset_iff.2 (self_mem_star 𝒯 v)
  by_cases hvX : v ∈ X
  · obtain ⟨w, hwS, hwX⟩ : ∃ w ∈ G.star 𝒯 v, w ∉ X := by
      by_contra! h
      exact hne (subset_antisymm hX h)
    rcases mem_star.1 hwS with rfl | ⟨T, hT𝒯, hm, hwT⟩
    · exact absurd hvX hwX
    · have hTX : ¬T ⊆ X := fun h ↦ hwX (h hwT)
      by_cases h₁ : (X ∩ T).Nonempty
      · exact (h𝒯 T hT𝒯).exists_inner_boundary (subset_star hT𝒯 hm) h₁ hTX
      · have hTX' : Disjoint T X := by
          rw [disjoint_left]
          intro u huT huX
          exact h₁ ⟨u, mem_inter.2 ⟨huX, huT⟩⟩
        have hvT : v ∉ T := fun h ↦ disjoint_left.1 hTX' h hvX
        exact hm.exists_inner_boundary (disjoint_singleton_left.2 hvT) hvS (subset_star hT𝒯 hm)
          (singleton_subset_iff.2 hvX) hTX'
  · obtain ⟨w, hwX⟩ := hXne
    rcases mem_star.1 (hX hwX) with rfl | ⟨T, hT𝒯, hm, hwT⟩
    · exact absurd hwX hvX
    · have h₁ : (X ∩ T).Nonempty := ⟨w, mem_inter.2 ⟨hwX, hwT⟩⟩
      by_cases h₂ : T ⊆ X
      · have hvT : v ∉ T := fun h ↦ hvX (h₂ h)
        exact hm.symm.exists_inner_boundary (disjoint_singleton_right.2 hvT) (subset_star hT𝒯 hm)
          hvS h₂ (disjoint_singleton_left.2 hvX)
      · exact (h𝒯 T hT𝒯).exists_inner_boundary (subset_star hT𝒯 hm) h₁ h₂

variable (G) in
/-- The double points of `Y` lying on a single component of `Y`. -/
def loops (Y : Finset V) : Finset E :=
  (G.inner Y).filter fun e ↦ (G.ends e).IsDiag

/-- **Handshake.** Summing over the components of `Y` the double points through them (other
than their own) counts the double points of `Y` between distinct components twice and the
boundary once. -/
theorem sum_card_boundary_singleton (Y : Finset V) :
    ∑ w ∈ Y, ((G.boundary {w}).card : ℤ) + 2 * (G.loops Y).card =
      2 * (G.inner Y).card + (G.boundary Y).card := by
  simp only [card_eq_sum (G.boundary _), card_eq_sum (G.loops Y), card_eq_sum (G.inner Y),
    mul_sum]
  rw [sum_comm, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun e _ ↦ ?_
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  simp only [loops, mem_filter, mem_boundary_of_ends h, mem_inner_of_ends h, mem_singleton, h,
    Sym2.mk_isDiag_iff]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a ∈ Y <;> simp [ha]
  · have key : ∀ w, (if (a = w ∧ ¬b = w) ∨ (¬a = w ∧ b = w) then (1 : ℤ) else 0) =
        (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
      intro w
      by_cases h₁ : a = w <;> by_cases h₂ : b = w
      · exact absurd (h₁.trans h₂.symm) hab
      all_goals simp [h₁, h₂]
    simp only [key, sum_add_distrib, sum_ite_eq]
    by_cases ha : a ∈ Y <;> by_cases hb : b ∈ Y <;> simp [ha, hb, hab]

theorem sum_card_marks_singleton (Y : Finset V) :
    ∑ w ∈ Y, ((G.marks {w}).card : ℤ) = (G.marks Y).card := by
  simp only [card_eq_sum (G.marks _)]
  rw [sum_comm]
  refine sum_congr rfl fun μ _ ↦ ?_
  simp only [mem_marks, mem_singleton]
  rw [sum_ite_eq]

/-- The defect sum of a subcurve without double points on single components. -/
theorem sum_defect {Y : Finset V} (hY : G.loops Y = ∅) :
    ∑ w ∈ Y, G.defect w =
      (G.marks Y).card + 2 * (G.inner Y).card + (G.boundary Y).card - 2 * Y.card := by
  have h₁ := sum_card_boundary_singleton (G := G) Y
  have h₂ := sum_card_marks_singleton (G := G) Y
  rw [hY, card_empty, Nat.cast_zero, mul_zero, add_zero] at h₁
  simp only [defect, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
  omega

/-- A subcurve of a tree has no double point on a single component. -/
theorem IsTree.loops_eq_empty {Y S : Finset V} (hY : G.IsTree Y) (hS : S ⊆ Y) :
    G.loops S = ∅ := by
  ext e
  simp only [loops, mem_filter, notMem_empty, iff_false, not_and]
  intro he hdiag
  obtain ⟨a, b, h⟩ := exists_ends (G := G) e
  rw [h, Sym2.mk_isDiag_iff] at hdiag
  exact hY.ne_of_mem_inner (inner_mono hS he) h hdiag

theorem IsTree.sum_defect {Y : Finset V} (hY : G.IsTree Y) :
    ∑ w ∈ Y, G.defect w = (G.marks Y).card + (G.boundary Y).card - 2 := by
  rw [IncidenceGraph.sum_defect (hY.loops_eq_empty subset_rfl)]
  have := hY.card_inner_add_one
  omega

/-- The star of a component of `Y` lies in `Y` if every member of `𝒯` meeting `Y` lies in it. -/
theorem star_subset {𝒯 : Finset (Finset V)} {Y : Finset V} {v : V} (hv : v ∈ Y)
    (hsat : ∀ T ∈ 𝒯, G.Meets T Y → T ⊆ Y) : G.star 𝒯 v ⊆ Y := by
  intro w hw
  rcases mem_star.1 hw with rfl | ⟨T, hT, hm, hwT⟩
  · exact hv
  · exact hsat T hT (hm.symm.mono subset_rfl (singleton_subset_iff.2 hv)) hwT

/-- **Counting lemma.** Let `Y` be a tree, `𝒯` a separated family of trees with at most two
special points each, every member meeting `Y` contained in `Y`, and `U ≠ ∅` the set of
components of `Y` outside `⋃ 𝒯`. Then the stars of the components in `U` carry in total at most
`2 #U + (|Y ∩ D'| + |∂Y|) - 2` special points. -/
theorem sum_star_le {Y : Finset V} {𝒯 : Finset (Finset V)} (hY : G.IsTree Y)
    (h𝒯 : ∀ T ∈ 𝒯, G.IsTree T ∧ (G.marks T).card + (G.boundary T).card ≤ 2)
    (hsep : G.IsSeparated 𝒯) (hsat : ∀ T ∈ 𝒯, G.Meets T Y → T ⊆ Y)
    (hU : (Y.filter fun v ↦ ∀ T ∈ 𝒯, v ∉ T).Nonempty) :
    ∑ v ∈ Y.filter (fun v ↦ ∀ T ∈ 𝒯, v ∉ T),
        (((G.marks (G.star 𝒯 v)).card : ℤ) + (G.boundary (G.star 𝒯 v)).card) ≤
      2 * (Y.filter fun v ↦ ∀ T ∈ 𝒯, v ∉ T).card + (G.marks Y).card + (G.boundary Y).card - 2 := by
  set U := Y.filter fun v ↦ ∀ T ∈ 𝒯, v ∉ T with hUdef
  set S : Finset V → ℤ := fun T ↦ ∑ w ∈ T, G.defect w with hS
  have hST : ∀ T ∈ 𝒯, S T ≤ 0 := by
    intro T hT
    simp only [hS, (h𝒯 T hT).1.sum_defect]
    have := (h𝒯 T hT).2
    omega
  -- the special points of a star are bounded by the defects of its pieces
  have step₁ : ∀ v ∈ U, ((G.marks (G.star 𝒯 v)).card : ℤ) + (G.boundary (G.star 𝒯 v)).card ≤
      G.defect v + (∑ T ∈ 𝒯, if G.Meets {v} T then S T else 0) + 2 := by
    intro v hv
    obtain ⟨hvY, hvT⟩ := mem_filter.1 hv
    have hsub := star_subset (G := G) hvY hsat
    have hconn := isConnected_star (fun T hT ↦ (h𝒯 T hT).1.isConnected) v
    have hsum := IncidenceGraph.sum_defect (hY.loops_eq_empty hsub)
    have hcard := hconn.card_le_card_inner_add_one
    have hdec : ∑ w ∈ G.star 𝒯 v, G.defect w =
        G.defect v + ∑ T ∈ 𝒯, if G.Meets {v} T then S T else 0 := by
      have hvB : v ∉ (𝒯.filter fun T ↦ G.Meets {v} T).biUnion id := by
        rw [mem_biUnion]
        rintro ⟨T, hT, hvT'⟩
        exact hvT T (mem_filter.1 hT).1 hvT'
      rw [star, sum_insert hvB, sum_biUnion (hsep.pairwiseDisjoint (filter_subset _ _)),
        sum_filter]
      rfl
    omega
  -- exchanging the order of summation
  have step₂ : ∑ v ∈ U, (∑ T ∈ 𝒯, if G.Meets {v} T then S T else 0) =
      ∑ T ∈ 𝒯, ((U.filter fun v ↦ G.Meets {v} T).card : ℤ) * S T := by
    rw [sum_comm]
    refine sum_congr rfl fun T _ ↦ ?_
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  -- each member of `𝒯` inside `Y` lies in the star of some component of `U`
  have step₃ : ∀ T ∈ 𝒯,
      ((U.filter fun v ↦ G.Meets {v} T).card : ℤ) * S T ≤ if T ⊆ Y then S T else 0 := by
    intro T hT
    by_cases hTY : T ⊆ Y
    · rw [if_pos hTY]
      obtain ⟨v₀, hv₀⟩ := hU
      obtain ⟨hv₀Y, hv₀T⟩ := mem_filter.1 hv₀
      have hTne : T ≠ Y := fun h ↦ hv₀T T hT (h ▸ hv₀Y)
      obtain ⟨e, he, heb⟩ := hY.isConnected.2 T hTY (h𝒯 T hT).1.isConnected.nonempty hTne
      obtain ⟨a, b, hab⟩ := exists_ends (G := G) e
      obtain ⟨a, b, hab, haT, hbY, hbT⟩ :
          ∃ a b, G.ends e = s(a, b) ∧ a ∈ T ∧ b ∈ Y ∧ b ∉ T := by
        rw [mem_inner_of_ends hab] at he
        rcases (mem_boundary_of_ends hab).1 heb with ⟨haT, hbT⟩ | ⟨haT, hbT⟩
        · exact ⟨a, b, hab, haT, he.2, hbT⟩
        · exact ⟨b, a, hab.trans Sym2.eq_swap, hbT, he.1, haT⟩
      have hbU : b ∈ U.filter fun v ↦ G.Meets {v} T := by
        refine mem_filter.2 ⟨mem_filter.2 ⟨hbY, fun T' hT' hbT' ↦ ?_⟩,
          meets_of_ends (hab.trans Sym2.eq_swap) (mem_singleton_self b) haT⟩
        have hne : T ≠ T' := fun h ↦ hbT (h ▸ hbT')
        exact hsep T hT T' hT' hne (meets_of_ends hab haT hbT')
      have h₁ : (1 : ℤ) ≤ (U.filter fun v ↦ G.Meets {v} T).card := by
        exact_mod_cast card_pos.2 ⟨b, hbU⟩
      have := hST T hT
      nlinarith
    · rw [if_neg hTY]
      have : U.filter (fun v ↦ G.Meets {v} T) = ∅ := by
        rw [filter_eq_empty_iff]
        intro v hv hm
        exact hTY (hsat T hT (hm.symm.mono subset_rfl
          (singleton_subset_iff.2 (mem_filter.1 hv).1)))
      simp [this]
  -- the components of `Y` are those of `U` and those of the members of `𝒯` inside `Y`
  have step₄ : ∑ v ∈ U, G.defect v + ∑ T ∈ 𝒯, (if T ⊆ Y then S T else 0) =
      ∑ w ∈ Y, G.defect w := by
    have hcov : Y.filter (fun v ↦ ¬∀ T ∈ 𝒯, v ∉ T) = (𝒯.filter fun T ↦ T ⊆ Y).biUnion id := by
      ext w
      simp only [mem_filter, mem_biUnion, id, not_forall, not_not]
      constructor
      · rintro ⟨hwY, T, hT, hwT⟩
        exact ⟨T, ⟨hT, hsat T hT (meets_of_mem hwT hwY)⟩, hwT⟩
      · rintro ⟨T, ⟨hT, hTY⟩, hwT⟩
        exact ⟨hTY hwT, T, hT, hwT⟩
    rw [← sum_filter, ← sum_filter_add_sum_filter_not Y (fun v ↦ ∀ T ∈ 𝒯, v ∉ T), hcov,
      sum_biUnion (hsep.pairwiseDisjoint (filter_subset _ _))]
    rfl
  have step₅ := hY.sum_defect
  have hsum₁ := sum_le_sum step₁
  have e₁ : ∑ v ∈ U, (G.defect v + (∑ T ∈ 𝒯, if G.Meets {v} T then S T else 0) + 2) =
      ∑ v ∈ U, G.defect v + ∑ v ∈ U, (∑ T ∈ 𝒯, if G.Meets {v} T then S T else 0) +
        2 * U.card := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
    omega
  rw [e₁, step₂] at hsum₁
  have hsum₂ := sum_le_sum step₃
  linarith

/-- **Exceptional components after contraction.** Let `Y` be an exceptional tree and `𝒯` a
separated family of exceptional trees such that every member meeting `Y` lies in `Y`. If some
component of `Y` is not in `⋃ 𝒯`, then for some such component `w` the star of `w` is an
exceptional tree: after contracting the members of `𝒯`, the image of `Y` contains an
exceptional component. -/
theorem IsExceptionalTree.exists_isExceptionalTree_star {Y : Finset V} {𝒯 : Finset (Finset V)}
    (hY : G.IsExceptionalTree Y) (h𝒯 : ∀ T ∈ 𝒯, G.IsExceptionalTree T)
    (hsep : G.IsSeparated 𝒯) (hsat : ∀ T ∈ 𝒯, G.Meets T Y → T ⊆ Y) {v : V} (hv : v ∈ Y)
    (hvT : ∀ T ∈ 𝒯, v ∉ T) :
    ∃ w ∈ Y, (∀ T ∈ 𝒯, w ∉ T) ∧ G.IsExceptionalTree (G.star 𝒯 w) := by
  by_contra! hcon
  have hU : (Y.filter fun v ↦ ∀ T ∈ 𝒯, v ∉ T).Nonempty := ⟨v, mem_filter.2 ⟨hv, hvT⟩⟩
  have hle := sum_star_le hY.isTree
    (fun T hT ↦ ⟨(h𝒯 T hT).isTree, (h𝒯 T hT).card_marks_add_card_boundary_le⟩) hsep hsat hU
  have hge : ∀ w ∈ Y.filter (fun v ↦ ∀ T ∈ 𝒯, v ∉ T),
      (3 : ℤ) ≤ (G.marks (G.star 𝒯 w)).card + (G.boundary (G.star 𝒯 w)).card := by
    intro w hw
    obtain ⟨hwY, hwT⟩ := mem_filter.1 hw
    have hsub := star_subset (G := G) hwY hsat
    have htree := hY.isTree.isTree_of_subset hsub
      (isConnected_star (fun T hT ↦ (h𝒯 T hT).isTree.isConnected) w)
    by_contra hlt
    exact hcon w hwY hwT ⟨⟨htree, fun u hu ↦ hY.isP1Tree.genus_eq_zero (hsub hu)⟩,
      (coe_subset.2 hsub).trans hY.subset_eligible, by omega⟩
  have hsum := sum_le_sum hge
  rw [sum_const, nsmul_eq_mul] at hsum
  have hYm := hY.card_marks_add_card_boundary_le
  have hcard := card_pos.2 hU
  omega

/-- **Every exceptional tree contains an exceptional component** (the case `𝒯 = ∅`). -/
theorem IsExceptionalTree.exists_isExceptional {Y : Finset V} (hY : G.IsExceptionalTree Y) :
    ∃ v ∈ Y, G.IsExceptional v := by
  obtain ⟨v, hv⟩ := hY.nonempty
  obtain ⟨w, hw, -, h⟩ := hY.exists_isExceptionalTree_star (𝒯 := ∅) (by simp)
    (by simp [IsSeparated]) (by simp) hv (by simp)
  rw [star_empty] at h
  exact ⟨w, hw, h⟩

/-- **Lemma B.3 (stable blow-down), main step.** Every maximal exceptional tree is a member of
every stable family. -/
theorem IsStableFamily.mem_of_maximal (hG : G.IsAnchored) {𝒯 : Finset (Finset V)}
    (h : G.IsStableFamily 𝒯) {Y : Finset V} (hY : Maximal G.IsExceptionalTree Y) : Y ∈ 𝒯 := by
  have hsat : ∀ T ∈ 𝒯, G.Meets T Y → T ⊆ Y := fun T hT hm ↦
    subset_of_meets_of_maximal hG hY (h.exceptional T hT) hm
  have hcov : ∀ v ∈ Y, ∃ T ∈ 𝒯, v ∈ T := by
    intro v hv
    by_contra! hvT
    obtain ⟨w, -, hwT, hw⟩ :=
      hY.1.exists_isExceptionalTree_star h.exceptional h.separated hsat hv hvT
    exact h.stable w hwT hw
  obtain ⟨v, hv⟩ := hY.1.nonempty
  obtain ⟨T, hT, hvT⟩ := hcov v hv
  have hTY : T ⊆ Y := hsat T hT (meets_of_mem hvT hv)
  by_cases hTeq : T = Y
  · exact hTeq ▸ hT
  exfalso
  obtain ⟨e, he, heb⟩ :=
    hY.1.isTree.isConnected.2 T hTY (h.exceptional T hT).nonempty hTeq
  obtain ⟨a, b, hab⟩ := exists_ends (G := G) e
  rw [mem_inner_of_ends hab] at he
  rcases (mem_boundary_of_ends hab).1 heb with ⟨haT, hbT⟩ | ⟨haT, hbT⟩
  · obtain ⟨T', hT', hbT'⟩ := hcov b he.2
    have hne : T ≠ T' := fun h' ↦ hbT (h' ▸ hbT')
    exact h.separated T hT T' hT' hne (meets_of_ends hab haT hbT')
  · obtain ⟨T', hT', haT'⟩ := hcov a he.1
    have hne : T ≠ T' := fun h' ↦ haT (h' ▸ haT')
    exact h.separated T hT T' hT' hne (meets_of_ends (hab.trans Sym2.eq_swap) hbT haT')

/-- **Lemma B.3 (uniqueness of the stable blow-down), combinatorial form.** The members of a
stable family are exactly the maximal exceptional trees. -/
theorem IsStableFamily.mem_iff [Fintype V] (hG : G.IsAnchored) {𝒯 : Finset (Finset V)}
    (h : G.IsStableFamily 𝒯) {T : Finset V} : T ∈ 𝒯 ↔ Maximal G.IsExceptionalTree T := by
  refine ⟨fun hT ↦ ?_, h.mem_of_maximal hG⟩
  obtain ⟨T', hTT', hT'⟩ := (h.exceptional T hT).exists_maximal
  have hT'𝒯 := h.mem_of_maximal hG hT'
  by_cases hne : T = T'
  · exact hne ▸ hT'
  · obtain ⟨v, hv⟩ := (h.exceptional T hT).nonempty
    exact absurd (meets_of_mem hv (hTT' hv)) (h.separated T hT T' hT'𝒯 hne)

/-- **Existence of the stable blow-down, combinatorial form.** The maximal exceptional trees form
a stable family. -/
theorem isStableFamily_maximal [Fintype V] (hG : G.IsAnchored) :
    G.IsStableFamily (univ.filter fun T ↦ Maximal G.IsExceptionalTree T) where
  exceptional T hT := (mem_filter.1 hT).2.1
  separated T hT T' hT' hne hm :=
    hne (eq_of_meets_of_maximal hG (mem_filter.1 hT).2 (mem_filter.1 hT').2 hm)
  stable v hv hstar := by
    obtain ⟨T, hT, hTmax⟩ := hstar.exists_maximal
    exact hv T (mem_filter.2 ⟨mem_univ T, hTmax⟩) (hT (self_mem_star _ v))

/-- **Lemma B.3: the stable blow-down is unique** (combinatorial form): two stable families of
the same incidence data coincide. -/
theorem IsStableFamily.eq [Fintype V] (hG : G.IsAnchored) {𝒯 𝒯' : Finset (Finset V)}
    (h : G.IsStableFamily 𝒯) (h' : G.IsStableFamily 𝒯') : 𝒯 = 𝒯' := by
  ext T
  rw [h.mem_iff hG, h'.mem_iff hG]

/-- Every exceptional tree is contained in a member of a stable family (it is contracted by the
stable blow-down; this is what Temkin uses in Corollary 4.4.5). -/
theorem IsStableFamily.exists_superset [Fintype V] (hG : G.IsAnchored)
    {𝒯 : Finset (Finset V)} (h : G.IsStableFamily 𝒯) {Y : Finset V}
    (hY : G.IsExceptionalTree Y) : ∃ T ∈ 𝒯, Y ⊆ T := by
  obtain ⟨T, hYT, hT⟩ := hY.exists_maximal
  exact ⟨T, h.mem_of_maximal hG hT, hYT⟩

end Stable

end IncidenceGraph

end DeJongAlterations.StableModification.CurvesField
