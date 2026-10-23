/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricFibre
import DeJongAlterations.StableModification.CurvesField.StableDown

/-!
# The incidence graph of a curve along a nodal subcurve (Temkin, Cor. B.2)

Let `X` be a reduced quasi-compact curve, locally of finite type over a field `k`, with finitely
many generic points and normalization `π : X̃ → X`, and let `Z ⊆ X` be a closed subset which is a
curve (every point of `Z` lies on a component of `X` contained in `Z`) such that every closed point
of `Z` is a smooth point or an ordinary double point of `X` (`X` is semi-stable along `Z`).

* `branches z`: the branches of `X` at `z` (the points of `π⁻¹(z)`), recorded as the multiset of
  the components carrying them; its cardinality is `#π⁻¹(z)` (`card_branches`) and its members
  are the components through `z` (`mem_branches`).
* `nodalGraph q hdim Z`: the incidence graph (`CurvesField.IncidenceGraph`) whose vertices are the
  points of `X` (only the generic points occur), whose edges are the ordinary double points of
  `X` on `Z`, with ends the components of the two branches, and with genus `g(v) = p_a(X̃_v)`.
* For `G` the generic points of `Z` (the components of `Z`) and `O` the other generic points:
  a double point `e ∈ Z` is an inner double point of `G` iff no branch of the normalization
  `X̃_O → X` of the other components lies over it, and a boundary point otherwise
  (`mem_inner_nodalGraph_iff`, `mem_boundary_nodalGraph_iff`); the inner and boundary double points
  together are all double points on `Z` (`card_boundary_add_card_inner_nodalGraph`); the points of
  `X̃_O` over `Z` correspond to the boundary points (`natCard_preimage_eq_card_boundary`: Temkin's
  `|x̃| = |∂Z|`, l. 4446–4447); and a subcurve `Y ⊆ G` whose union of components is connected is
  connected in the incidence graph (`isConnected_nodalGraph`).

This is the extraction of the incidence graph of `Z` with genera and boundary in the proof of
Corollary B.2 of M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4440–4450).

Blueprint: `sm-curves-fields-stabdown.tex`, `def:sm-stabdown-nodal-graph`,
`lem:sm-stabdown-graph-counts`, `lem:sm-stabdown-graph-connected`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph

set_option autoImplicit false

universe u

noncomputable section

section Pair

variable {α : Type*}

/-- The unordered pair of the elements of a multiset of cardinality two. -/
def sym2OfCardEqTwo (s : Multiset α) (h : Multiset.card s = 2) : Sym2 α :=
  s((Multiset.card_eq_two.1 h).choose, (Multiset.card_eq_two.1 h).choose_spec.choose)

lemma mem_sym2OfCardEqTwo {s : Multiset α} (h : Multiset.card s = 2) (a : α) :
    a ∈ sym2OfCardEqTwo s h ↔ a ∈ s := by
  have hs := (Multiset.card_eq_two.1 h).choose_spec.choose_spec
  conv_rhs => rw [hs]
  simp [sym2OfCardEqTwo]

end Pair

section Branches

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)]

/-- The number of branches at `z` of the component with generic point `v`: the number of points
over `z` of the normalization `X̃_v → X` of that component. -/
def branchCount (v z : X) : ℕ :=
  Nat.card ↥(normalizationPointsMap ({v} : Set X) ⁻¹' {z})

variable (X) in
/-- The generic points of `X` as a finset. -/
def genericFinset : Finset X :=
  (Set.toFinite (genericPoints X)).toFinset

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
lemma coe_genericFinset : (genericFinset X : Set X) = genericPoints X :=
  Set.Finite.coe_toFinset _

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
lemma mem_genericFinset {v : X} : v ∈ genericFinset X ↔ v ∈ genericPoints X :=
  Set.Finite.mem_toFinset _

/-- The branches of `X` at `z` (the points of the normalization over `z`), each recorded by the
component carrying it. -/
def branches (z : X) : Multiset X :=
  ∑ v ∈ genericFinset X, branchCount v z • ({v} : Multiset X)

omit [IsAffineHom (pullback.diagonal (terminal.from X))] [Finite (genericPoints X)] in
/-- A generic point lying in the closure of a point is that point. -/
lemma eq_of_mem_closure_of_mem_genericPoints {v z : X} (hz : z ∈ genericPoints X)
    (h : z ∈ closure {v}) : v = z :=
  (mem_genericPoints_iff z).1 hz v (specializes_iff_mem_closure.2 h)

variable {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

omit [Finite (genericPoints X)] in
include q in
/-- `#π_S⁻¹(z) = ∑_{v ∈ T} #π_v⁻¹(z)` for a finite set `S = T` of points. -/
lemma natCard_fiber_eq_sum_of_eq (S : Set X) [Finite S] (T : Finset X) (hST : S = T) (z : X) :
    Nat.card ↥(normalizationPointsMap S ⁻¹' {z}) = ∑ v ∈ T, branchCount v z := by
  subst hST
  exact natCard_fiber_normalizationPoints_eq_sum q T z

omit [Finite (genericPoints X)] in
include q in
/-- The component of `v` has a branch at `z` iff `z` lies on it. -/
lemma branchCount_ne_zero_iff (v z : X) : branchCount v z ≠ 0 ↔ z ∈ closure {v} := by
  have : IsFinite (normalizationPointsMap ({v} : Set X)) :=
    isFinite_normalizationPointsMap (S := ({v} : Set X)) q
  have hfin : Finite ↥(normalizationPointsMap ({v} : Set X) ⁻¹' {z}) :=
    ((normalizationPointsMap ({v} : Set X)).finite_preimage_singleton z).to_subtype
  rw [mem_closure_iff_nonempty_fiber q v z, branchCount, Nat.card_ne_zero]
  constructor
  · rintro ⟨h, -⟩
    exact Set.nonempty_coe_sort.1 h
  · intro h
    exact ⟨h.to_subtype, hfin⟩

omit [Finite (genericPoints X)] in
include q in
/-- The normalization in a finite set `S` of points has a point over `z` iff `z` lies on the
closure of a point of `S`. -/
lemma nonempty_fiber_iff (S : Set X) [Finite S] (z : X) :
    (normalizationPointsMap S ⁻¹' {z}).Nonempty ↔ ∃ v ∈ S, z ∈ closure {v} := by
  have : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap (S := S) q
  have hfin : Finite ↥(normalizationPointsMap S ⁻¹' {z}) :=
    ((normalizationPointsMap S).finite_preimage_singleton z).to_subtype
  have hS := Set.Finite.coe_toFinset (Set.toFinite S)
  have hsum := natCard_fiber_eq_sum_of_eq q S _ hS.symm z
  have key : (normalizationPointsMap S ⁻¹' {z}).Nonempty ↔
      Nat.card ↥(normalizationPointsMap S ⁻¹' {z}) ≠ 0 := by
    rw [Nat.card_ne_zero]
    exact ⟨fun h => ⟨h.to_subtype, hfin⟩, fun h => Set.nonempty_coe_sort.1 h.1⟩
  rw [key, hsum, Ne, Finset.sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨v, hv, hne⟩
    exact ⟨v, (Set.Finite.mem_toFinset _).1 hv, (branchCount_ne_zero_iff q v z).1 hne⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, (Set.Finite.mem_toFinset _).2 hv, (branchCount_ne_zero_iff q v z).2 hz⟩

include q in
/-- The number of branches at `z` is the number of points of the normalization over `z`. -/
lemma card_branches (z : X) :
    Multiset.card (branches z) = Nat.card ↥(normalizationPointsMap (genericPoints X) ⁻¹' {z}) := by
  rw [natCard_fiber_eq_sum_of_eq q (genericPoints X) (genericFinset X) coe_genericFinset.symm z,
    branches, Multiset.card_sum]
  simp [Multiset.card_nsmul]

include q in
/-- The components carrying the branches at `z` are the components through `z`. -/
lemma mem_branches (v z : X) : v ∈ branches z ↔ v ∈ genericPoints X ∧ z ∈ closure {v} := by
  rw [branches, Multiset.mem_sum]
  constructor
  · rintro ⟨w, hw, hvw⟩
    rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hvw
    obtain ⟨hne, rfl⟩ := hvw
    exact ⟨mem_genericFinset.1 hw, (branchCount_ne_zero_iff q v z).1 hne⟩
  · rintro ⟨hv, hz⟩
    exact ⟨v, mem_genericFinset.2 hv,
      Multiset.mem_nsmul.2 ⟨(branchCount_ne_zero_iff q v z).2 hz, Multiset.mem_singleton_self v⟩⟩

include q in
/-- Two distinct components through `z` give at least two branches at `z`. -/
lemma two_le_natCard_fiber {z v₁ v₂ : X} (h₁ : v₁ ∈ genericPoints X) (h₂ : v₂ ∈ genericPoints X)
    (hne : v₁ ≠ v₂) (hz₁ : z ∈ closure {v₁}) (hz₂ : z ∈ closure {v₂}) :
    2 ≤ Nat.card ↥(normalizationPointsMap (genericPoints X) ⁻¹' {z}) := by
  classical
  rw [natCard_fiber_eq_sum_of_eq q (genericPoints X) (genericFinset X) coe_genericFinset.symm z]
  have hsub : ({v₁, v₂} : Finset X) ⊆ genericFinset X := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact mem_genericFinset.2 h₁
    · exact mem_genericFinset.2 h₂
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  rw [Finset.sum_pair hne]
  have a₁ := Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q v₁ z).2 hz₁)
  have a₂ := Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q v₂ z).2 hz₂)
  omega

end Branches

section Subcurve

/-! ### A subcurve `Z` and its complement

`Z` is a closed subset, `G` the finset of generic points of `X` in `Z` (the components of `Z`) and
`O` the set of the other generic points. -/

variable {X : Scheme.{u}} {Z : Set X} (hZ : IsClosed Z) {G : Finset X}
  (hG : (G : Set X) = genericPoints X ∩ Z) {O : Set X} (hO : O = genericPoints X \ Z)

include hZ hG in
/-- The components in `G` lie in `Z`. -/
lemma closure_subset_of_mem {v : X} (hv : v ∈ G) : closure {v} ⊆ Z := by
  have : v ∈ (G : Set X) := hv
  rw [hG] at this
  exact closure_minimal (Set.singleton_subset_iff.2 this.2) hZ

include hG hO in
/-- A generic point not in `G` is in `O`. -/
lemma mem_outer_of_not_mem {v : X} (hv : v ∈ genericPoints X) (hvG : v ∉ G) : v ∈ O := by
  rw [hO]
  refine ⟨hv, fun hvZ => hvG ?_⟩
  have : v ∈ (G : Set X) := by rw [hG]; exact ⟨hv, hvZ⟩
  exact this

include hG hO in
/-- `G` and `O` are disjoint. -/
lemma not_mem_of_mem_outer {v : X} (hv : v ∈ O) : v ∉ G := by
  intro hvG
  have : v ∈ (G : Set X) := hvG
  rw [hG] at this
  rw [hO] at hv
  exact hv.2 this.2

include hG hO in
lemma genericPoints_eq_union : genericPoints X = O ∪ (G : Set X) := by
  rw [hO, hG]
  ext v
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

include hG hO in
lemma disjoint_outer : Disjoint O (G : Set X) := by
  rw [Set.disjoint_left]
  exact fun v hv => not_mem_of_mem_outer hG hO hv

end Subcurve

section Graph

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (hdim : topologicalKrullDim X ≤ 1)

omit [CompactSpace X] in
include hdim in
/-- An ordinary double point has two branches. -/
lemma card_branches_of_mem_nodesIn {Z : Set X} {z : X} (hz : z ∈ nodesIn q Z) :
    Multiset.card (branches z) = 2 := by
  rw [card_branches q z]
  exact natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hz.2.1 hz.2.2.1 hz.2.2.2

/-- **The incidence graph of `X` along `Z`** (Temkin, Cor. B.2, l. 4440–4450): the vertices are
the points of `X` (only generic points occur as ends), the edges are the ordinary double points of
`X` on `Z`, the ends of a double point are the components carrying its two branches, the genus of
a component is `g(v) = p_a(X̃_v)` (`componentGenus`, truncated at `0`), there are no marked
points, and the eligible components are those in `Z`. -/
def nodalGraph (Z : Set X) : IncidenceGraph X (nodesIn q Z) Empty where
  ends e := sym2OfCardEqTwo (branches e.1) (card_branches_of_mem_nodesIn q hdim e.2)
  genus v := (componentGenus (structureCoeff q) v).toNat
  mark := Empty.elim
  eligible := Z ∩ genericPoints X

/-- The ends of a double point are the components through it. -/
lemma mem_nodalGraph_ends {Z : Set X} (e : nodesIn q Z) (v : X) :
    v ∈ (nodalGraph q hdim Z).ends e ↔ v ∈ genericPoints X ∧ e.1 ∈ closure {v} :=
  (mem_sym2OfCardEqTwo (card_branches_of_mem_nodesIn q hdim e.2) v).trans (mem_branches q v e.1)

lemma nodalGraph_genus (Z : Set X) (v : X) :
    (nodalGraph q hdim Z).genus v = (componentGenus (structureCoeff q) v).toNat :=
  rfl

/-! ### The subcurve `Z` and its complement

In the rest of this file `Z` is closed, `G` is the finset of generic points of `X` in `Z`, `O` the
set of the other generic points, every point of `Z` lies on a component in `G`, and every closed
point of `Z` is a smooth point or an ordinary double point. -/

variable {Z : Set X} (hZ : IsClosed Z) {G : Finset X} (hG : (G : Set X) = genericPoints X ∩ Z)
  {O : Set X} [Finite O] (hO : O = genericPoints X \ Z)
  (hcurve : ∀ z ∈ Z, ∃ v ∈ G, z ∈ closure {v})
  (hnodal : ∀ y ∈ Z, IsClosed {y} →
    DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y)

include hdim hnodal in
/-- **A point of `Z` on two distinct components is a double point.** -/
lemma mem_nodesIn_of_mem_closure {z v₁ v₂ : X} (hz : z ∈ Z) (h₁ : v₁ ∈ genericPoints X)
    (h₂ : v₂ ∈ genericPoints X) (hne : v₁ ≠ v₂) (hz₁ : z ∈ closure {v₁})
    (hz₂ : z ∈ closure {v₂}) : z ∈ nodesIn q Z := by
  have hzg : z ∉ genericPoints X := fun hg => hne
    ((eq_of_mem_closure_of_mem_genericPoints hg hz₁).trans
      (eq_of_mem_closure_of_mem_genericPoints hg hz₂).symm)
  have hzc := isClosed_singleton_of_not_mem_genericPoints hdim hzg
  refine ⟨hz, hzc, hzg, ?_⟩
  have h2 := two_le_natCard_fiber q h₁ h₂ hne hz₁ hz₂
  rcases hnodal z hz hzc with hsm | hn
  · have : IsReduced X := inferInstance
    have : LocallyOfFinitePresentation q := by
      have := isLocallyNoetherian_of_locallyOfFiniteType q
      infer_instance
    rw [natCard_fiber_eq_one_of_isSmoothAt q hdim z hzc hzg hsm] at h2
    omega
  · exact hn

/-- At a double point with two distinct components `v₁ ∋ z`, `v₂ ∋ z`, the ends are `v₁, v₂`. -/
lemma nodalGraph_ends_eq {v₁ v₂ : X} (e : nodesIn q Z) (h₁ : v₁ ∈ genericPoints X)
    (h₂ : v₂ ∈ genericPoints X) (hne : v₁ ≠ v₂) (hz₁ : e.1 ∈ closure {v₁})
    (hz₂ : e.1 ∈ closure {v₂}) : (nodalGraph q hdim Z).ends e = s(v₁, v₂) :=
  (Sym2.mem_and_mem_iff hne).1 ⟨(mem_nodalGraph_ends q hdim e v₁).2 ⟨h₁, hz₁⟩,
    (mem_nodalGraph_ends q hdim e v₂).2 ⟨h₂, hz₂⟩⟩

open scoped Classical in
include hG hO hcurve in
/-- **Boundary double points**: a double point `e ∈ Z` is a boundary point of `G` iff the
normalization `X̃_O → X` of the other components has a point over `e`. -/
lemma mem_boundary_nodalGraph_iff [Fintype (nodesIn q Z)] (e : nodesIn q Z) :
    e ∈ (nodalGraph q hdim Z).boundary G ↔ (normalizationPointsMap O ⁻¹' {e.1}).Nonempty := by
  rw [mem_boundary, nonempty_fiber_iff q O e.1]
  obtain ⟨v', hv'G, hv'⟩ := hcurve e.1 e.2.1
  have hv'g : v' ∈ genericPoints X := by
    have : v' ∈ (G : Set X) := hv'G
    rw [hG] at this
    exact this.1
  constructor
  · rintro ⟨-, v, hv, hvG⟩
    obtain ⟨hvg, hvz⟩ := (mem_nodalGraph_ends q hdim e v).1 hv
    exact ⟨v, mem_outer_of_not_mem hG hO hvg hvG, hvz⟩
  · rintro ⟨v, hvO, hvz⟩
    have hvg : v ∈ genericPoints X := by rw [hO] at hvO; exact hvO.1
    exact ⟨⟨v', (mem_nodalGraph_ends q hdim e v').2 ⟨hv'g, hv'⟩, hv'G⟩,
      ⟨v, (mem_nodalGraph_ends q hdim e v).2 ⟨hvg, hvz⟩, not_mem_of_mem_outer hG hO hvO⟩⟩

include hG hO in
/-- **Inner double points**: a double point `e ∈ Z` is an inner point of `G` iff the
normalization `X̃_O → X` of the other components has no point over `e`. -/
lemma mem_inner_nodalGraph_iff [DecidableEq X] [Fintype (nodesIn q Z)] (e : nodesIn q Z) :
    e ∈ (nodalGraph q hdim Z).inner G ↔ ¬ (normalizationPointsMap O ⁻¹' {e.1}).Nonempty := by
  rw [mem_inner, nonempty_fiber_iff q O e.1]
  constructor
  · rintro h ⟨v, hvO, hvz⟩
    have hvg : v ∈ genericPoints X := by rw [hO] at hvO; exact hvO.1
    exact not_mem_of_mem_outer hG hO hvO (h v ((mem_nodalGraph_ends q hdim e v).2 ⟨hvg, hvz⟩))
  · intro h v hv
    obtain ⟨hvg, hvz⟩ := (mem_nodalGraph_ends q hdim e v).1 hv
    by_contra hvG
    exact h ⟨v, mem_outer_of_not_mem hG hO hvg hvG, hvz⟩

open scoped Classical in
include hG hO hcurve in
/-- **The double points on `Z` are the inner and the boundary double points of `G`**:
`#∂G + #inner(G) = #(double points of X on Z)`. -/
lemma card_boundary_add_card_inner_nodalGraph [Fintype (nodesIn q Z)] :
    ((nodalGraph q hdim Z).boundary G).card + ((nodalGraph q hdim Z).inner G).card =
      (nodesIn q Z).ncard := by
  have hdisj : Disjoint ((nodalGraph q hdim Z).boundary G) ((nodalGraph q hdim Z).inner G) := by
    rw [Finset.disjoint_left]
    intro e hb hi
    exact (mem_inner_nodalGraph_iff q hdim hG hO e).1 hi
      ((mem_boundary_nodalGraph_iff q hdim hG hO hcurve e).1 hb)
  have hunion : (nodalGraph q hdim Z).boundary G ∪ (nodalGraph q hdim Z).inner G =
      Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : (normalizationPointsMap O ⁻¹' {e.1}).Nonempty
    · exact Or.inl ((mem_boundary_nodalGraph_iff q hdim hG hO hcurve e).2 h)
    · exact Or.inr ((mem_inner_nodalGraph_iff q hdim hG hO e).2 h)
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]

include hdim hG hO hcurve hnodal in
/-- **A point of `X̃_O` over `Z` lies over a double point, alone in its fibre.** -/
lemma outer_fiber {z : X} (hz : z ∈ Z) (hne : (normalizationPointsMap O ⁻¹' {z}).Nonempty) :
    z ∈ nodesIn q Z ∧ Nat.card ↥(normalizationPointsMap O ⁻¹' {z}) = 1 := by
  obtain ⟨v, hvO, hvz⟩ := (nonempty_fiber_iff q O z).1 hne
  obtain ⟨v', hv'G, hv'z⟩ := hcurve z hz
  have hvg : v ∈ genericPoints X := by rw [hO] at hvO; exact hvO.1
  have hv'g : v' ∈ genericPoints X := by
    have : v' ∈ (G : Set X) := hv'G
    rw [hG] at this
    exact this.1
  have hvv' : v ≠ v' := fun h => not_mem_of_mem_outer hG hO hvO (h ▸ hv'G)
  have hnode := mem_nodesIn_of_mem_closure q hdim hnodal hz hvg hv'g hvv' hvz hv'z
  refine ⟨hnode, ?_⟩
  have h2 := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hnode.2.1
    hnode.2.2.1 hnode.2.2.2
  rw [natCard_fiber_normalizationPoints_union q (genericPoints X) O (G : Set X)
    (genericPoints_eq_union hG hO) (disjoint_outer hG hO) z,
    natCard_fiber_eq_sum_of_eq q (G : Set X) G rfl z] at h2
  have hG1 : 1 ≤ ∑ w ∈ G, branchCount w z :=
    le_trans (Nat.pos_of_ne_zero ((branchCount_ne_zero_iff q v' z).2 hv'z))
      (Finset.single_le_sum (f := fun w => branchCount w z) (fun _ _ => Nat.zero_le _) hv'G)
  have : Finite ↥(normalizationPointsMap O ⁻¹' {z}) := by
    have : IsFinite (normalizationPointsMap O) := isFinite_normalizationPointsMap (S := O) q
    exact ((normalizationPointsMap O).finite_preimage_singleton z).to_subtype
  have hO1 : 0 < Nat.card ↥(normalizationPointsMap O ⁻¹' {z}) :=
    Nat.card_pos_iff.2 ⟨hne.to_subtype, inferInstance⟩
  omega

open scoped Classical in
include hdim hG hO hcurve hnodal in
/-- **The branch count `|x̃| = |∂Z|`** (Temkin, Cor. B.2, l. 4446–4447): the points of the
normalization `X̃_O → X` of the components not in `Z` lying over `Z` correspond to the boundary
double points of `G`. -/
lemma natCard_preimage_eq_card_boundary [Fintype (nodesIn q Z)] :
    Nat.card ↥(normalizationPointsMap O ⁻¹' Z) = ((nodalGraph q hdim Z).boundary G).card := by
  let φ : ↥(normalizationPointsMap O ⁻¹' Z) → ↥((nodalGraph q hdim Z).boundary G) := fun w =>
    ⟨⟨normalizationPointsMap O w.1, (outer_fiber q hdim hG hO hcurve hnodal w.2
        ⟨w.1, rfl⟩).1⟩,
      (mem_boundary_nodalGraph_iff q hdim hG hO hcurve _).2 ⟨w.1, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun w₁ w₂ h => ?_, fun e => ?_⟩
    · have h' : normalizationPointsMap O w₁.1 = normalizationPointsMap O w₂.1 :=
        congrArg (fun e : ↥((nodalGraph q hdim Z).boundary G) => e.1.1) h
      have h1 := (outer_fiber q hdim hG hO hcurve hnodal w₁.2 ⟨w₁.1, rfl⟩).2
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h1
      have : (⟨w₁.1, rfl⟩ : ↥(normalizationPointsMap O ⁻¹' {normalizationPointsMap O w₁.1})) =
          ⟨w₂.1, h'.symm⟩ := Subsingleton.elim _ _
      have h'' := congrArg Subtype.val this
      exact Subtype.ext h''
    · obtain ⟨w, hw⟩ := (mem_boundary_nodalGraph_iff q hdim hG hO hcurve e.1).1 e.2
      have hwZ : w ∈ normalizationPointsMap O ⁻¹' Z := by
        change normalizationPointsMap O w ∈ Z
        rw [show normalizationPointsMap O w = e.1.1 from hw]
        exact e.1.2.1
      refine ⟨⟨w, hwZ⟩, Subtype.ext (Subtype.ext ?_)⟩
      exact hw
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

open scoped Classical in
include hZ hG hdim hnodal in
/-- **Connected subcurves are connected in the incidence graph**: if `Y ⊆ G` is nonempty and the
union `⋃_{v ∈ Y} closure {v}` of its components is preconnected, then `Y` is connected in the
incidence graph (every nonempty proper part `W ⊊ Y` meets `Y ∖ W` in a double point, which has one
branch on `W` and one on `Y ∖ W`). -/
lemma isConnected_nodalGraph [Fintype (nodesIn q Z)] {Y : Finset X} (hYG : Y ⊆ G)
    (hYne : Y.Nonempty) (hY : _root_.IsPreconnected (⋃ v ∈ Y, closure ({v} : Set X))) :
    (nodalGraph q hdim Z).IsConnected Y := by
  refine ⟨hYne, fun W hWY hWne hWY' => ?_⟩
  have hgen : ∀ v ∈ G, v ∈ genericPoints X := fun v hv => by
    have : v ∈ (G : Set X) := hv
    rw [hG] at this
    exact this.1
  have hdne : (Y \ W).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h => hWY' (Finset.Subset.antisymm hWY h)
  obtain ⟨z, hzY, hzW, hzW'⟩ := isPreconnected_closed_iff.1 hY (⋃ v ∈ W, closure ({v} : Set X))
    (⋃ v ∈ Y \ W, closure ({v} : Set X))
    (isClosed_biUnion_finset fun _ _ => isClosed_closure)
    (isClosed_biUnion_finset fun _ _ => isClosed_closure)
    (by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨v, hv, hzv⟩ := hz
      by_cases hvW : v ∈ W
      · exact Or.inl (Set.mem_biUnion hvW hzv)
      · exact Or.inr (Set.mem_biUnion (Finset.mem_sdiff.2 ⟨hv, hvW⟩) hzv))
    (by
      obtain ⟨v, hv⟩ := hWne
      exact ⟨v, Set.mem_biUnion (hWY hv) (subset_closure rfl),
        Set.mem_biUnion hv (subset_closure rfl)⟩)
    (by
      obtain ⟨v, hv⟩ := hdne
      exact ⟨v, Set.mem_biUnion (Finset.mem_sdiff.1 hv).1 (subset_closure rfl),
        Set.mem_biUnion hv (subset_closure rfl)⟩)
  simp only [Set.mem_iUnion] at hzW hzW'
  obtain ⟨v₁, hv₁, hz₁⟩ := hzW
  obtain ⟨v₂, hv₂, hz₂⟩ := hzW'
  obtain ⟨hv₂Y, hv₂W⟩ := Finset.mem_sdiff.1 hv₂
  have hne : v₁ ≠ v₂ := fun h => hv₂W (h ▸ hv₁)
  have hzZ : z ∈ Z := closure_subset_of_mem hZ hG (hYG (hWY hv₁)) hz₁
  have hnode := mem_nodesIn_of_mem_closure q hdim hnodal hzZ (hgen v₁ (hYG (hWY hv₁)))
    (hgen v₂ (hYG hv₂Y)) hne hz₁ hz₂
  let e : nodesIn q Z := ⟨z, hnode⟩
  have hends := nodalGraph_ends_eq q hdim e (hgen v₁ (hYG (hWY hv₁))) (hgen v₂ (hYG hv₂Y))
    hne hz₁ hz₂
  refine ⟨e, (mem_inner_of_ends hends).2 ⟨hWY hv₁, hv₂Y⟩, (mem_boundary_of_ends hends).2 ?_⟩
  exact Or.inl ⟨hv₁, hv₂W⟩

end Graph

end

end DeJongAlterations.StableModification.CurvesField.Genus
