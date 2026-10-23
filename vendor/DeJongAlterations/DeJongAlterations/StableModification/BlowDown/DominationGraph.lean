/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.Trees

/-!
# Incidence data under change of edge set and marks (for Temkin, Corollary 4.4.3)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Corollary 4.4.3 (`sepcloscor`, T:3145–3149): the fibres of the two dominations `h' : C̄ → C'` and
`h : C̄ → C_st` are compared inside **one** incidence graph of the fibre `C̄_s`. The stability
criterion (`BlowDown.stability_criterion_fibre`) describes the fibres of `h'` in the incidence
graph of `C̄_s` along the locus contracted by `h'`, and those of `h` along the locus contracted by
`h`, both without marks; Corollary 4.4.3 needs them in the incidence graph along the locus
contracted to points of `C`, with the marks of `C̄`. This file provides the combinatorial
bookkeeping (namespace `CurvesField.IncidenceGraph`, file `CurvesField/Trees.lean`):

* `transfer`: an injection of edge sets compatible with the ends and the genera, onto all edges
  with an end in a set `W` of components, identifies the inner and boundary double points of every
  `Y ⊆ W`, hence connectedness, trees and `ℙ¹`-trees (`inner_eq_map_of_transfer`,
  `boundary_eq_map_of_transfer`, `isP1Tree_iff_of_transfer`);
* `withMarks`: the same incidence data with another set of marked points;
* `exists_superset_of_finite_eligible`: Lemma B.3 in the form "every exceptional tree lies in a
  member of a stable family" (`IsStableFamily.exists_superset`) for incidence data whose set of
  vertices is infinite but whose eligible components are finite (the vertices of the incidence
  graph of a curve are all its points).

Blueprint: `sm-blow-down-domination.tex`, `lem:sm-dom-graph-transfer`.
-/

namespace DeJongAlterations.StableModification.BlowDown.Domination

open Finset
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅

section Transfer

variable {V : Type u₁} {E₁ : Type u₂} {E₂ : Type u₃} {M₁ : Type u₄} {M₂ : Type u₅}
  [DecidableEq V] [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]
  [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
  {G₁ : IncidenceGraph V E₁ M₁} {G₂ : IncidenceGraph V E₂ M₂}

/-- A *transfer* of incidence data along a set `W` of components: an injection `ι : E₁ → E₂` of
double points compatible with the ends and the genera on `W`, whose image contains every double
point of `G₂` with a branch on `W`. -/
structure IsTransfer (G₁ : IncidenceGraph V E₁ M₁) (G₂ : IncidenceGraph V E₂ M₂) (ι : E₁ → E₂)
    (W : Finset V) : Prop where
  injective : Function.Injective ι
  ends_eq : ∀ e, G₂.ends (ι e) = G₁.ends e
  genus_eq : ∀ v ∈ W, G₂.genus v = G₁.genus v
  surj : ∀ e₂, (∃ v ∈ G₂.ends e₂, v ∈ W) → ∃ e₁, ι e₁ = e₂

variable {ι : E₁ → E₂} {W : Finset V}

/-- Under a transfer, the inner double points of `Y ⊆ W` correspond. -/
theorem inner_eq_map_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    G₂.inner Y = (G₁.inner Y).map ⟨ι, hι.injective⟩ := by
  ext e₂
  simp only [mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro he
    obtain ⟨a, b, hab⟩ := exists_ends (G := G₂) e₂
    have ha : a ∈ Y := (mem_inner.1 he) a (by simp [hab])
    obtain ⟨e₁, rfl⟩ := hι.surj e₂ ⟨a, by simp [hab], hY ha⟩
    refine ⟨e₁, ?_, rfl⟩
    rw [mem_inner, ← hι.ends_eq]
    exact mem_inner.1 he
  · rintro ⟨e₁, he₁, rfl⟩
    rw [mem_inner, hι.ends_eq]
    exact mem_inner.1 he₁

/-- Under a transfer, the boundary double points of `Y ⊆ W` correspond. -/
theorem boundary_eq_map_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    G₂.boundary Y = (G₁.boundary Y).map ⟨ι, hι.injective⟩ := by
  ext e₂
  simp only [mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro he
    obtain ⟨⟨a, ha, haY⟩, -⟩ := mem_boundary.1 he
    obtain ⟨e₁, rfl⟩ := hι.surj e₂ ⟨a, ha, hY haY⟩
    refine ⟨e₁, ?_, rfl⟩
    rw [mem_boundary, ← hι.ends_eq]
    exact mem_boundary.1 he
  · rintro ⟨e₁, he₁, rfl⟩
    rw [mem_boundary, hι.ends_eq]
    exact mem_boundary.1 he₁

theorem card_inner_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    (G₂.inner Y).card = (G₁.inner Y).card := by
  rw [inner_eq_map_of_transfer hι hY, card_map]

theorem card_boundary_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    (G₂.boundary Y).card = (G₁.boundary Y).card := by
  rw [boundary_eq_map_of_transfer hι hY, card_map]

/-- Under a transfer, connectedness of `Y ⊆ W` is the same in both incidence data. -/
theorem isConnected_iff_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    G₂.IsConnected Y ↔ G₁.IsConnected Y := by
  unfold IsConnected
  refine and_congr Iff.rfl (forall₂_congr fun X hXY ↦ imp_congr Iff.rfl (imp_congr Iff.rfl ?_))
  rw [inner_eq_map_of_transfer hι hY, boundary_eq_map_of_transfer hι (hXY.trans hY)]
  simp only [mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨e₁, he₁, rfl⟩, ⟨e₁', he₁', he⟩⟩
    rw [hι.injective he] at he₁'
    exact ⟨e₁, he₁, he₁'⟩
  · rintro ⟨e₁, he₁, he₁'⟩
    exact ⟨ι e₁, ⟨e₁, he₁, rfl⟩, ⟨e₁, he₁', rfl⟩⟩

theorem isTree_iff_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    G₂.IsTree Y ↔ G₁.IsTree Y := by
  unfold IsTree
  rw [isConnected_iff_of_transfer hι hY, card_inner_of_transfer hι hY]

/-- Under a transfer, `Y ⊆ W` is a `ℙ¹`-tree in one incidence data iff in the other. -/
theorem isP1Tree_iff_of_transfer (hι : IsTransfer G₁ G₂ ι W) {Y : Finset V} (hY : Y ⊆ W) :
    G₂.IsP1Tree Y ↔ G₁.IsP1Tree Y := by
  unfold IsP1Tree
  rw [isTree_iff_of_transfer hι hY]
  refine and_congr Iff.rfl (forall₂_congr fun v hv ↦ ?_)
  rw [hι.genus_eq v (hY hv)]

end Transfer

section Marks

variable {V : Type u₁} {E : Type u₂} {M₀ : Type u₃} {M : Type u₄}

/-- The incidence data `G` with the marked points replaced by `M`, through `mark`. -/
def withMarks (G : IncidenceGraph V E M₀) (mark : M → V) : IncidenceGraph V E M where
  ends := G.ends
  genus := G.genus
  mark := mark
  eligible := G.eligible

variable (G : IncidenceGraph V E M₀) (mark : M → V)

@[simp] theorem withMarks_ends : (withMarks G mark).ends = G.ends := rfl

@[simp] theorem withMarks_genus : (withMarks G mark).genus = G.genus := rfl

@[simp] theorem withMarks_eligible : (withMarks G mark).eligible = G.eligible := rfl

@[simp] theorem withMarks_mark : (withMarks G mark).mark = mark := rfl

/-- Changing the marks is a transfer along every set of components (the identity of edges). -/
theorem isTransfer_withMarks (W : Finset V) : IsTransfer G (withMarks G mark) id W where
  injective := Function.injective_id
  ends_eq _ := rfl
  genus_eq _ _ := rfl
  surj e _ := ⟨e, rfl⟩

end Marks

section Maximal

variable {V : Type u₁} {E : Type u₂} {M : Type u₃} [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype M] [DecidableEq M] {G : IncidenceGraph V E M}

/-- With finitely many eligible components there are finitely many exceptional trees. -/
theorem finite_setOf_isExceptionalTree (hfin : G.eligible.Finite) :
    {Y : Finset V | G.IsExceptionalTree Y}.Finite := by
  refine (hfin.toFinset.powerset : Finset (Finset V)).finite_toSet.subset fun Y hY ↦ ?_
  simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Set.Finite.coe_toFinset]
  exact hY.subset_eligible

/-- Every exceptional tree is contained in a maximal one, if there are finitely many eligible
components. -/
theorem IsExceptionalTree.exists_maximal_of_finite (hfin : G.eligible.Finite) {Y : Finset V}
    (hY : G.IsExceptionalTree Y) : ∃ T, Y ⊆ T ∧ Maximal G.IsExceptionalTree T :=
  (finite_setOf_isExceptionalTree hfin).exists_le_maximal hY

/-- **Lemma B.3, final form** (Temkin, App. B, T:4476–4486; `IsStableFamily.exists_superset`
for incidence data with finitely many eligible components): for anchored incidence data, every
exceptional tree is contained in a member of any stable family. -/
theorem exists_superset_of_finite_eligible (hG : G.IsAnchored) (hfin : G.eligible.Finite)
    {𝒯 : Finset (Finset V)} (h : G.IsStableFamily 𝒯) {Y : Finset V}
    (hY : G.IsExceptionalTree Y) : ∃ T ∈ 𝒯, Y ⊆ T := by
  obtain ⟨T, hYT, hT⟩ := IsExceptionalTree.exists_maximal_of_finite hfin hY
  exact ⟨T, h.mem_of_maximal hG hT, hYT⟩

end Maximal

end DeJongAlterations.StableModification.BlowDown.Domination
