import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Analytic.AnalyticSubsetOpens

/-!
# Analytic subsets and irreducible components of complex spaces

An *analytic subset* of a (reduced) complex space `X` is a subset which is
locally the common zero set of finitely many holomorphic functions on `X`. In a
local embedding `(Ω, C) ≅ V ⊆ X` the holomorphic functions on `V` are locally
restrictions of holomorphic functions on `Ω` (this is how the structure sheaf of
the model is defined), so a subset of `X` is analytic if and only if near every
point it is, in some local embedding, the trace on `C` of an analytic subset of
the ambient open set `Ω`. This is the definition used here
(`SourceReducedComplexSpace.IsAnalyticSubset`); the trace property then holds
near every point of every local embedding
(`IsAnalyticSubset.exists_local_trace`).

An analytic subset is *irreducible* if it is nonempty and is not the union of
two analytic subsets different from it; the *irreducible components* of `X`
are its maximal irreducible analytic subsets (Grauert--Remmert, *Coherent
analytic sheaves*, Ch. 9, §2). These notions enter condition 1 of
`def:unibranch:L105`.

Main results:

* `IsAnalyticSubset.isClosed`: analytic subsets are closed.
* `IsAnalyticSubset.exists_local_trace`: independence of the local embedding.
* `isComplexAnalyticSubset_image_of_isAnalyticSubset_model` and
  `isAnalyticSubset_model_iff`: on an embedded model `(U, C)` the analytic
  subsets of the complex space are exactly the analytic subsets of `U`
  contained in `C`.
* `isIrreducibleComponent_model_univ_iff`: a domain `U ⊆ ℂ^n` (with its
  complex-space structure) is irreducible; it is its only irreducible component.

Original source: Appendix B (`appendix_unibranch.tex`), `def:unibranch:L105`
(condition 1). Blueprint: `claude-unibranch.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces

namespace Hironaka.Analytic.Unibranch

noncomputable section

namespace SourceReducedComplexSpace

variable (X : SourceReducedComplexSpace)

/-- Analytic subsets of a complex space: near every point, in some local
embedding `(Ω, C)`, the set is the trace on `C` of an analytic subset of `Ω`. -/
def IsAnalyticSubset (A : Set X.obj.left) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ A' : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A' ∧
      e.toPoint ⁻¹' A = Subtype.val ⁻¹' A'

/-- Irreducible analytic subsets: nonempty analytic subsets which are not the
union of two analytic subsets both different from them. -/
def IsIrreducibleAnalyticSubset (A : Set X.obj.left) : Prop :=
  X.IsAnalyticSubset A ∧ A.Nonempty ∧
    ∀ B C : Set X.obj.left, X.IsAnalyticSubset B → X.IsAnalyticSubset C →
      B ⊆ A → C ⊆ A → A = B ∪ C → A = B ∨ A = C

/-- The irreducible components of a complex space: its maximal irreducible
analytic subsets. -/
def IsIrreducibleComponent (Z : Set X.obj.left) : Prop :=
  X.IsIrreducibleAnalyticSubset Z ∧
    ∀ B : Set X.obj.left, X.IsIrreducibleAnalyticSubset B → Z ⊆ B → B = Z

variable {X}

theorem isAnalyticSubset_univ : X.IsAnalyticSubset univ := by
  intro x
  refine ⟨LocalEmbedding.ofPoint X x, LocalEmbedding.mem_range_ofPoint X x, univ,
    isComplexAnalyticSubset_univ, ?_⟩
  simp

theorem isAnalyticSubset_empty : X.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨LocalEmbedding.ofPoint X x, LocalEmbedding.mem_range_ofPoint X x, ∅,
    isComplexAnalyticSubset_empty, ?_⟩
  simp

/-- Analytic subsets of a complex space are closed. -/
theorem IsAnalyticSubset.isClosed {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) :
    IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨e, ⟨c, rfl⟩, A', hA', hpre⟩ := hA x
  have hcl : IsClosed (e.toPoint ⁻¹' A) := by
    rw [hpre]
    exact hA'.isClosed.preimage continuous_subtype_val
  have hopen : IsOpen (e.toPoint '' (e.toPoint ⁻¹' A)ᶜ) :=
    e.isOpenEmbedding_toPoint.isOpenMap _ hcl.isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨c, hx, rfl⟩) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- Independence of the local embedding: an analytic subset is, near every point
of every local embedding `(Ω, C)`, the trace of an analytic subset of an open
neighbourhood in `Ω`. -/
theorem IsAnalyticSubset.exists_local_trace {A : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (e : LocalEmbedding X) (c : e.carrier) :
    ∃ O : Opens e.ambient, c.val ∈ O ∧ ∃ A'' : Set O,
      IsComplexAnalyticSubset (n := e.dim) A'' ∧
      ∀ (y : e.carrier) (hy : y.val ∈ O), e.toPoint y ∈ A ↔ (⟨y.val, hy⟩ : O) ∈ A'' := by
  obtain ⟨e₂, hc, A', hA', hpre⟩ := hA (e.toPoint c)
  obtain ⟨O, hcO, f, hf, hfac⟩ := LocalEmbedding.exists_contMDiff_factor e.map e.overPoint e₂ c hc
  refine ⟨O, hcO, f ⁻¹' A',
    Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hA',
    ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hfac y hy
  change e.toPoint y ∈ A ↔ f ⟨y.val, hy⟩ ∈ A'
  rw [← hz]
  change e.toPoint y ∈ A ↔ z ∈ Subtype.val ⁻¹' A'
  rw [← hpre]
  change e.toPoint y ∈ A ↔ e₂.toPoint z ∈ A
  rw [hzy]
  rfl

/-- On an embedded model `(U, C)`, an analytic subset of the complex space is an
analytic subset of `U` (contained in `C`). -/
theorem isComplexAnalyticSubset_image_of_isAnalyticSubset_model {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset (n := n) C}
    {A : Set C} (hA : (sourceReducedComplexSpaceModel U C hC).IsAnalyticSubset A) :
    IsComplexAnalyticSubset (n := n) (Subtype.val '' A : Set U) := by
  apply Hironaka.AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro u
  by_cases hu : u ∈ C
  · obtain ⟨O, hcO, A'', hA'', hiff⟩ :=
      hA.exists_local_trace (LocalEmbedding.model U C hC) ⟨u, hu⟩
    refine ⟨O, hcO, ?_⟩
    have hCO : IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' C : Set O) :=
      Hironaka.AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
        hC O
    have heq : ((↑) ⁻¹' (Subtype.val '' A) : Set O) = A'' ∩ ((↑) ⁻¹' C : Set O) := by
      ext o
      constructor
      · rintro ⟨a, ha, hao⟩
        have hoC : (o : U) ∈ C := hao ▸ a.property
        refine ⟨?_, hoC⟩
        have := (hiff ⟨o.val, hoC⟩ o.property).mp (by
          rw [LocalEmbedding.model_toPoint]
          have : (⟨o.val, hoC⟩ : C) = a := Subtype.ext hao.symm
          rw [this]
          exact ha)
        exact this
      · rintro ⟨ho, hoC⟩
        have := (hiff ⟨o.val, hoC⟩ o.property).mpr ho
        rw [LocalEmbedding.model_toPoint] at this
        exact ⟨_, this, rfl⟩
    rw [heq]
    exact hA''.inter hCO
  · have hCcl : IsClosed C := hC.isClosed
    refine ⟨⟨Cᶜ, hCcl.isOpen_compl⟩, hu, ?_⟩
    have : ((↑) ⁻¹' (Subtype.val '' A) : Set (⟨Cᶜ, hCcl.isOpen_compl⟩ : Opens U)) = ∅ := by
      ext o
      simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro a _ hao
      exact o.property (hao ▸ a.property)
    rw [this]
    exact isComplexAnalyticSubset_empty

/-- Conversely, traces of analytic subsets of `U` are analytic in the model. -/
theorem isAnalyticSubset_model_of_isComplexAnalyticSubset {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset (n := n) C}
    {A' : Set U} (hA' : IsComplexAnalyticSubset (n := n) A') :
    (sourceReducedComplexSpaceModel U C hC).IsAnalyticSubset (Subtype.val ⁻¹' A' : Set C) := by
  intro x
  exact ⟨LocalEmbedding.model U C hC, ⟨x, rfl⟩, A', hA', rfl⟩

/-- On an embedded model `(U, C)`, the analytic subsets of the complex space are
exactly the analytic subsets of `U` contained in `C`. -/
theorem isAnalyticSubset_model_iff {n : ℕ}
    {U : Opens (ComplexModel n)} {C : Set U} {hC : IsComplexAnalyticSubset (n := n) C}
    (A : Set C) :
    (sourceReducedComplexSpaceModel U C hC).IsAnalyticSubset A ↔
      IsComplexAnalyticSubset (n := n) (Subtype.val '' A : Set U) := by
  refine ⟨isComplexAnalyticSubset_image_of_isAnalyticSubset_model, fun h => ?_⟩
  have := isAnalyticSubset_model_of_isComplexAnalyticSubset (hC := hC) h
  rwa [Subtype.val_injective.preimage_image] at this

/-- A domain `U ⊆ ℂ^n`, as a complex space, is irreducible. -/
theorem isIrreducibleAnalyticSubset_model_univ {n : ℕ} {U : Opens (ComplexModel n)}
    (hU : IsConnected (U : Set (ComplexModel n))) :
    (sourceReducedComplexSpaceModel U (univ : Set U) isComplexAnalyticSubset_univ).IsIrreducibleAnalyticSubset
      univ := by
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  obtain ⟨u, hu⟩ := hU.nonempty
  refine ⟨isAnalyticSubset_univ, ⟨⟨⟨u, hu⟩, trivial⟩, trivial⟩, ?_⟩
  intro B C hB hC _ _ hBC
  have hirr := isComplexAnalyticallyIrreducible_univ_of_connectedSpace (n := n) (M := U)
  have hcover : (univ : Set U) = Subtype.val '' B ∪ Subtype.val '' C := by
    ext v
    simp only [mem_univ, mem_union, mem_image, true_iff]
    have : (⟨v, trivial⟩ : (univ : Set U)) ∈ B ∪ C := by
      rw [← hBC]
      trivial
    rcases this with h | h
    · exact Or.inl ⟨_, h, rfl⟩
    · exact Or.inr ⟨_, h, rfl⟩
  have key : ∀ D : Set (univ : Set U), (univ : Set U) = Subtype.val '' D → univ = D := by
    intro D hD
    ext p
    simp only [mem_univ, true_iff]
    have : p.val ∈ Subtype.val '' D := by
      rw [← hD]
      trivial
    obtain ⟨q, hq, hqp⟩ := this
    rwa [← Subtype.ext hqp]
  rcases hirr.eq_left_or_eq_right
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_model hB)
      (isComplexAnalyticSubset_image_of_isAnalyticSubset_model hC)
      (subset_univ _) (subset_univ _) hcover with h | h
  · exact Or.inl (key B h)
  · exact Or.inr (key C h)

/-- The only irreducible component of a domain `U ⊆ ℂ^n` is `U` itself. -/
theorem isIrreducibleComponent_model_univ_iff {n : ℕ} {U : Opens (ComplexModel n)}
    (hU : IsConnected (U : Set (ComplexModel n)))
    (Z : Set (sourceReducedComplexSpaceModel U (univ : Set U)
      isComplexAnalyticSubset_univ).obj.left) :
    (sourceReducedComplexSpaceModel U (univ : Set U)
      isComplexAnalyticSubset_univ).IsIrreducibleComponent Z ↔ Z = univ := by
  constructor
  · rintro ⟨_, hmax⟩
    exact (hmax univ (isIrreducibleAnalyticSubset_model_univ hU) (subset_univ Z)).symm
  · rintro rfl
    exact ⟨isIrreducibleAnalyticSubset_model_univ hU, fun B _ hB => eq_univ_of_univ_subset hB⟩

end SourceReducedComplexSpace

end

end Hironaka.Analytic.Unibranch
