/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.NilradicalCoverEngine
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Original reduction points and canonical generic components

The actual nilradical closed immersion internally supplies its point homeomorphism, closed and
generic point correspondence, actual generic lifts, and native reducedness of its closed source.

Blueprint: `reduction-canonical-geometry.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace DeJongAlterations.StableModificationBridge.ReductionCanonicalGeometry

noncomputable section

def homeomorph (X : Scheme.{u}) : X.nilradical.subscheme ≃ₜ X :=
  X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (NilradicalCoverEngine.reduction_surjective X)

@[simp]
theorem homeomorph_apply (X : Scheme.{u}) (x : X.nilradical.subscheme) :
    homeomorph X x = X.nilradical.subschemeι x := rfl

theorem isClosed_singleton_iff (X : Scheme.{u}) (x : X.nilradical.subscheme) :
    IsClosed ({x} : Set X.nilradical.subscheme) ↔ IsClosed ({X.nilradical.subschemeι x} : Set X) := by
  simpa only [Set.image_singleton] using
    (X.nilradical.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed (s := {x}))

private theorem genericPoint_image {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {x : A} (hx : x ∈ genericPoints A) : e x ∈ genericPoints B := by
  have h := image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
    (fun y => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible) e.surjective hx
  change closure {e x} ∈ irreducibleComponents B
  simpa only [e.image_closure, Set.image_singleton] using h

theorem mem_genericPoints_iff (X : Scheme.{u}) (x : X.nilradical.subscheme) :
    x ∈ genericPoints X.nilradical.subscheme ↔ X.nilradical.subschemeι x ∈ genericPoints X := by
  constructor
  · exact genericPoint_image (homeomorph X)
  · intro hx
    have h := genericPoint_image (homeomorph X).symm hx
    simpa only [← homeomorph_apply X x, Homeomorph.symm_apply_apply] using h

theorem exists_genericPoint_lift (X : Scheme.{u}) (x : X) (hx : x ∈ genericPoints X) :
    ∃ y : X.nilradical.subscheme, X.nilradical.subschemeι y = x ∧ y ∈ genericPoints X.nilradical.subscheme := by
  refine ⟨(homeomorph X).symm x, (homeomorph X).apply_symm_apply x, ?_⟩
  apply (mem_genericPoints_iff X _).mpr
  simpa only [← homeomorph_apply, Homeomorph.apply_symm_apply] using hx

theorem isReduced_reduction (X : Scheme.{u}) : IsReduced X.nilradical.subscheme := by
  exact Geometry.ReducedClosedSubscheme.isReduced_radical_subscheme (⊥ : X.IdealSheafData)

end

end DeJongAlterations.StableModificationBridge.ReductionCanonicalGeometry
