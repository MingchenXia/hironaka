/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Functoriality of the exceptional locus

Source: CT22, Section 4.

`exceptionalLocus n f` is the set of points where the holomorphic differential
of an equidimensional map fails to be bijective.  Two facts make it functorial
along a composition, which is what an induction over `IsBlowupSequence` needs:

* `exceptionalLocus_id`: the identity has empty exceptional locus.
* `exceptionalLocus_comp`: `Exc(f ∘ g) = Exc(g) ∪ g⁻¹(Exc f)`.

The second rests on the chain rule plus a purely linear-algebraic fact: for
continuous linear endomorphisms of a finite-dimensional space, a composition is
bijective exactly when both factors are (`bijective_comp_clm_iff`).  All three
manifolds have the same dimension `n`, so all the differentials are
endomorphisms of `ComplexModel n`; in particular injectivity and surjectivity
coincide, which is what makes the "only if" direction true.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]

/-- For endomorphisms of a finite-dimensional space, a composition is bijective
exactly when both factors are. -/
theorem bijective_comp_clm_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (A B : E →L[ℂ] E) :
    Function.Bijective (A.comp B) ↔
      Function.Bijective A ∧ Function.Bijective B := by
  constructor
  · intro h
    have hcomp : (↑(A.comp B) : E → E) = (A : E → E) ∘ (B : E → E) := rfl
    rw [hcomp] at h
    have hBinj : Function.Injective (B : E → E) := h.1.of_comp
    have hAsurj : Function.Surjective (A : E → E) := h.2.of_comp
    exact ⟨⟨LinearMap.injective_iff_surjective.mpr hAsurj, hAsurj⟩,
      ⟨hBinj, LinearMap.injective_iff_surjective.mp hBinj⟩⟩
  · intro ⟨hA, hB⟩
    exact hA.comp hB

omit [IsComplexManifold n Y] in
/-- The identity map has empty exceptional locus. -/
@[simp] theorem exceptionalLocus_id : exceptionalLocus n (id : Y → Y) = ∅ := by
  ext y
  simp only [exceptionalLocus, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  rw [mfderiv_id]
  exact Function.bijective_id

omit [IsComplexManifold n X] [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- **`Exc(f ∘ g) = Exc(g) ∪ g⁻¹(Exc f)`.** -/
theorem exceptionalLocus_comp {f : Y → X} {g : Z → Y}
    (hf : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f)
    (hg : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g) :
    exceptionalLocus n (f ∘ g) =
      exceptionalLocus n g ∪ g ⁻¹' exceptionalLocus n f := by
  ext z
  have hchain := mfderiv_comp (I := 𝓘(ℂ, ComplexModel n))
    (I' := 𝓘(ℂ, ComplexModel n)) (I'' := 𝓘(ℂ, ComplexModel n))
    (f := g) (g := f) z (hf (g z)) (hg z)
  have key : Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (f ∘ g) z) ↔
      Function.Bijective
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f (g z)) ∧
        Function.Bijective
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g z) := by
    rw [hchain]
    exact bijective_comp_clm_iff (E := ComplexModel n) _ _
  simp only [exceptionalLocus, mem_ofPred_eq, mem_union, mem_preimage, key,
    not_and_or]
  tauto

end

end Hironaka.BlowupSequences
