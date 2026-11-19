/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Rees.Defs

/-!
# The graded Rees algebra: components and degree one

Basic facts about the grading `reesAlgebra.grading I` of the Rees algebra `⨁ᵢ Iⁱ tⁱ`
[Hau14, Definition 4.6], in which Mathlib's polynomial variable `X` plays the role of Hauser's `t`.

* `reesAlgebra.coe_component`: the degree-`n` component of `p` is the monomial `(coeff n p) tⁿ`.
* `reesAlgebra.degreeOne I : I →ₗ[R] reesAlgebra I`: the degree-one element `a t` of `a ∈ I`
  [Hau14, Definition 4.16], whose range is the degree-one piece
  (`reesAlgebra.grading_one_eq_range`) and whose values generate the irrelevant ideal
  (`Hironaka.Scheme.BlowUp.Rees.Irrelevant`).
-/

@[expose] public section

open Polynomial

universe u

variable {R : Type u} [CommRing R]

section Components

variable {I : Ideal R}

@[simp]
theorem reesAlgebra.coe_component (n : ℕ) (p : reesAlgebra I) :
    ((reesAlgebra.component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) :=
  rfl

end Components

section DegreeOne

variable (I : Ideal R)

/-- The degree-one element `a t` of the Rees algebra, for `a ∈ I` — an element of `I` defines a
homogeneous element of degree `1` of the Rees algebra [Hau14, Definition 4.16] — as an `R`-linear
map `I → reesAlgebra I`.  Its range is the degree-one piece (`reesAlgebra.grading_one_eq_range`),
its values generate the irrelevant ideal (`reesAlgebra.irrelevant_le_span_degreeOne`), and the
chart cover of the affine blow-up is indexed by it (`affineBlowUp.affineOpenCover`). -/
noncomputable def reesAlgebra.degreeOne : I →ₗ[R] reesAlgebra I where
  toFun a := ⟨monomial 1 (a : R), reesAlgebra.monomial_mem.mpr (by simp)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (by simp [smul_monomial])

variable {I}

@[simp]
theorem reesAlgebra.coe_degreeOne (a : I) :
    (reesAlgebra.degreeOne I a : R[X]) = monomial 1 (a : R) :=
  rfl

theorem reesAlgebra.degreeOne_mem (a : I) :
    reesAlgebra.degreeOne I a ∈ reesAlgebra.grading I 1 :=
  reesAlgebra.mem_grading_of_coe_eq_monomial rfl

/-- The degree-one piece is `I t`: its elements are exactly the `a t`, `a ∈ I`. -/
theorem reesAlgebra.mem_grading_one_iff {p : reesAlgebra I} :
    p ∈ reesAlgebra.grading I 1 ↔ ∃ a : I, reesAlgebra.degreeOne I a = p := by
  refine ⟨fun hp => ?_, fun ⟨a, ha⟩ => ha ▸ reesAlgebra.degreeOne_mem a⟩
  obtain ⟨c, hc, hpc⟩ := reesAlgebra.mem_grading_iff_exists.mp hp
  exact ⟨⟨c, by simpa using hc⟩, Subtype.ext hpc.symm⟩

variable (I) in
/-- The degree-one piece is the range of `a ↦ a t`. -/
theorem reesAlgebra.grading_one_eq_range :
    reesAlgebra.grading I 1 = LinearMap.range (reesAlgebra.degreeOne I) :=
  Submodule.ext fun _ => reesAlgebra.mem_grading_one_iff.trans LinearMap.mem_range.symm

end DegreeOne
