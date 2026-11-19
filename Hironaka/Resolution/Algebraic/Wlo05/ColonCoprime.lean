/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.Transform

/-!
# Colon ideals of comaximal ideal sheaves

Ideal sheaves with disjoint supports are comaximal (`sup_eq_top_of_disjoint_support`), the product
of comaximal ideal sheaves is their intersection (`mul_eq_inf_of_sup_eq_top`), and the colon of the
product by one factor is the other (`colon_mul_left_of_sup_eq_top`: `(I · J) : I = J` when
`I + J = 𝒪`, since `x · I ⊆ I · J ⊆ J` and `x = x·a + x·b` for `1 = a + b`). Everything is proved
sectionwise on the affine opens, through `ideal_sup`, `ideal_mul`, `le_def` and the colon
(`le_colon_iff_mul_le`, `colon_mul_le`).

These are the tools for the products of pairwise disjoint components
(`Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon`) in Włodarczyk's embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`): when the loop isolates the strict transforms of
some components of `Y` before any blow-up, the ideal of the remaining components is the colon of the
ideal of `Y` by the ideal of the isolated ones, the two being comaximal because the components of a
smooth `Y` are disjoint (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant`).
-/

public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- Ideal sheaves with disjoint supports are comaximal: `supp (I ⊔ J) = supp I ⊓ supp J = ∅`. -/
theorem sup_eq_top_of_disjoint_support (h : Disjoint I.support J.support) : I ⊔ J = ⊤ := by
  rw [← support_eq_bot_iff, support_sup]
  exact disjoint_iff.mp h

/-- On every affine open, comaximal ideal sheaves have comaximal ideals of sections. -/
theorem ideal_sup_eq_top_of_sup_eq_top (h : I ⊔ J = ⊤) (U : X.affineOpens) :
    I.ideal U ⊔ J.ideal U = ⊤ := by
  have := congrFun (congrArg IdealSheafData.ideal h) U
  rw [ideal_sup, ideal_top, Pi.sup_apply, Pi.top_apply] at this
  exact this

/-- The product of comaximal ideal sheaves is their intersection (Mathlib's
`Ideal.mul_eq_inf_of_coprime` on every affine open). -/
theorem mul_eq_inf_of_sup_eq_top (h : I ⊔ J = ⊤) : I * J = I ⊓ J := by
  ext U : 2
  rw [ideal_mul, ideal_inf, Pi.mul_apply, Pi.inf_apply]
  exact Ideal.mul_eq_inf_of_coprime (ideal_sup_eq_top_of_sup_eq_top I J h U)

/-- The colon of the product by the first factor is the second, for comaximal ideal sheaves:
`(I · J) : I = J`. -/
theorem colon_mul_left_of_sup_eq_top (h : I ⊔ J = ⊤) : (I * J).colon I = J := by
  refine le_antisymm ?_ ?_
  · rw [le_def]
    intro U x hx
    have hone : (1 : Γ(X, U)) ∈ I.ideal U ⊔ J.ideal U := by
      rw [ideal_sup_eq_top_of_sup_eq_top I J h U]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
    have hxa : x * a ∈ (I * J).ideal U := by
      have hle := le_def.mp (colon_mul_le (I * J) I) U
      rw [ideal_mul, Pi.mul_apply] at hle
      exact hle (Ideal.mul_mem_mul hx ha)
    have hxa' : x * a ∈ J.ideal U := by
      rw [ideal_mul, Pi.mul_apply] at hxa
      exact (Submodule.mem_inf.mp (Ideal.mul_le_inf hxa)).2
    have hxb : x * b ∈ J.ideal U := Ideal.mul_mem_left _ x hb
    have : x = x * a + x * b := by rw [← mul_add, hab, mul_one]
    rw [this]
    exact Ideal.add_mem _ hxa' hxb
  · rw [le_colon_iff_mul_le, le_def]
    intro U
    rw [ideal_mul, ideal_mul, Pi.mul_apply, Pi.mul_apply, mul_comm]

end AlgebraicGeometry.Scheme.IdealSheafData
