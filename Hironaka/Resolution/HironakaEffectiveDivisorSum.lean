/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDivisorResidual

set_option autoImplicit false

/-!
# Actual effective-divisor arithmetic and finite hypersurface sums

The operations are constructed from invertible ideals. The bridge from an
actual ideal factorization to an effective-divisor sum retains multiplicities.
Blueprint: `hironaka-divisor-sum-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaEffectiveDivisorSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  IdealWeightPowers GermIdealTotalTransform HironakaDivisorResidual

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Equality of the genuine invertible ideal determines the divisor. -/
theorem effectiveDivisor_eq_of_ideal_eq {D G : EffectiveDivisor n M}
    (h : D.ideal = G.ideal) : D = G := by
  cases D
  cases G
  cases h
  rfl

/-- The zero effective divisor is produced by the holomorphic unit ideal. -/
instance : Zero (EffectiveDivisor n M) :=
  ⟨⟨unitIdeal n M, BlowupExceptionalDivisor.isInvertible_unitIdeal⟩⟩

/-- Addition is produced by the genuine product of invertible ideals. -/
instance : Add (EffectiveDivisor n M) :=
  ⟨fun D G => ⟨D.ideal.mul G.ideal, isInvertible_mul D.isInvertible G.isInvertible⟩⟩

@[simp] theorem ideal_zero : (0 : EffectiveDivisor n M).ideal = unitIdeal n M := rfl

@[simp] theorem ideal_add (D G : EffectiveDivisor n M) :
    (D + G).ideal = D.ideal.mul G.ideal := rfl

/-- Effective divisors carry actual commutative additive arithmetic. -/
instance : AddCommMonoid (EffectiveDivisor n M) where
  add_assoc D G H := effectiveDivisor_eq_of_ideal_eq
    (mul_assoc (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
      (DivisorMetric.isCoherent_of_isInvertible G.isInvertible)
      (DivisorMetric.isCoherent_of_isInvertible H.isInvertible))
  zero_add D := effectiveDivisor_eq_of_ideal_eq
    (BlowupControlledTransform.unitIdeal_mul
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible))
  add_zero D := effectiveDivisor_eq_of_ideal_eq
    (RestrictLeCalculus.mul_unitIdeal
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible))
  add_comm D G := effectiveDivisor_eq_of_ideal_eq
    (RestrictLeCalculus.mul_comm' D.ideal G.ideal)
  nsmul := nsmulRec

/-- Natural scalar multiplication agrees with genuine ideal powers. -/
@[simp] theorem ideal_nsmul (a : ℕ) (D : EffectiveDivisor n M) :
    (a • D).ideal = idealPow D.ideal a := by
  induction a with
  | zero => simp [idealPow_zero]
  | succ a ih => rw [succ_nsmul, ideal_add, ih, idealPow_succ]

/-- The genuine product has precisely the union of the two zero loci. -/
theorem zeroLocus_mul_eq_union {I J : GermIdeal n M}
    (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (I.mul J).zeroLocus = I.zeroLocus ∪ J.zeroLocus := by
  apply Subset.antisymm
  · intro x hx
    by_contra h
    have hxI : x ∉ I.zeroLocus := fun hI => h (Or.inl hI)
    have hxJ : x ∉ J.zeroLocus := fun hJ => h (Or.inr hJ)
    exact RestrictLeCalculus.notMem_zeroLocus_mul hI hJ hxI hxJ hx
  · intro x hx
    rcases hx with hx | hx
    · rw [RestrictLeCalculus.mul_comm']
      exact RestrictLeCalculus.zeroLocus_right_subset_mul J I hx
    · exact RestrictLeCalculus.zeroLocus_right_subset_mul I J hx

@[simp] theorem support_zero : (0 : EffectiveDivisor n M).support = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h1 : (unitIdeal n M).mem x (fun _ => (1 : ℂ)) :=
    holomorphicAt_const 1
  exact one_ne_zero (hx _ h1)

/-- Addition retains exactly the union of the actual supports. -/
@[simp] theorem support_add (D G : EffectiveDivisor n M) :
    (D + G).support = D.support ∪ G.support :=
  zeroLocus_mul_eq_union
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
    (DivisorMetric.isCoherent_of_isInvertible G.isInvertible)

/-- Positive multiples retain exactly the actual support. -/
theorem support_nsmul (D : EffectiveDivisor n M) {a : ℕ} (ha : 0 < a) :
    (a • D).support = D.support := by
  cases a with
  | zero => omega
  | succ a =>
    induction a with
    | zero => simp
    | succ a ih => rw [succ_nsmul, support_add, ih (by omega), union_self]

/-- Smooth codimension-one geometry produces a genuine effective divisor. -/
def hypersurfaceDivisor {W : Set M} (hW : IsClosed W)
    (hcodim : ∀ x ∈ W, ∃ d, RegularAtDim (n := n) W x d ∧ d + 1 = n) :
    EffectiveDivisor n M :=
  ⟨vanishingIdeal W, BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne
    hW (by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨d, hd, hdn⟩ := hcodim x (interior_subset hx)
      have hfull := EmbeddedFromResolution.regularAtDim_of_mem_nhds (n := n)
        (mem_interior_iff_mem_nhds.mp hx)
      have heq := RegularPointDimension.eq_of_regularAtDim hd hfull
      omega) hcodim⟩

@[simp] theorem ideal_hypersurfaceDivisor {W : Set M} (hW : IsClosed W)
    (hcodim : ∀ x ∈ W, ∃ d, RegularAtDim (n := n) W x d ∧ d + 1 = n) :
    (hypersurfaceDivisor hW hcodim).ideal = vanishingIdeal (n := n) W := rfl

@[simp] theorem support_hypersurfaceDivisor {W : Set M} (hW : IsClosed W)
    (hcodim : ∀ x ∈ W, ∃ d, RegularAtDim (n := n) W x d ∧ d + 1 = n) :
    (hypersurfaceDivisor hW hcodim).support = W :=
  BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW

/-- The actual finite sum of natural multiples of smooth hypersurfaces. -/
def componentSum : (A : List (Set M × ℕ)) →
    (∀ p ∈ A, IsClosed p.1 ∧
      ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n) →
    EffectiveDivisor n M
  | [], _ => 0
  | p :: A, hA => p.2 • hypersurfaceDivisor (hA p (by simp)).1
      (hA p (by simp)).2 + componentSum A (fun q hq => hA q (List.mem_cons_of_mem p hq))

/-- The finite sum has exactly the complete original component-power ideal. -/
theorem ideal_componentSum (A : List (Set M × ℕ))
    (hA : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n) :
    (componentSum A hA).ideal = componentPowerProduct (n := n) A := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    simp only [componentSum, ideal_add, ideal_nsmul, ideal_hypersurfaceDivisor,
      ih, componentPowerProduct]

/-- A proved full ideal factorization yields equality of actual divisors. -/
theorem eq_componentSum_of_ideal_eq (D : EffectiveDivisor n M)
    (A : List (Set M × ℕ))
    (hA : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n)
    (hD : D.ideal = componentPowerProduct (n := n) A) :
    D = componentSum A hA :=
  effectiveDivisor_eq_of_ideal_eq (hD.trans (ideal_componentSum A hA).symm)

end
end Hironaka.HironakaEffectiveDivisorSum
