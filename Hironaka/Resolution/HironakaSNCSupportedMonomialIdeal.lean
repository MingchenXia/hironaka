/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDivisorResidualUnit
import Hironaka.Invariant.MonomialPartIntrinsic

set_option autoImplicit false

/-!
# The actual supported divisor ideal equals its intrinsic monomial ideal

Source: Włodarczyk 2005, Step 2. This uses actual divisor exponents and
the genuine colon residual, without assuming any globally constant
integer coefficient for a disconnected SNC list member.
Blueprint: `hironaka-snc-supported-monomial-ideal.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSNCSupportedMonomialIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings InvertibleIdealQuotient HironakaDivisorResidualUnit
  HironakaDivisorPowers MonomialPart IdealWeightPowers GermIdealTotalTransform
  RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine monomial generator and its nearby nonvanishing produce
actual invertibility, with no connectedness input. -/
theorem isInvertible_monomialPart (hn : 0 < n) {E : List (Set M)}
    (hE : IsSNCDivisor n E) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ y, DivisorExponent.IsNonzeroAt 𝔞 y) :
    (monomialPart n 𝔞 E).IsInvertible := by
  intro x
  obtain ⟨U, hU, hxU, m, hmhol, hmne, hgen⟩ :=
    exists_generator_monomialPart hn hE h𝔞 hne x
  refine ⟨U, hU, hxU, m, ?_, ?_, hgen⟩
  · intro y hy
    exact (hmhol y hy).mdifferentiableAt.mdifferentiableWithinAt
  · intro W hW hWU hWne
    obtain ⟨y, hyW⟩ := hWne
    obtain ⟨z, hzm, hzW⟩ :=
      ((hmne y (hWU hyW)).and_eventually (hW.mem_nhds hyW)).exists
    exact ⟨z, hzW, hzm⟩

omit [IsComplexManifold n M] in
/-- The previously defined intrinsic nonmonomial ideal is the actual colon. -/
theorem nonmonomialPart_eq_colon (𝔞 : GermIdeal n M) (E : List (Set M)) :
    nonmonomialPart n 𝔞 E = colon 𝔞 (monomialPart n 𝔞 E) := by
  apply GermIdeal.ext
  apply funext
  intro x
  apply funext
  intro f
  apply propext
  constructor
  · intro hf
    refine ⟨hf.1, fun g hg => ?_⟩
    simpa only [mul_comm] using hf.2 g hg
  · intro hf
    refine ⟨hf.1, fun g hg => ?_⟩
    simpa only [mul_comm] using hf.2 g hg

/-- For an actual effective divisor the genuine nonmonomial ideal is
invertible, by the proved colon producer for nested invertible ideals. -/
theorem isInvertible_nonmonomialPart (hn : 0 < n) (D : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E) :
    (nonmonomialPart n D.ideal E).IsInvertible := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  rw [nonmonomialPart_eq_colon]
  exact ActualInvertibleIdealDifference.isInvertible_colon D.isInvertible
    (isInvertible_monomialPart hn hE hcoh
      (fun y => isNonzeroAt_of_isInvertible D.isInvertible y))
    (le_monomialPart hn hE hcoh)

/-- An SNC hyperplane cannot contain any point in ambient dimension zero. -/
theorem notMem_member_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (E : List (Set M)) (hE : IsSNCDivisor 0 E) (i : Fin E.length) (x : M) :
    x ∉ E.get i := by
  intro hxi
  obtain ⟨S, -, hcard, -⟩ := hE.2 x
  have hS : S i = ∅ := Finset.eq_empty_of_forall_notMem fun j _ => j.elim0
  have h01 : (0 : ℕ) = 1 := by simpa only [hS, Finset.card_empty] using hcard i hxi
  exact Nat.zero_ne_one h01

/-- With no active SNC member, the intrinsic monomial ideal is exactly
the holomorphic unit ideal, including ambient dimension zero. -/
theorem monomialPart_eq_unitIdeal_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (𝔞 : GermIdeal 0 M) (E : List (Set M)) (hE : IsSNCDivisor 0 E) :
    monomialPart 0 𝔞 E = unitIdeal 0 M := by
  exact GermIdeal.ext (funext fun x => funext fun f => propext
    ⟨fun hf => hf.1, fun hf => ⟨hf, fun i hi => (notMem_member_of_dim_zero E hE i x hi).elim⟩⟩)

private theorem ideal_eq_unitIdeal_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (D : EffectiveDivisor 0 M) (E : List (Set M)) (hE : IsSNCDivisor 0 E)
    (hsupport : D.support ⊆ ⋃ W ∈ E, W) : D.ideal = unitIdeal 0 M := by
  apply BlowupTowerTransforms.eq_unitIdeal_of_zeroLocus_eq_empty
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hmem : ∃ W ∈ E, x ∈ W := by
    obtain ⟨W, hW⟩ := mem_iUnion.mp (hsupport hx)
    obtain ⟨hWE, hxW⟩ := mem_iUnion.mp hW
    exact ⟨W, hWE, hxW⟩
  obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
  exact notMem_member_of_dim_zero E hE i x hi

/-- The genuine nonmonomial residual of a supported effective divisor
is the unit ideal. Disconnected SNC members and dimension zero are allowed. -/
theorem nonmonomialPart_eq_unitIdeal_of_support_subset (D : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ W ∈ E, W) :
    nonmonomialPart n D.ideal E = unitIdeal n M := by
  by_cases hn : 0 < n
  · have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
    have hne : ∀ y, DivisorExponent.IsNonzeroAt D.ideal y :=
      fun y => isNonzeroAt_of_isInvertible D.isInvertible y
    let R : EffectiveDivisor n M :=
      ⟨nonmonomialPart n D.ideal E, isInvertible_nonmonomialPart hn D E hE⟩
    have hRcoh := DivisorMetric.isCoherent_of_isInvertible R.isInvertible
    have hRD : R.support ⊆ D.support := by
      change (nonmonomialPart n D.ideal E).zeroLocus ⊆ D.ideal.zeroLocus
      have hfac := eq_mul_monomialPart hn hE hcoh hne
      have hsub := RestrictLeCalculus.zeroLocus_right_subset_mul
        (monomialPart n D.ideal E) (nonmonomialPart n D.ideal E)
      rw [RestrictLeCalculus.mul_comm', ← hfac] at hsub
      exact hsub
    apply BlowupTowerTransforms.eq_unitIdeal_of_zeroLocus_eq_empty hRcoh
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨W, hWE, hxW, hlocal⟩ :=
      exists_member_locally_in_support R E hE (hRD.trans hsupport) hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hWE
    have hxi : x ∈ E.get i := hi.symm ▸ hxW
    obtain ⟨f, hf, hfnot⟩ := exists_mem_nonmonomialPart_notMem hn hE hcoh hne hxi
    apply hfnot
    refine ⟨hf.1, ?_⟩
    filter_upwards [hlocal, HadamardBridge.eventually_mem_of_isCoherent hRcoh hf]
      with y hy hyf hyi
    exact hy (hi ▸ hyi) f hyf
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hD := ideal_eq_unitIdeal_of_dim_zero D E hE hsupport
    rw [hD]
    exact GermIdeal.ext (funext fun x => funext fun f => propext
      ⟨fun hf => hf.1, fun hf => ⟨hf, fun m hm => hf.mul hm.1⟩⟩)

/-- An SNC-supported effective divisor has exactly its intrinsic
monomial germ ideal, with all original stalks and actual exponents retained. -/
theorem ideal_eq_monomialPart_of_support_subset (D : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ W ∈ E, W) :
    D.ideal = monomialPart n D.ideal E := by
  by_cases hn : 0 < n
  · have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
    have hne : ∀ y, DivisorExponent.IsNonzeroAt D.ideal y :=
      fun y => isNonzeroAt_of_isInvertible D.isInvertible y
    calc
      D.ideal = (nonmonomialPart n D.ideal E).mul (monomialPart n D.ideal E) :=
        eq_mul_monomialPart hn hE hcoh hne
      _ = (unitIdeal n M).mul (monomialPart n D.ideal E) :=
        congrArg (fun I => I.mul (monomialPart n D.ideal E))
          (nonmonomialPart_eq_unitIdeal_of_support_subset D E hE hsupport)
      _ = monomialPart n D.ideal E :=
        BlowupControlledTransform.unitIdeal_mul (isCoherent_monomialPart hn hE hcoh hne)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [monomialPart_eq_unitIdeal_of_dim_zero D.ideal E hE]
    exact ideal_eq_unitIdeal_of_dim_zero D E hE hsupport

end
end Hironaka.HironakaSNCSupportedMonomialIdeal
