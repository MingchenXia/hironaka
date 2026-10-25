/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL)
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Purely inseparable base change of a geometrically reduced field

This file contains the field theory of the purely inseparable base change used by the Claude team
in place of de Jong's Bertini step 4.11 (c), (d) (de Jong, *Smoothness, semi-stability and
alterations*, 1996, §4.11; blueprint chapter `sm-dj-perfection`, node
`lem:sm-dj-perfection-field`). The route is not in de Jong.

Let `K` be a field of exponential characteristic `q`.

* `isField_tensorProduct_of_isPurelyInseparable`: if `L / K` is purely inseparable and `F / K` is
  geometrically reduced (Mathlib's `Algebra.IsGeometricallyReduced`, i.e. `F` is a separable
  extension of `K` in the sense of Mac Lane), then `L ⊗[K] F` is a field. The proof is
  elementary: every element of `L ⊗[K] F` has a `q`-power in `1 ⊗ F`, so a non-nilpotent element is
  invertible, and `L ⊗[K] F` is reduced.
* `linearDisjoint_of_isGeometricallyReduced`: consequently, inside any field `M`, a purely
  inseparable intermediate field `Ω` and a geometrically reduced intermediate field `F` are
  linearly disjoint over `K`.
* `rootField K M m` is `K^{1/q^m} = {x ∈ M | x ^ q ^ m ∈ K}`; the `K_m` of the blueprint. These
  increase with `m`, their union is the relative perfect closure `perfectClosure K M` (which is
  `K^{perf}` when `M` is algebraically closed), and every finite purely inseparable intermediate
  field lies in some `K_m` (`le_rootField_exponent`).
* `exists_finiteDimensional_of_mem_adjoin`: if `Ω / K` is algebraic, every element of the field
  `Ω(S)` already lies in `E(S)` for an intermediate field `E ≤ Ω` finite over `K`. This is the
  "directed union" step of the stabilization argument.
-/

open TensorProduct

noncomputable section

namespace DeJongAlterations.StableModification.Perfection

universe u v w

section TensorField

variable (K : Type u) (L : Type v) (F : Type w) [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra K F]

/-- The tensor product of two field extensions is nontrivial. -/
theorem nontrivial_tensorProduct : Nontrivial (L ⊗[K] F) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K L F
    (algebraMap K L).injective (algebraMap K F).injective

/-- If `L / K` is purely inseparable, every element of `L ⊗[K] F` has a `q`-power in `1 ⊗ F`,
where `q` is the exponential characteristic of `K`. -/
theorem exists_pow_mem_range_includeRight [IsPurelyInseparable K L] (x : L ⊗[K] F) :
    ∃ n : ℕ, x ^ ringExpChar K ^ n ∈
      (Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F).range := by
  have := nontrivial_tensorProduct K L F
  have : ExpChar (L ⊗[K] F) (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K (L ⊗[K] F)).injective (ringExpChar K)
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l f =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K (ringExpChar K) l
    refine ⟨n, c • f ^ ringExpChar K ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [add_pow_expChar_pow]
    refine add_mem ?_ ?_
    · rw [pow_add, pow_mul]
      exact pow_mem hn _
    · rw [add_comm, pow_add, pow_mul]
      exact pow_mem hm _

/-- **Purely inseparable base change of a geometrically reduced field is a field.** If `L / K` is
purely inseparable and `F / K` is geometrically reduced (separable in the sense of Mac Lane), then
`L ⊗[K] F` is a field. -/
theorem isField_tensorProduct_of_isPurelyInseparable [IsPurelyInseparable K L]
    [Algebra.IsGeometricallyReduced K F] : IsField (L ⊗[K] F) := by
  have hnt := nontrivial_tensorProduct K L F
  refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, f, hf⟩ := exists_pow_mem_range_includeRight K L F x
  have hf' : (Algebra.TensorProduct.includeRight f : L ⊗[K] F) = x ^ ringExpChar K ^ n := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf'
    exact hx (IsReduced.eq_zero x ⟨_, hf'.symm⟩)
  have hpos : 0 < ringExpChar K ^ n := pow_pos (expChar_pos K (ringExpChar K)) n
  refine ⟨x ^ (ringExpChar K ^ n - 1) * Algebra.TensorProduct.includeRight f⁻¹, ?_⟩
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, ← hf', ← map_mul, mul_inv_cancel₀ hf0,
    map_one]

/-- Inside any field `M`, a purely inseparable intermediate field `Ω` and a geometrically reduced
intermediate field `F` are linearly disjoint over `K`. -/
theorem linearDisjoint_of_isGeometricallyReduced {M : Type v} [Field M] [Algebra K M]
    (Ω F : IntermediateField K M) [IsPurelyInseparable K Ω]
    [Algebra.IsGeometricallyReduced K F] : Ω.LinearDisjoint F :=
  IntermediateField.LinearDisjoint.of_isField (isField_tensorProduct_of_isPurelyInseparable K Ω F)

end TensorField

section RootField

variable (K : Type u) (M : Type v) [Field K] [Field M] [Algebra K M]

/-- A field extension of `K` has the exponential characteristic of `K`. -/
theorem expChar_ringExpChar : ExpChar M (ringExpChar K) :=
  expChar_of_injective_algebraMap (algebraMap K M).injective (ringExpChar K)

attribute [local instance] expChar_ringExpChar

/-- The field `K^{1/q^m} = {x ∈ M | x ^ q ^ m ∈ K}` of `q^m`-th roots of elements of `K` inside `M`,
where `q` is the exponential characteristic of `K`. This is the field `K_m` of the blueprint. -/
def rootField (m : ℕ) : IntermediateField K M :=
  ((algebraMap K M).fieldRange.comap (iterateFrobenius M (ringExpChar K) m)).toIntermediateField
    fun x => ⟨x ^ ringExpChar K ^ m, by simp [iterateFrobenius_def]⟩

variable {K M}

theorem mem_rootField {m : ℕ} {x : M} :
    x ∈ rootField K M m ↔ x ^ ringExpChar K ^ m ∈ (algebraMap K M).range := by
  change iterateFrobenius M (ringExpChar K) m x ∈ (algebraMap K M).fieldRange ↔ _
  rw [iterateFrobenius_def]
  rfl

theorem rootField_mono {m m' : ℕ} (h : m ≤ m') : rootField K M m ≤ rootField K M m' := by
  intro x hx
  rw [mem_rootField] at hx ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_mul]
  exact pow_mem hx _

theorem rootField_zero : rootField K M 0 = ⊥ := by
  ext x
  rw [mem_rootField, IntermediateField.mem_bot, pow_zero, pow_one]
  rfl

theorem rootField_le_perfectClosure (m : ℕ) : rootField K M m ≤ perfectClosure K M :=
  fun _ hx => mem_perfectClosure_iff.2 ⟨m, mem_rootField.1 hx⟩

/-- The perfect closure of `K` in `M` is the union of the fields `K^{1/q^m}`. -/
theorem iSup_rootField : ⨆ m, rootField K M m = perfectClosure K M := by
  refine le_antisymm (iSup_le rootField_le_perfectClosure) fun x hx => ?_
  obtain ⟨m, hm⟩ := mem_perfectClosure_iff.1 hx
  exact le_iSup (rootField K M) m (mem_rootField.2 hm)

/-- Every element of the perfect closure lies in some `K^{1/q^m}`. -/
theorem exists_mem_rootField_of_mem_perfectClosure {x : M} (hx : x ∈ perfectClosure K M) :
    ∃ m, x ∈ rootField K M m := by
  obtain ⟨m, hm⟩ := mem_perfectClosure_iff.1 hx
  exact ⟨m, mem_rootField.2 hm⟩

/-- A finite purely inseparable intermediate field `E` lies in `K^{1/q^e}`, `e` its exponent. -/
theorem le_rootField_exponent (E : IntermediateField K M) [FiniteDimensional K E]
    [IsPurelyInseparable K E] : E ≤ rootField K M (IsPurelyInseparable.exponent K E) := by
  intro x hx
  rw [mem_rootField]
  obtain ⟨c, hc⟩ := IsPurelyInseparable.exponent_def K (⟨x, hx⟩ : E)
  refine ⟨c, ?_⟩
  have := congrArg (fun y : E => (y : M)) hc
  simpa using this

/-- In characteristic zero all the fields `K^{1/q^m}` are `K`. -/
theorem rootField_eq_bot_of_charZero [CharZero K] (m : ℕ) : rootField K M m = ⊥ := by
  ext x
  rw [mem_rootField, ringExpChar.eq_one, one_pow, pow_one, IntermediateField.mem_bot]
  rfl

end RootField

section DirectedUnion

variable {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]

/-- **Directed union.** If `Ω / K` is algebraic, every element of the field `Ω(S)` generated by a
set `S ⊆ M` over `Ω` lies in `E(S)` for some intermediate field `E ≤ Ω` that is finite over `K`. -/
theorem exists_finiteDimensional_of_mem_adjoin (Ω : IntermediateField K M)
    [Algebra.IsAlgebraic K Ω] (S : Set M) {x : M} (hx : x ∈ IntermediateField.adjoin Ω S) :
    ∃ E : IntermediateField K M, E ≤ Ω ∧ FiniteDimensional K E ∧
      x ∈ IntermediateField.adjoin E S := by
  have hx' : x ∈ (IntermediateField.adjoin Ω S).restrictScalars K := hx
  rw [IntermediateField.restrictScalars_adjoin] at hx'
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hx'
  let E := IntermediateField.adjoin K ((T : Set M) ∩ (Ω : Set M))
  have hEΩ : E ≤ Ω := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  refine ⟨E, hEΩ, ?_, ?_⟩
  · have : Finite ↥((T : Set M) ∩ (Ω : Set M)) := (T.finite_toSet.inter_of_left _).to_subtype
    refine IntermediateField.finiteDimensional_adjoin fun y hy => ?_
    have : IsIntegral K (⟨y, hy.2⟩ : Ω) := Algebra.IsIntegral.isIntegral _
    exact this.map Ω.val
  · have : x ∈ (IntermediateField.adjoin E S).restrictScalars K := by
      rw [IntermediateField.restrictScalars_adjoin]
      refine IntermediateField.adjoin.mono K _ _ ?_ hxT
      intro t ht
      rcases hT ht with h | h
      · exact Or.inl (IntermediateField.subset_adjoin K _ ⟨ht, h⟩)
      · exact Or.inr h
    exact this

end DirectedUnion

end DeJongAlterations.StableModification.Perfection

end
