/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.ImmediateDegreeP
import DeJongAlterations.StableModification.Valuation.Analytic.Inertia
import DeJongAlterations.StableModification.Valuation.Analytic.Annulus
import DeJongAlterations.StableModification.Valuation.Analytic.Gauss
import DeJongAlterations.StableModification.Valuation.SepClosed

/-!
# One-dimensional analytic fields: closures, unramified extensions and types

Let `k` be an algebraically closed analytic field and `L` a non-archimedean normed field containing
`k`. This file sets up the vocabulary of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), §6.2–§6.3 (`semi-stable.tex`, lines 3663–3677 and 3981–3999), for
the uniformization of one-dimensional analytic fields (Temkin's Theorems 6.3.1 and 2.1.10).

## Main definitions

* `closureAdjoin k x`: the closure `\overline{k(x)}` of `k(x)` in `L`, as an intermediate field.
* `IsOneDimensional k L`: `L` is finite over `\overline{k(y)}` for some `y ∉ k` (Temkin,
  lines 3664–3666).
* `IsUnramified K L`: a finite extension `L/K` with `f_{L/K} = [L : K]` and separable residue
  extension (Temkin's Lemma 2.1.5(ii) form of "unramified").
* `IsResidueTrivial k L`, `IsValueTrivial k L`, `IsImmediateOver k L`: `L` has the residue field
  of `k`, the value group of `k`, or both (`L` is `k`-immediate).

## Main results

* `isImmediateOver_iff`, `IsResidueTrivial.of_finiteDimensional`,
  `IsValueTrivial.of_finiteDimensional`, `IsImmediateOver.of_finiteDimensional`: these
  properties pass to finite extensions (`k` algebraically closed).
* `IsImmediateOver.isImmediate`, `IsImmediateOver.isTypeFourGenerator`.
* `isTypeFourGenerator_or_isAnnulusGenerator_or_isGaussGenerator` (**types of generators**): a
  topological generator `z ∉ k` is a type 4 generator, or an affine transform of it is an annulus
  generator or a Gauss generator (Temkin's types 4, 3, 2).

## References

Blueprint chapter `sm-val-onedim.tex`: `def:sm-an-closure-adjoin`, `lem:sm-an-closure-adjoin`,
`def:sm-an-one-dimensional`, `def:sm-an-unramified-analytic`, `def:sm-an-constant-residue`,
`lem:sm-an-constant-residue`, `lem:sm-an-types`.
-/

noncomputable section

open IsLocalRing Polynomial Module Topology
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### The closure of `k(x)` -/

section Closure

variable (k : Type*) {L : Type*} [Field k] [NormedField L] [Algebra k L]

/-- The closure `\overline{k(x)}` of the subfield `k(x)` of `L` (Temkin, §6.2). -/
def closureAdjoin (x : L) : IntermediateField k L :=
  Subfield.toIntermediateField (IntermediateField.adjoin k {x}).toSubfield.topologicalClosure
    fun c ↦ Subfield.le_topologicalClosure _ (IntermediateField.algebraMap_mem _ c)

variable {k}

theorem coe_closureAdjoin (x : L) :
    (closureAdjoin k x : Set L) = closure (IntermediateField.adjoin k {x} : Set L) := rfl

theorem mem_closureAdjoin_iff {x y : L} :
    y ∈ closureAdjoin k x ↔ y ∈ closure (IntermediateField.adjoin k {x} : Set L) := Iff.rfl

theorem adjoin_le_closureAdjoin (x : L) : IntermediateField.adjoin k {x} ≤ closureAdjoin k x :=
  fun _ hy ↦ subset_closure hy

theorem mem_closureAdjoin_self (x : L) : x ∈ closureAdjoin k x :=
  adjoin_le_closureAdjoin x (IntermediateField.mem_adjoin_simple_self k x)

theorem isClosed_closureAdjoin (x : L) : IsClosed (closureAdjoin k x : Set L) := isClosed_closure

/-- `\overline{k(x)}` is contained in every closed intermediate field containing `x`. -/
theorem closureAdjoin_le {x : L} {E : IntermediateField k L} (hE : IsClosed (E : Set L))
    (hx : x ∈ E) : closureAdjoin k x ≤ E :=
  fun _ hy ↦ closure_minimal (show (IntermediateField.adjoin k {x} : Set L) ⊆ E from
    IntermediateField.adjoin_simple_le_iff.mpr hx) hE hy

theorem closureAdjoin_le_closureAdjoin {x y : L} (h : y ∈ closureAdjoin k x) :
    closureAdjoin k y ≤ closureAdjoin k x :=
  closureAdjoin_le (isClosed_closureAdjoin x) h

instance completeSpace_closureAdjoin [CompleteSpace L] (x : L) :
    CompleteSpace (closureAdjoin k x) :=
  (isClosed_closureAdjoin x).completeSpace_coe

/-- **Density in a subfield**: for an intermediate field `S` and `x ∈ S`, `k(x)` is dense in `S`
iff `S` is contained in the closure of `k(x)` in `L`. -/
theorem dense_adjoin_iff {B : Type*} [Field B] [Algebra B L] [Algebra k B] [IsScalarTower k B L]
    (S : IntermediateField B L) {x : L} (hx : x ∈ S) :
    Dense (IntermediateField.adjoin k {(⟨x, hx⟩ : S)} : Set S) ↔
      (S : Set L) ⊆ closure (IntermediateField.adjoin k {x} : Set L) := by
  have himage : ((↑) : S → L) '' (IntermediateField.adjoin k {(⟨x, hx⟩ : S)} : Set S) =
      (IntermediateField.adjoin k {x} : Set L) := by
    have := IntermediateField.adjoin_map k {(⟨x, hx⟩ : S)} ((S.val).restrictScalars k)
    rw [Set.image_singleton] at this
    exact congrArg (fun E : IntermediateField k L ↦ (E : Set L)) this
  rw [Subtype.dense_iff]
  exact Iff.of_eq (congrArg (fun T : Set L ↦ (S : Set L) ⊆ closure T) himage)

/-- `k(x)` is dense in `\overline{k(x)}`. -/
theorem dense_adjoin_closureAdjoin (x : L) :
    Dense (IntermediateField.adjoin k {(⟨x, mem_closureAdjoin_self x⟩ : closureAdjoin k x)} :
      Set (closureAdjoin k x)) :=
  (dense_adjoin_iff (closureAdjoin k x) (mem_closureAdjoin_self x)).mpr subset_rfl

end Closure

/-! ### Normed structures on intermediate fields -/

section IntermediateFieldNormed

/-- An intermediate field of a normed algebra over a nontrivially normed field is a nontrivially
normed field. -/
instance nontriviallyNormedFieldIntermediateField {k L : Type*} [NontriviallyNormedField k]
    [NormedField L] [NormedAlgebra k L] (E : IntermediateField k L) :
    NontriviallyNormedField E :=
  { (inferInstance : NormedField E) with
    non_trivial := by
      obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := k)
      exact ⟨algebraMap k E c, by rwa [norm_algebraMap']⟩ }

/-- For a tower `k → B → L` of fields with `L` a normed `k`-algebra, an intermediate field of `L/B`
is a normed `k`-algebra. Not an instance; introduce it with `letI` where needed. -/
abbrev normedAlgebraOfTower (k : Type*) {B L : Type*} [NormedField k] [Field B] [NormedField L]
    [NormedAlgebra k L] [Algebra B L] [Algebra k B] [IsScalarTower k B L]
    (M : IntermediateField B L) : NormedAlgebra k M :=
  { (inferInstance : Algebra k M) with
    norm_smul_le := fun c x ↦ by
      change ‖((c • x : M) : L)‖ ≤ ‖c‖ * ‖(x : L)‖
      exact (norm_smul_le c (x : L)) }

end IntermediateFieldNormed

/-! ### One-dimensional fields and unramified extensions -/

section Defs

variable (k L : Type*) [Field k] [NormedField L] [Algebra k L]

/-- An analytic `k`-field `L` is **one-dimensional** (Temkin, lines 3664–3666) if it is finite
over `\overline{k(y)}` for some `y ∉ k`. -/
def IsOneDimensional : Prop :=
  ∃ y : L, y ∉ Set.range (algebraMap k L) ∧ FiniteDimensional (closureAdjoin k y) L

variable (K : Type*) [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]

/-- A finite extension `L/K` of non-archimedean normed fields is **unramified** if
`f_{L/K} = [L : K]` and the residue field extension is separable (Temkin, Lemma 2.1.5(ii); for
complete `K` this is equivalent to being standard-unramified). -/
structure IsUnramified (K L : Type*) [NormedField K] [IsUltrametricDist K] [NormedField L]
    [IsUltrametricDist L] [NormedAlgebra K L] : Prop where
  finiteDimensional : FiniteDimensional K L
  inertiaDegree_eq : inertiaDegree K L = finrank K L
  isSeparable : Algebra.IsSeparable (ResidueField (unitBall K)) (ResidueField (unitBall L))

end Defs

/-! ### Fields with the residue field or the value group of `k` -/

section Constant

variable (k K : Type*) [NormedField k] [NormedField K] [NormedAlgebra k K]

/-- `K` has the **residue field of `k`**: every element of `K°` is congruent modulo `K°°` to an
element of `k°`. -/
def IsResidueTrivial : Prop :=
  ∀ x : K, ‖x‖ ≤ 1 → ∃ c : k, ‖c‖ ≤ 1 ∧ ‖x - algebraMap k K c‖ < 1

/-- `K` has the **value group of `k`**: `|K| = |k|`. -/
def IsValueTrivial : Prop := ∀ x : K, ∃ c : k, ‖c‖ = ‖x‖

/-- `K` is **`k`-immediate**: every `x ≠ 0` admits `c ∈ k` with `‖x - c‖ < ‖x‖`. -/
def IsImmediateOver : Prop := ∀ x : K, x ≠ 0 → ∃ c : k, ‖x - algebraMap k K c‖ < ‖x‖

variable {k K}

section Ultra

variable [IsUltrametricDist K]

theorem IsImmediateOver.isValueTrivial (h : IsImmediateOver k K) : IsValueTrivial k K := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨c, hc⟩ := h x hx
  exact ⟨c, by rw [← norm_algebraMap' K c]; exact norm_eq_of_norm_sub_lt hc⟩

theorem IsImmediateOver.isResidueTrivial (h : IsImmediateOver k K) : IsResidueTrivial k K := by
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact ⟨0, by simpa using hlt⟩
  obtain ⟨c, hc⟩ := h x hx0
  have hcn : ‖c‖ = 1 := by rw [← norm_algebraMap' K c, norm_eq_of_norm_sub_lt hc, heq]
  exact ⟨c, hcn.le, by rwa [heq] at hc⟩

omit [IsUltrametricDist K] in
theorem isImmediateOver_of_isResidueTrivial (hr : IsResidueTrivial k K) (hv : IsValueTrivial k K) :
    IsImmediateOver k K := by
  intro x hx
  obtain ⟨c₁, hc₁⟩ := hv x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc₁0 : algebraMap k K c₁ ≠ 0 := by
    intro h0
    rw [← norm_algebraMap' K c₁, h0, norm_zero] at hc₁
    exact hxpos.ne hc₁
  have hxc : ‖x / algebraMap k K c₁‖ = 1 := by
    rw [norm_div, norm_algebraMap', hc₁, div_self hxpos.ne']
  obtain ⟨c₂, -, hc₂⟩ := hr _ hxc.le
  refine ⟨c₁ * c₂, ?_⟩
  have heq : x - algebraMap k K (c₁ * c₂) =
      algebraMap k K c₁ * (x / algebraMap k K c₁ - algebraMap k K c₂) := by
    rw [map_mul, mul_sub, mul_div_cancel₀ _ hc₁0]
  rw [heq, norm_mul, norm_algebraMap', hc₁]
  exact mul_lt_of_lt_one_right hxpos hc₂

/-- `K` is `k`-immediate iff it has the residue field and the value group of `k`. -/
theorem isImmediateOver_iff :
    IsImmediateOver k K ↔ IsResidueTrivial k K ∧ IsValueTrivial k K :=
  ⟨fun h ↦ ⟨h.isResidueTrivial, h.isValueTrivial⟩,
    fun h ↦ isImmediateOver_of_isResidueTrivial h.1 h.2⟩

end Ultra

/-- **Type 4 generators of `k`-immediate fields**: if `K` is `k`-immediate, `k` is complete,
`x ∉ k` and `k(x)` is dense in `K`, then `x` is a type 4 generator. -/
theorem IsImmediateOver.isTypeFourGenerator [CompleteSpace k] (h : IsImmediateOver k K) {x : K}
    (hx : x ∉ Set.range (algebraMap k K))
    (hd : Dense (IntermediateField.adjoin k {x} : Set K)) : IsTypeFourGenerator k x := by
  have hna : ∀ a : k, ∃ a' : k, ‖x - algebraMap k K a'‖ < ‖x - algebraMap k K a‖ := by
    intro a
    have hxa : x - algebraMap k K a ≠ 0 := fun h0 ↦ hx ⟨a, (sub_eq_zero.mp h0).symm⟩
    obtain ⟨c, hc⟩ := h _ hxa
    exact ⟨a + c, by rwa [map_add, ← sub_sub]⟩
  exact ⟨hd, hna, radius_pos_of_completeSpace hna⟩

end Constant

/-! ### Finite extensions -/

section Finite

variable {k K L : Type*} [NontriviallyNormedField k] [IsUltrametricDist k] [IsAlgClosed k]
  [NormedField K] [IsUltrametricDist K] [NormedAlgebra k K]
  [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [NormedAlgebra k L]
  [IsScalarTower k K L] [FiniteDimensional K L]

/-- The residue field of an algebraically closed non-trivially normed field is algebraically
closed. -/
theorem isAlgClosed_residueField_unitBall (k : Type*) [NontriviallyNormedField k]
    [IsUltrametricDist k] [IsAlgClosed k] : IsAlgClosed (ResidueField (unitBall k)) :=
  isAlgClosed_residueField_of_ne_top (unitBall k) (unitBall_ne_top k)

/-- An element algebraic over an algebraically closed subfield lies in it. -/
theorem mem_range_of_isAlgebraic_of_isAlgClosed {E F : Type*} [Field E] [Field F] [Algebra E F]
    [IsAlgClosed E] {x : F} (hx : IsAlgebraic E x) : x ∈ (algebraMap E F).range := by
  rw [← minpoly.natDegree_eq_one_iff]
  exact Polynomial.natDegree_eq_of_degree_eq_some
    (IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hx.isIntegral))

omit [IsAlgClosed k] in
/-- If `K` has the residue field of `k`, the residue map `k̃ → K̃` is surjective. -/
theorem IsResidueTrivial.surjective_algebraMap (h : IsResidueTrivial k K) :
    Function.Surjective
      (algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall K))) := by
  intro w
  obtain ⟨y, rfl⟩ := residue_surjective w
  obtain ⟨c, hc1, hc⟩ := h y (norm_coe_unitBall_le_one y)
  refine ⟨residue (unitBall k) ⟨c, mem_unitBall.mpr hc1⟩, ?_⟩
  rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall, norm_sub_rev]
  exact hc

/-- **The residue field passes to finite extensions** (`k` algebraically closed). -/
theorem IsResidueTrivial.of_finiteDimensional (h : IsResidueTrivial k K) :
    IsResidueTrivial k L := by
  have := isAlgClosed_residueField_unitBall k
  have hsurj := h.surjective_algebraMap
  have hint1 : Algebra.IsIntegral (ResidueField (unitBall k)) (ResidueField (unitBall K)) :=
    ⟨fun w ↦ by obtain ⟨v, rfl⟩ := hsurj w; exact isIntegral_algebraMap⟩
  have hint2 : Algebra.IsIntegral (ResidueField (unitBall K)) (ResidueField (unitBall L)) :=
    Algebra.IsIntegral.of_finite _ _
  have hint : Algebra.IsIntegral (ResidueField (unitBall k)) (ResidueField (unitBall L)) :=
    Algebra.IsIntegral.trans (ResidueField (unitBall K))
  intro x hx
  obtain ⟨w, hw⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ResidueField (unitBall k)) (K := ResidueField (unitBall L))).2
    (residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩)
  obtain ⟨c, rfl⟩ := residue_surjective w
  refine ⟨c, norm_coe_unitBall_le_one c, ?_⟩
  rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall] at hw
  rw [norm_sub_rev]
  exact hw

omit [IsUltrametricDist k] [NormedAlgebra k K] [NormedAlgebra k L] [IsScalarTower k K L] in
/-- **The value group passes to finite extensions** (`k` algebraically closed). -/
theorem IsValueTrivial.of_finiteDimensional (h : IsValueTrivial k K) : IsValueTrivial k L := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  set u : Lˣ := Units.mk0 x hx
  set n := Nat.card (ValueGroupQuotient K L)
  have hn : 0 < n := Nat.card_pos
  have h1 : valueClass K L 1 = valueClass K L (u ^ n) := by
    rw [map_one, map_pow, pow_card_eq_one']
  obtain ⟨c, hc⟩ := valueClass_eq_valueClass_iff.mp h1
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow, Units.val_one, norm_one,
    mul_one, u] at hc
  obtain ⟨a, ha⟩ := h c
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq a hn
  refine ⟨d, ?_⟩
  have : ‖d‖ ^ n = ‖x‖ ^ n := by rw [← norm_pow, hd, ha, hc]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn.ne').mp this

/-- **`k`-immediate fields pass to finite extensions** (`k` algebraically closed). -/
theorem IsImmediateOver.of_finiteDimensional (h : IsImmediateOver k K) : IsImmediateOver k L :=
  isImmediateOver_iff.mpr ⟨h.isResidueTrivial.of_finiteDimensional,
    h.isValueTrivial.of_finiteDimensional⟩

omit [IsUltrametricDist k] [IsAlgClosed k] in
/-- If `L` is `k`-immediate, every finite extension `L/K` with `k ⊆ K` is immediate. -/
theorem IsImmediateOver.isImmediate (h : IsImmediateOver k L) : IsImmediate K L :=
  isImmediate_of_forall_exists_norm_sub_lt fun x hx ↦ by
    obtain ⟨c, hc⟩ := h x hx
    exact ⟨algebraMap k K c, by rwa [← IsScalarTower.algebraMap_apply]⟩

end Finite

/-! ### Types of generators -/

section Types

variable {k K : Type*} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]
  [IsAlgClosed k] [NormedField K] [IsUltrametricDist K] [NormedAlgebra k K]

omit [IsUltrametricDist k] [CompleteSpace k] [IsAlgClosed k] [IsUltrametricDist K] in
/-- An affine change of generator does not change `k(z)`. -/
theorem adjoin_affine_eq (z : K) (a : k) {t : k} (ht : t ≠ 0) :
    IntermediateField.adjoin k {algebraMap k K t * (z - algebraMap k K a)} =
      IntermediateField.adjoin k {z} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (sub_mem (IntermediateField.mem_adjoin_simple_self k z)
        (IntermediateField.algebraMap_mem _ _))
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hz : z = algebraMap k K t⁻¹ * (algebraMap k K t * (z - algebraMap k K a)) +
        algebraMap k K a := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul, sub_add_cancel]
    set E := IntermediateField.adjoin k {algebraMap k K t * (z - algebraMap k K a)}
    rw [hz]
    exact add_mem (mul_mem (IntermediateField.algebraMap_mem E _)
      (IntermediateField.mem_adjoin_simple_self k _)) (IntermediateField.algebraMap_mem E _)

omit [IsUltrametricDist k] [CompleteSpace k] [IsAlgClosed k] [IsUltrametricDist K] in
theorem adjoin_sub_algebraMap_eq (z : K) (a : k) :
    IntermediateField.adjoin k {z - algebraMap k K a} = IntermediateField.adjoin k {z} := by
  have := adjoin_affine_eq z a (one_ne_zero (α := k))
  rwa [map_one, one_mul] at this

/-- **Types of generators** (Temkin's types 4, 3, 2 of fields topologically generated by one
element, lines 3667–3677 and 3703–3712): if `z ∉ k` and `k(z)` is dense in `K`, then `z` is a
type 4 generator, or `z - a` is an annulus generator for some `a ∈ k`, or `t (z - a)` is a Gauss
generator for some `a ∈ k`, `t ∈ k^×`. -/
theorem isTypeFourGenerator_or_isAnnulusGenerator_or_isGaussGenerator {z : K}
    (hz : z ∉ Set.range (algebraMap k K)) (hd : Dense (IntermediateField.adjoin k {z} : Set K)) :
    IsTypeFourGenerator k z ∨ (∃ a : k, IsAnnulusGenerator k (z - algebraMap k K a)) ∨
      ∃ a t : k, t ≠ 0 ∧ IsGaussGenerator k (algebraMap k K t * (z - algebraMap k K a)) := by
  by_cases h : ∀ a : k, ∃ a' : k, ‖z - algebraMap k K a'‖ < ‖z - algebraMap k K a‖
  · exact Or.inl ⟨hd, h, radius_pos_of_completeSpace h⟩
  push Not at h
  obtain ⟨a, ha⟩ := h
  set w := z - algebraMap k K a with hw
  have hw0 : w ≠ 0 := fun h0 ↦ hz ⟨a, (sub_eq_zero.mp h0).symm⟩
  have hmin : ∀ c : k, ‖w‖ ≤ ‖w - algebraMap k K c‖ := by
    intro c
    have := ha (a + c)
    rwa [map_add, ← sub_sub] at this
  by_cases hv : ∃ c : k, ‖w‖ = ‖c‖
  · right; right
    obtain ⟨c, hc⟩ := hv
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact hw0 (norm_eq_zero.mp hc)
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    set u := algebraMap k K c⁻¹ * w with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_mul, norm_algebraMap', norm_inv, hc, inv_mul_cancel₀ hcpos.ne']
    have htr : Transcendental (ResidueField (unitBall k))
        (residue (unitBall K) ⟨u, mem_unitBall.mpr hu1.le⟩) := by
      intro halg
      have := isAlgClosed_residueField_unitBall k
      obtain ⟨v, hv⟩ := mem_range_of_isAlgebraic_of_isAlgClosed halg
      obtain ⟨d, rfl⟩ := residue_surjective v
      rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall] at hv
      have hlt : ‖w - algebraMap k K (c * d)‖ < ‖w‖ := by
        have heq : w - algebraMap k K (c * d) = algebraMap k K c * (u - algebraMap k K d) := by
          rw [hu, mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul,
            map_mul]
        rw [norm_sub_rev] at hv
        rw [heq, norm_mul, norm_algebraMap', ← hc]
        exact mul_lt_of_lt_one_right (norm_pos_iff.mpr hw0) hv
      exact (hmin (c * d)).not_gt hlt
    refine ⟨a, c⁻¹, inv_ne_zero hc0, ?_⟩
    exact { toIsGaussElement := isGaussElement_of_transcendental_residue hu1.le htr
            dense_adjoin := by rw [adjoin_affine_eq z a (inv_ne_zero hc0)]; exact hd }
  · right; left
    push Not at hv
    refine ⟨a, ⟨?_, hv⟩⟩
    rw [adjoin_sub_algebraMap_eq]
    exact hd

end Types



end DeJongAlterations.StableModification.Valuation.Analytic
