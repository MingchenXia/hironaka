/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Defect
import DeJongAlterations.StableModification.Valuation.Analytic.Hensel
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Zorn

/-!
# Coefficient fields of non-archimedean fields

Let `F` be a field with a non-archimedean absolute value. A *coefficient field* of `F` is a
subfield `F₀` contained in the closed unit ball `F°` such that the residue map `F₀ → F̃` is
surjective; it is then an isomorphism `F₀ ≃+* F̃` (`IsCoefficientField.residueEquiv`), and every
nonzero element of `F₀` has absolute value one. Coefficient fields replace, in the type 2 part of
Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition 6.2.5
(`semi-stable.tex`, lines 3794–3810), Temkin's discretely valued subfield `k₀ ⊆ k` with
`k̃₀ = k̃`: a trivially valued subfield lifting the residue field makes the lifting of residue
bases a matter of linear algebra.

No Teichmüller map is used: when `k` is perfect (for instance algebraically closed) the limit
`lim (lift of x̃^{1/pⁿ})^{pⁿ}` does not depend only on `x̃` (the lifts `y^{1/pⁿ}` of `x̃^{1/pⁿ}`
give the constant sequence `y` for every lift `y` of `x̃`), so a coefficient field is chosen by
Zorn's lemma.

## Main definitions

* `subfieldResidue F₀ hF₀`: the residue map `F₀ →+* F̃` of a subfield contained in `F°`.
* `IsCoefficientField F₀`: `F₀ ⊆ F°` and `subfieldResidue` is surjective.
* `IsCoefficientField.residueEquiv`, `IsCoefficientField.toUnitBallHom`: the isomorphism
  `F₀ ≃+* F̃` and the retraction `F° →+* F₀`, `x ↦ residueEquiv⁻¹ x̃`.

## Main results

* `norm_le_one_of_isAlgebraic`, `adjoin_le_unitBall_of_isAlgebraic`: elements algebraic over a
  subfield of the unit ball lie in the unit ball.
* `adjoin_le_unitBall_of_norm_aeval_eq_one`, `norm_aeval_eq_one_of_eval₂_ne_zero`: adjoining a
  residually transcendental element stays in the unit ball.
* `exists_isAlgebraic_residue_eq`: Hensel lifts of simple residue roots over a subfield of the
  unit ball, for complete `F`.
* `exists_maximal_le_unitBall`: maximal subfields of the unit ball (Zorn), with
  `mem_of_isAlgebraic_of_maximal`, `mem_of_norm_aeval_eq_one_of_maximal`.
* `exists_isCoefficientField_of_le`, `exists_isCoefficientField`: an algebraically closed field
  has an algebraically closed coefficient field containing any given subfield of its unit ball,
  in particular in characteristic `p`; then `isAlgClosed_residueField_of_charP`: its residue
  field is
  algebraically closed.
* `IsCoefficientField.exists_isCoefficientField_map_le`: coefficient fields lift along an
  extension `K → L` with `L` complete and `L̃/K̃` separable.

## References

Blueprint `sm-val-onedim-type2.tex`: `def:sm-an-coefficient-field`,
`lem:sm-an-unit-ball-subfield`, `lem:sm-an-unit-ball-algebraic`,
`lem:sm-an-unit-ball-transcendental`, `lem:sm-an-unit-ball-hensel`,
`lem:sm-an-unit-ball-maximal`, `prop:sm-an-coefficient-field-algclosed`,
`prop:sm-an-coefficient-field-lift`.
-/

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-- A finite sum of elements of absolute value `< C` has absolute value `< C` (non-archimedean,
`C > 0`). -/
theorem norm_finset_sum_lt {E ι : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {s : Finset ι} {f : ι → E} {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

/-! ### Subfields of the unit ball -/

section UnitBall

variable (F₀ : Subfield F) (hF₀ : ∀ x ∈ F₀, ‖x‖ ≤ 1)

/-- The inclusion of a subfield contained in the unit ball into the unit ball. -/
def subfieldToUnitBall : F₀ →+* unitBall F where
  toFun x := ⟨x, mem_unitBall.mpr (hF₀ x x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The residue map `F₀ → F̃` of a subfield contained in the unit ball. -/
def subfieldResidue : F₀ →+* ResidueField (unitBall F) :=
  (residue (unitBall F)).comp (subfieldToUnitBall F₀ hF₀)

@[simp]
theorem coe_subfieldToUnitBall (x : F₀) : (subfieldToUnitBall F₀ hF₀ x : F) = x := rfl

theorem subfieldResidue_apply (x : F₀) :
    subfieldResidue F₀ hF₀ x = residue (unitBall F) ⟨x, mem_unitBall.mpr (hF₀ x x.2)⟩ := rfl

theorem subfieldResidue_injective : Function.Injective (subfieldResidue F₀ hF₀) :=
  (subfieldResidue F₀ hF₀).injective

theorem unitBall_subtype_comp_subfieldToUnitBall :
    (unitBall F).subtype.comp (subfieldToUnitBall F₀ hF₀) = algebraMap F₀ F := rfl

variable {F₀}

include hF₀ in
omit [IsUltrametricDist F] in
/-- **Lemma (subfields of the unit ball), (1)**: a nonzero element of a subfield contained in the
unit ball has absolute value one. -/
theorem norm_eq_one_of_mem_of_le_one {x : F} (hx : x ∈ F₀) (h0 : x ≠ 0) : ‖x‖ = 1 := by
  have h1 := hF₀ x hx
  have h2 := hF₀ x⁻¹ (F₀.inv_mem hx)
  rw [norm_inv] at h2
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

include hF₀ in
omit [IsUltrametricDist F] in
/-- A subfield contained in the unit ball meets the open unit ball only in `0`. -/
theorem eq_zero_of_mem_of_norm_lt_one {x : F} (hx : x ∈ F₀) (h : ‖x‖ < 1) : x = 0 := by
  by_contra h0
  exact (norm_eq_one_of_mem_of_le_one hF₀ hx h0).not_lt h

end UnitBall

/-! ### Algebraic and residually transcendental elements -/

section Adjoin

variable {F₀ : Subfield F} (hF₀ : ∀ x ∈ F₀, ‖x‖ ≤ 1)
include hF₀

/-- **Algebraic elements over a subfield of the unit ball** lie in the unit ball. -/
theorem norm_le_one_of_isAlgebraic {x : F} (hx : IsAlgebraic F₀ x) : ‖x‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hint := hx.isIntegral
  have hm : (minpoly F₀ x).Monic := minpoly.monic hint
  have h0 : aeval x (minpoly F₀ x) = 0 := minpoly.aeval F₀ x
  set n := (minpoly F₀ x).natDegree
  rw [hm.as_sum] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have hxn : 0 < ‖x ^ n‖ := by
    rw [norm_pow]
    exact pow_pos (one_pos.trans h) n
  have hsum : ‖∑ i ∈ Finset.range n, algebraMap F₀ F ((minpoly F₀ x).coeff i) * x ^ i‖ <
      ‖x ^ n‖ := by
    refine norm_finset_sum_lt hxn fun i hi ↦ ?_
    rw [norm_mul, norm_pow, norm_pow]
    have hc : ‖algebraMap F₀ F ((minpoly F₀ x).coeff i)‖ ≤ 1 :=
      hF₀ _ ((minpoly F₀ x).coeff i).2
    have hi' : i < n := Finset.mem_range.mp hi
    calc ‖algebraMap F₀ F ((minpoly F₀ x).coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ n := pow_lt_pow_right₀ h hi'
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsum.ne'
  rw [h0, norm_zero, max_eq_left hsum.le] at heq
  exact hxn.ne' heq.symm

/-- The field generated over a subfield of the unit ball by an algebraic element lies in the unit
ball. -/
theorem adjoin_le_unitBall_of_isAlgebraic {x : F} (hx : IsAlgebraic F₀ x) :
    ∀ y ∈ F₀⟮x⟯, ‖y‖ ≤ 1 := by
  have : Algebra.IsAlgebraic F₀ F₀⟮x⟯ := IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
  intro y hy
  have hy' : IsAlgebraic F₀ (⟨y, hy⟩ : F₀⟮x⟯) := Algebra.IsAlgebraic.isAlgebraic _
  exact norm_le_one_of_isAlgebraic hF₀ ((isAlgebraic_algebraMap_iff
    (algebraMap F₀⟮x⟯ F).injective).mpr hy')

omit hF₀ [IsUltrametricDist F] in
/-- **Residually transcendental elements, (1)**: if `‖g(x)‖ = 1` for every nonzero polynomial `g`
over a field `R`, then `R(x)` lies in the unit ball. -/
theorem adjoin_le_unitBall_of_norm_aeval_eq_one {R : Type*} [Field R] [Algebra R F] {x : F}
    (h : ∀ g : R[X], g ≠ 0 → ‖aeval x g‖ = 1) : ∀ y ∈ R⟮x⟯, ‖y‖ ≤ 1 := by
  have hval : ∀ g : R[X], ‖aeval x g‖ ≤ 1 := fun g ↦ by
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · exact (h g hg).le
  intro y hy
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff R y).mp hy
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [norm_div, h s hs, div_one]
    exact hval r

omit hF₀ in
/-- Evaluating a polynomial over `F₀ ⊆ F°` at `x ∈ F°` inside the unit ball. -/
theorem coe_eval₂_subfieldToUnitBall (hF₀ : ∀ x ∈ F₀, ‖x‖ ≤ 1) (g : F₀[X]) (x : unitBall F) :
    ((g.eval₂ (subfieldToUnitBall F₀ hF₀) x : unitBall F) : F) = aeval (x : F) g := by
  change (unitBall F).subtype (g.eval₂ (subfieldToUnitBall F₀ hF₀) x) = _
  rw [hom_eval₂, unitBall_subtype_comp_subfieldToUnitBall, aeval_def]
  rfl

/-- Evaluation commutes with the residue map: for `g ∈ F₀[X]` and `x ∈ F°`, the residue of
`g(x)` is the value at `x̃` of the residue polynomial of `g`. -/
theorem residue_eval₂_subfieldToUnitBall (g : F₀[X]) (x : unitBall F) :
    residue (unitBall F) (g.eval₂ (subfieldToUnitBall F₀ hF₀) x) =
      g.eval₂ (subfieldResidue F₀ hF₀) (residue (unitBall F) x) := by
  rw [hom_eval₂]
  rfl

/-- **Residually transcendental elements, (2)**: if `x ∈ F°` and `x̃` is transcendental over the
residues of `F₀`, then `‖g(x)‖ = 1` for every nonzero `g ∈ F₀[X]`. -/
theorem norm_aeval_eq_one_of_eval₂_ne_zero (x : unitBall F)
    (h : ∀ g : F₀[X], g ≠ 0 → g.eval₂ (subfieldResidue F₀ hF₀) (residue (unitBall F) x) ≠ 0)
    (g : F₀[X]) (hg : g ≠ 0) : ‖aeval (x : F) g‖ = 1 := by
  rw [← coe_eval₂_subfieldToUnitBall hF₀]
  refine norm_eq_one_of_residue_ne_zero ?_
  rw [residue_eval₂_subfieldToUnitBall]
  exact h g hg

/-- **Hensel lifts over a subfield of the unit ball.** Let `F` be complete and `F₀ ⊆ F°`. A simple
root `β` of a monic polynomial `ḡ ∈ F̃[X]` whose coefficients are residues of elements of `F₀` is
the residue of an element of `F°` algebraic over `F₀`. -/
theorem exists_isAlgebraic_residue_eq [CompleteSpace F] (g : (ResidueField (unitBall F))[X])
    (hg : g.Monic) (hcoeff : ∀ n, g.coeff n ∈ Set.range (subfieldResidue F₀ hF₀))
    {β : ResidueField (unitBall F)} (hβ : g.eval β = 0) (hβ' : g.derivative.eval β ≠ 0) :
    ∃ x : unitBall F, residue (unitBall F) x = β ∧ IsAlgebraic F₀ (x : F) := by
  obtain ⟨G, hGg, -, hG⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts g).mpr hcoeff) hg
  set H : (unitBall F)[X] := G.map (subfieldToUnitBall F₀ hF₀) with hH
  have hHmonic : H.Monic := hG.map _
  have hmapH : H.map (residue (unitBall F)) = g := by
    rw [hH, Polynomial.map_map]
    exact hGg
  have h1 : aeval β H = 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, eval₂_eq_eval_map, hmapH, hβ]
  have h2 : aeval β (derivative H) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, eval₂_eq_eval_map, ← Polynomial.derivative_map,
      hmapH]
    exact hβ'
  obtain ⟨x, hx, hxβ⟩ := exists_isRoot_residue_eq H hHmonic β h1 h2
  refine ⟨x, hxβ, G, hG.ne_zero, ?_⟩
  have hx' : H.eval x = 0 := hx
  rw [hH, eval_map] at hx'
  rw [← coe_eval₂_subfieldToUnitBall hF₀, hx']
  rfl

end Adjoin

/-! ### Maximal subfields of the unit ball -/

section Maximal

omit [IsUltrametricDist F] in
/-- **Maximal subfields of the unit ball** (Zorn): every subfield contained in the unit ball is
contained in a maximal one. -/
theorem exists_maximal_le_unitBall (F₀ : Subfield F) (hF₀ : ∀ x ∈ F₀, ‖x‖ ≤ 1) :
    ∃ F₁ : Subfield F, F₀ ≤ F₁ ∧ Maximal (fun F' : Subfield F ↦ ∀ x ∈ F', ‖x‖ ≤ 1) F₁ := by
  refine zorn_le_nonempty₀ {F' : Subfield F | ∀ x ∈ F', ‖x‖ ≤ 1} ?_ F₀ hF₀
  intro c hc hchain y hy
  refine ⟨sSup c, fun x hx ↦ ?_, fun z hz ↦ le_sSup hz⟩
  obtain ⟨s, hs, hxs⟩ := (Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hchain.directedOn).mp hx
  exact hc hs x hxs

variable {F₁ : Subfield F} (hmax : Maximal (fun F' : Subfield F ↦ ∀ x ∈ F', ‖x‖ ≤ 1) F₁)
include hmax

omit [IsUltrametricDist F] in
/-- A maximal subfield of the unit ball contains every element `x` such that `F₁(x)` lies in the
unit ball. -/
theorem mem_of_adjoin_le_unitBall_of_maximal {x : F} (hx : ∀ y ∈ F₁⟮x⟯, ‖y‖ ≤ 1) : x ∈ F₁ := by
  have hle : F₁ ≤ (F₁⟮x⟯).toSubfield := fun y hy ↦
    (F₁⟮x⟯).algebraMap_mem (⟨y, hy⟩ : F₁)
  exact hmax.2 hx hle (IntermediateField.mem_adjoin_simple_self F₁ x)

/-- A maximal subfield of the unit ball is relatively algebraically closed. -/
theorem mem_of_isAlgebraic_of_maximal {x : F} (hx : IsAlgebraic F₁ x) : x ∈ F₁ :=
  mem_of_adjoin_le_unitBall_of_maximal hmax (adjoin_le_unitBall_of_isAlgebraic hmax.1 hx)

omit [IsUltrametricDist F] in
/-- A maximal subfield of the unit ball contains every residually transcendental element. -/
theorem mem_of_norm_aeval_eq_one_of_maximal {x : F}
    (hx : ∀ g : F₁[X], g ≠ 0 → ‖aeval x g‖ = 1) : x ∈ F₁ :=
  mem_of_adjoin_le_unitBall_of_maximal hmax (adjoin_le_unitBall_of_norm_aeval_eq_one hx)

end Maximal

/-! ### Coefficient fields -/

section CoefficientField

/-- A **coefficient field** of a non-archimedean field `F`: a subfield `F₀ ⊆ F°` whose residue
map `F₀ → F̃` is surjective (hence bijective). -/
structure IsCoefficientField (F₀ : Subfield F) : Prop where
  /-- `F₀` lies in the closed unit ball. -/
  norm_le_one : ∀ x ∈ F₀, ‖x‖ ≤ 1
  /-- The residue map of `F₀` is surjective. -/
  surjective : Function.Surjective (subfieldResidue F₀ norm_le_one)

namespace IsCoefficientField

variable {F₀ : Subfield F} (hF₀ : IsCoefficientField F₀)

/-- The residue isomorphism `F₀ ≃+* F̃` of a coefficient field. -/
def residueEquiv : F₀ ≃+* ResidueField (unitBall F) :=
  RingEquiv.ofBijective (subfieldResidue F₀ hF₀.norm_le_one)
    ⟨subfieldResidue_injective F₀ hF₀.norm_le_one, hF₀.surjective⟩

theorem residueEquiv_apply (x : F₀) :
    hF₀.residueEquiv x = subfieldResidue F₀ hF₀.norm_le_one x := rfl

/-- The residue of the element of `F₀` lifting `y ∈ F̃` is `y`. -/
theorem residue_residueEquiv_symm (y : ResidueField (unitBall F)) :
    residue (unitBall F) ⟨(hF₀.residueEquiv.symm y : F),
      mem_unitBall.mpr (hF₀.norm_le_one _ (hF₀.residueEquiv.symm y).2)⟩ = y :=
  hF₀.residueEquiv.apply_symm_apply y

/-- The retraction `F° →+* F₀`, `x ↦ residueEquiv⁻¹ x̃`. -/
def toUnitBallHom : unitBall F →+* F₀ :=
  hF₀.residueEquiv.symm.toRingHom.comp (residue (unitBall F))

theorem residue_toUnitBallHom (x : unitBall F) :
    residue (unitBall F) ⟨(hF₀.toUnitBallHom x : F),
      mem_unitBall.mpr (hF₀.norm_le_one _ (hF₀.toUnitBallHom x).2)⟩ = residue (unitBall F) x :=
  hF₀.residue_residueEquiv_symm _

/-- `‖x - σ(x)‖ < 1` for the retraction `σ = toUnitBallHom`. -/
theorem norm_sub_toUnitBallHom_lt_one (x : unitBall F) :
    ‖(x : F) - hF₀.toUnitBallHom x‖ < 1 := by
  have h := residue_eq_residue_iff.mp (hF₀.residue_toUnitBallHom x).symm
  simpa using h

include hF₀ in
/-- Every element of the unit ball is congruent modulo the open unit ball to an element of a
coefficient field. -/
theorem exists_mem_norm_sub_lt_one {x : F} (hx : ‖x‖ ≤ 1) : ∃ y ∈ F₀, ‖x - y‖ < 1 :=
  ⟨_, (hF₀.toUnitBallHom ⟨x, mem_unitBall.mpr hx⟩).2,
    hF₀.norm_sub_toUnitBallHom_lt_one ⟨x, mem_unitBall.mpr hx⟩⟩

end IsCoefficientField

/-- **Coefficient fields of algebraically closed fields.** Every subfield `F₁` of the unit ball of
an algebraically closed field is contained in an algebraically closed coefficient field. -/
theorem exists_isCoefficientField_of_le [IsAlgClosed F] (F₁ : Subfield F)
    (hF₁ : ∀ x ∈ F₁, ‖x‖ ≤ 1) :
    ∃ F₀ : Subfield F, F₁ ≤ F₀ ∧ IsCoefficientField F₀ ∧ IsAlgClosed F₀ := by
  obtain ⟨F₀, hle, hmax⟩ := exists_maximal_le_unitBall F₁ hF₁
  have hF₀ := hmax.1
  have halg : IsAlgClosed F₀ := by
    refine IsAlgClosed.of_exists_root F₀ fun p hmon hirr ↦ ?_
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero F p (degree_pos_of_irreducible hirr).ne'
    have hαF₀ : α ∈ F₀ := mem_of_isAlgebraic_of_maximal hmax ⟨p, hmon.ne_zero, hα⟩
    refine ⟨⟨α, hαF₀⟩, (algebraMap F₀ F).injective ?_⟩
    rw [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact hα
  refine ⟨F₀, hle, ⟨hF₀, fun β ↦ ?_⟩, halg⟩
  by_contra hβ
  obtain ⟨x, rfl⟩ := residue_surjective β
  have htr : ∀ g : F₀[X], g ≠ 0 →
      g.eval₂ (subfieldResidue F₀ hF₀) (residue (unitBall F) x) ≠ 0 := by
    intro g hg
    have key : ∀ g : F₀[X],
        g.eval₂ (subfieldResidue F₀ hF₀) (residue (unitBall F) x) = 0 → g = 0 := by
      intro g
      induction g using induction_on_X_sub_C_mul with
      | hC c =>
        intro h
        rw [eval₂_C] at h
        rw [(map_eq_zero_iff _ (subfieldResidue_injective F₀ hF₀)).mp h, C_0]
      | hmul a g ih =>
        intro h
        rw [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C, mul_eq_zero] at h
        rcases h with h | h
        · exact absurd ⟨a, (sub_eq_zero.mp h).symm⟩ hβ
        · rw [ih h, mul_zero]
    exact fun h ↦ hg (key g h)
  have hx : (x : F) ∈ F₀ :=
    mem_of_norm_aeval_eq_one_of_maximal hmax (norm_aeval_eq_one_of_eval₂_ne_zero hF₀ x htr)
  exact hβ ⟨⟨x, hx⟩, rfl⟩

omit [IsUltrametricDist F] in
/-- In characteristic `p`, the prime field lies in the unit ball. -/
theorem norm_le_one_of_mem_fieldRange_zmod (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∀ x ∈ (ZMod.castHom (dvd_refl p) F).fieldRange, ‖x‖ ≤ 1 := by
  rintro _ ⟨n, rfl⟩
  have hpow : (ZMod.castHom (dvd_refl p) F n) ^ p = ZMod.castHom (dvd_refl p) F n := by
    rw [← map_pow, ZMod.pow_card]
  by_contra h
  rw [not_le] at h
  have hlt : ‖ZMod.castHom (dvd_refl p) F n‖ ^ 1 < ‖ZMod.castHom (dvd_refl p) F n‖ ^ p :=
    pow_lt_pow_right₀ h (Fact.out : p.Prime).one_lt
  rw [pow_one, ← norm_pow, hpow] at hlt
  exact lt_irrefl _ hlt

/-- **Coefficient fields in characteristic `p`.** An algebraically closed non-archimedean field of
characteristic `p` has an algebraically closed coefficient field. -/
theorem exists_isCoefficientField [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ F₀ : Subfield F, IsCoefficientField F₀ ∧ IsAlgClosed F₀ := by
  obtain ⟨F₀, -, h, h'⟩ := exists_isCoefficientField_of_le _
    (norm_le_one_of_mem_fieldRange_zmod (F := F) p)
  exact ⟨F₀, h, h'⟩

/-- The residue field of an algebraically closed non-archimedean field of characteristic `p` is
algebraically closed. -/
theorem isAlgClosed_residueField_of_charP [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    IsAlgClosed (ResidueField (unitBall F)) := by
  obtain ⟨F₀, h, h'⟩ := exists_isCoefficientField (F := F) p
  exact IsAlgClosed.of_ringEquiv F₀ _ h.residueEquiv

/-- **Lifting coefficient fields along separable residue extensions.** Let `K → L` be an
extension of non-archimedean fields with `L` complete and `L̃/K̃` separable. Every coefficient
field `K₀` of `K` is contained (through `K → L`) in a coefficient field of `L`. -/
theorem IsCoefficientField.exists_isCoefficientField_map_le {K L : Type*} [NormedField K]
    [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L]
    [Algebra.IsSeparable (ResidueField (unitBall K)) (ResidueField (unitBall L))]
    {K₀ : Subfield K} (hK₀ : IsCoefficientField K₀) :
    ∃ L₀ : Subfield L, K₀.map (algebraMap K L) ≤ L₀ ∧ IsCoefficientField L₀ := by
  have hF₀ : ∀ x ∈ K₀.map (algebraMap K L), ‖x‖ ≤ 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [norm_algebraMap']
    exact hK₀.norm_le_one y hy
  obtain ⟨L₀, hle, hmax⟩ := exists_maximal_le_unitBall _ hF₀
  have hL₀ := hmax.1
  refine ⟨L₀, hle, hL₀, fun β ↦ ?_⟩
  have hsep : IsSeparable (ResidueField (unitBall K)) β := Algebra.IsSeparable.isSeparable _ β
  set m := minpoly (ResidueField (unitBall K)) β
  have hmon : m.Monic := minpoly.monic hsep.isIntegral
  set g := m.map (algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L)))
  have hg : g.Monic := hmon.map _
  have hgβ : g.eval β = 0 := by
    rw [eval_map_algebraMap]
    exact minpoly.aeval _ β
  have hgβ' : g.derivative.eval β ≠ 0 := by
    rw [Polynomial.derivative_map, eval_map]
    exact Polynomial.Separable.eval₂_derivative_ne_zero _ hsep
      (by rw [← aeval_def]; exact minpoly.aeval _ β)
  have hcoeff : ∀ n, g.coeff n ∈ Set.range (subfieldResidue L₀ hL₀) := by
    intro n
    obtain ⟨⟨y, hyK₀⟩, hy⟩ := hK₀.surjective (m.coeff n)
    have hyL : algebraMap K L y ∈ L₀ := hle ⟨y, hyK₀, rfl⟩
    refine ⟨⟨algebraMap K L y, hyL⟩, ?_⟩
    rw [coeff_map, ← hy, subfieldResidue_apply, subfieldResidue_apply, algebraMap_residue]
    rfl
  obtain ⟨x, hxβ, hxalg⟩ := exists_isAlgebraic_residue_eq hL₀ g hg hcoeff hgβ hgβ'
  have hx : (x : L) ∈ L₀ := mem_of_isAlgebraic_of_maximal hmax hxalg
  exact ⟨⟨x, hx⟩, hxβ⟩

end CoefficientField

end DeJongAlterations.StableModification.Valuation.Analytic
