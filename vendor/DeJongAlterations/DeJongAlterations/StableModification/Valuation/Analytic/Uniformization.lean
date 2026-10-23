/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.OneDimTypes
import DeJongAlterations.StableModification.Valuation.Analytic.CoefficientField
import DeJongAlterations.StableModification.Valuation.FunctionField.PoleNorm

/-!
# Uniformization of one-dimensional analytic fields

Let `k` be an algebraically closed complete non-archimedean field of exponential characteristic
`p` with residue field of the same exponential characteristic (equal characteristic). This file
proves the uniformization of one-dimensional analytic `k`-fields, M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010):

* `IsOneDimensional.exists_isUnramified` (**Theorem 6.3.1(i)**, `semi-stable.tex`, statement
  lines 3987–3996, proof lines 4051–4065 and 4089–4112): every one-dimensional analytic `k`-field
  `L` has an element `x ∉ k` such that `L` is finite and unramified over `\overline{k(x)}`;
  moreover `x` is a type 4 generator of `L`, an annulus generator of `L`, or a Gauss generator of
  `\overline{k(x)}`.
* `isUnramified_closureAdjoin_of_transcendental` (**Theorem 2.1.10(iii)**): if `x ∈ L°` has a
  residue `x̃` transcendental over `k̃` and `L̃/k̃(x̃)` is separable, then `L` is unramified over
  `\overline{k(x)}`.
* `uniformization_analytic` (**Theorem 2.1.10**, lines 2075–2086, proof lines 4144–4153): for an
  analytic `k`-field `L` finite over `\overline{k(y)}` for some `y`, (i) `L` is unramified over
  some `\overline{k(x)}`, (ii) the same holds for all `x'` close to `x`, and (iii) as above.

The proofs of Theorem 2.1.10 in characteristic `0` and in the degenerate case `y ∈ k` (then
`L = k`) are included; the hypothesis `K̃ ≠ k̃` of Temkin's 2.1.10(iii) is omitted, as it follows
from the transcendence of `x̃`. Theorem 6.3.1(iii) (stability) is in `OneDimStable.lean`.

The proof of Theorem 6.3.1(i) follows plan simplification S5 (`PLAN-SM-VAL.md`): by the type
trichotomy `isTypeFourGenerator_or_isAnnulusGenerator_or_isGaussGenerator`, `\overline{k(y)}` is
of type 4, 3 or 2; the type 4 case is `IsTypeFourGenerator.exists_isTypeFourGenerator`; in the
type 3 case a generator `x` of the value group of `L` (`exists_forall_norm_eq_zpow_mul`) makes
`L/\overline{k(x)}` immediate, hence trivial (`IsAnnulusGenerator.finrank_eq_one_of_isImmediate`);
in the type 2 case a separating transcendental residue (`IsFunctionFieldOneVar.exists_isSeparable`)
is lifted to a Gauss generator over which `L` is unramified (`IsGaussGenerator.isUnramified`).

## References

Blueprint chapter `sm-val-onedim.tex`: `thm:sm-an-unramified-generator`,
`thm:sm-an-uniformization-light`.
-/

noncomputable section

open IsLocalRing Polynomial Module Topology
open scoped IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

open DeJongAlterations.StableModification.Valuation.FunctionField (IsFunctionFieldOneVar)

/-! ### Auxiliary facts -/

section Trivial

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-- An extension `L/K` with `K → L` surjective is unramified. -/
theorem isUnramified_of_forall_mem_range (h : ∀ y : L, y ∈ Set.range (algebraMap K L)) :
    IsUnramified K L := by
  have hbt : (⊥ : IntermediateField K L) = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    obtain ⟨c, rfl⟩ := h y
    exact IntermediateField.algebraMap_mem _ c
  have h1 : finrank K L = 1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hbt
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [h1]; exact Nat.one_pos)
  have hf : inertiaDegree K L = 1 := le_antisymm (inertiaDegree_le_finrank.trans h1.le)
    (by rw [inertiaDegree_def]; exact Module.finrank_pos)
  refine ⟨this, by rw [hf, h1], ?_⟩
  have hr : (⊥ : IntermediateField (ResidueField (unitBall K)) (ResidueField (unitBall L))) = ⊤ :=
    IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr (by rw [← inertiaDegree_def]; exact hf)
  refine (separableClosure.eq_top_iff _ _).mp (eq_top_iff.mpr ?_)
  rw [← hr]
  exact bot_le

end Trivial

section Radius

variable {k K : Type*} [NormedField k] [CompleteSpace k] [NormedField K] [NormedAlgebra k K]

/-- Over a complete field `k`, every `z ∉ k` has positive radius `r(z) = inf_{a ∈ k} ‖z - a‖`. -/
theorem radius_pos_of_notMem_range {z : K} (hz : z ∉ Set.range (algebraMap k K)) :
    0 < radius k z := by
  by_contra hr
  have hr0 : radius k z = 0 := le_antisymm (not_lt.mp hr) (radius_nonneg z)
  have hcl : IsClosed (Set.range (algebraMap k K)) :=
    (algebraMap_isometry k K).isUniformInducing.isComplete_range.isClosed
  apply hz
  rw [← hcl.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha⟩ := exists_norm_sub_lt_of_radius_lt (k := k) (z := z) (t := ε) (by rwa [hr0])
  exact ⟨algebraMap k K a, ⟨a, rfl⟩, by rwa [dist_eq_norm]⟩

end Radius

section GaussClosure

variable {k L : Type*} [NormedField k] [NormedField L] [NormedAlgebra k L]

/-- A Gauss element `x` of `L` is a Gauss generator of `\overline{k(x)}`. -/
theorem isGaussGenerator_closureAdjoin {x : L} (hx : IsGaussElement k x) :
    IsGaussGenerator k (⟨x, mem_closureAdjoin_self x⟩ : closureAdjoin k x) where
  norm_le_one := hx.norm_le_one
  norm_coeff_le g i := by
    have h : ((aeval (⟨x, mem_closureAdjoin_self x⟩ : closureAdjoin k x) g : closureAdjoin k x) :
        L) = aeval x g :=
      (aeval_algHom_apply (closureAdjoin k x).val _ g).symm
    exact (hx.norm_coeff_le g i).trans_eq (congrArg norm h.symm)
  dense_adjoin := dense_adjoin_closureAdjoin x

end GaussClosure

section Separable

set_option linter.style.haveILetI false in
/-- Separability passes to larger base fields: if `F → L` is a tower over `k` and the image of `F`
contains an intermediate field `E` of `L/k` over which `L` is separable, then `L/F` is
separable. -/
theorem isSeparable_of_le_fieldRange {k F L : Type*} [Field k] [Field F] [Field L] [Algebra k F]
    [Algebra F L] [Algebra k L] [IsScalarTower k F L] {E : IntermediateField k L}
    (hE : E ≤ (IsScalarTower.toAlgHom k F L).fieldRange) [Algebra.IsSeparable E L] :
    Algebra.IsSeparable F L := by
  set φ := IsScalarTower.toAlgHom k F L with hφ
  letI : Algebra E F :=
    (φ.equivFieldRange.symm.toAlgHom.toRingHom.comp
      (IntermediateField.inclusion hE).toRingHom).toAlgebra
  haveI : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change (a : L) = φ (φ.equivFieldRange.symm (IntermediateField.inclusion hE a))
    exact (congrArg Subtype.val
      (φ.equivFieldRange.apply_symm_apply (IntermediateField.inclusion hE a))).symm
  exact Algebra.isSeparable_tower_top_of_isSeparable E F L

end Separable

/-! ### Theorem 2.1.10(iii) -/

section Main

variable {k L : Type*} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]
  [IsAlgClosed k] [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra k L]

omit [CompleteSpace k] [IsAlgClosed k] [CompleteSpace L] in
/-- An element with transcendental residue does not lie in `k`. -/
theorem notMem_range_of_transcendental_residue {x : L} (hx : ‖x‖ ≤ 1)
    (htr : Transcendental (ResidueField (unitBall k))
      (residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩)) :
    x ∉ Set.range (algebraMap k L) := by
  rintro ⟨c, rfl⟩
  have hc1 : ‖c‖ ≤ 1 := by rwa [norm_algebraMap'] at hx
  have h : residue (unitBall L) ⟨algebraMap k L c, mem_unitBall.mpr hx⟩ =
      algebraMap (ResidueField (unitBall k)) (ResidueField (unitBall L))
        (residue (unitBall k) ⟨c, mem_unitBall.mpr hc1⟩) := by
    rw [algebraMap_residue]
    rfl
  rw [h] at htr
  exact htr (isAlgebraic_algebraMap _)

set_option linter.style.haveILetI false in
/-- **Temkin, Theorem 2.1.10(iii)** (lines 2084–2085, proof lines 4151–4153; blueprint
`thm:sm-an-uniformization-light`(3)): let `L` be a one-dimensional analytic `k`-field and
`x ∈ L°` with residue `x̃` transcendental over `k̃` such that `L̃/k̃(x̃)` is separable. Then
`x ∉ k`, `x` is a Gauss generator of `\overline{k(x)}`, and `L` is finite and unramified over
`\overline{k(x)}`. -/
theorem isUnramified_closureAdjoin_of_transcendental (p : ℕ) [ExpChar k p]
    [ExpChar (ResidueField (unitBall k)) p] (hL : IsOneDimensional k L) {x : L} (hx : ‖x‖ ≤ 1)
    (htr : Transcendental (ResidueField (unitBall k))
      (residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩))
    (hsep : Algebra.IsSeparable
      (ResidueField (unitBall k))⟮residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩⟯
      (ResidueField (unitBall L))) :
    x ∉ Set.range (algebraMap k L) ∧
      IsGaussGenerator k (⟨x, mem_closureAdjoin_self x⟩ : closureAdjoin k x) ∧
        IsUnramified (closureAdjoin k x) L := by
  have hG : IsGaussElement k x := isGaussElement_of_transcendental_residue hx htr
  have hxk := notMem_range_of_transcendental_residue hx htr
  haveI := finiteDimensional_closureAdjoin hL hxk
  have hGK := isGaussGenerator_closureAdjoin hG
  set K := closureAdjoin k x with hK
  have hE : (ResidueField (unitBall k))⟮residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩⟯ ≤
      (IsScalarTower.toAlgHom (ResidueField (unitBall k)) (ResidueField (unitBall K))
        (ResidueField (unitBall L))).fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr
      ⟨residue (unitBall K) ⟨⟨x, mem_closureAdjoin_self x⟩, mem_unitBall.mpr hx⟩, rfl⟩
  haveI : Algebra.IsSeparable (ResidueField (unitBall K)) (ResidueField (unitBall L)) :=
    isSeparable_of_le_fieldRange hE
  exact ⟨hxk, hGK, IsGaussGenerator.isUnramified (K := K) (L := L) p hGK⟩

/-! ### Theorem 6.3.1(i) -/

set_option linter.style.haveILetI false in
/-- **Temkin, Theorem 6.3.1(i)** (lines 3987–3993, proof lines 4051–4065 and 4089–4112;
blueprint `thm:sm-an-unramified-generator`):
every one-dimensional analytic `k`-field `L` (with `k` algebraically closed of equal
characteristic) has an **unramified generator**: an element `x ∉ k` such that `L` is finite and
unramified over `\overline{k(x)}`. Moreover `x` is a type 4 generator of `L`, or an annulus
generator of `L`, or a Gauss generator of `\overline{k(x)}`. -/
theorem IsOneDimensional.exists_isUnramified (p : ℕ) [hk : ExpChar k p]
    [ExpChar (ResidueField (unitBall k)) p] (hL : IsOneDimensional k L) :
    ∃ x : L, x ∉ Set.range (algebraMap k L) ∧ IsUnramified (closureAdjoin k x) L ∧
      (IsTypeFourGenerator k x ∨ IsAnnulusGenerator k x ∨
        IsGaussGenerator k (⟨x, mem_closureAdjoin_self x⟩ : closureAdjoin k x)) := by
  obtain ⟨y, hy, hfin⟩ := id hL
  set K₀ := closureAdjoin k y with hK₀
  set y₀ : K₀ := ⟨y, mem_closureAdjoin_self y⟩ with hy₀_def
  have hy₀ : y₀ ∉ Set.range (algebraMap k K₀) := by
    rintro ⟨c, hc⟩
    exact hy ⟨c, congrArg Subtype.val hc⟩
  have hd : Dense (k⟮y₀⟯ : Set K₀) := dense_adjoin_closureAdjoin y
  rcases isTypeFourGenerator_or_isAnnulusGenerator_or_isGaussGenerator hy₀ hd with
    h4 | ⟨a, h3⟩ | ⟨a, t, ht, h2⟩
  · -- type 4
    obtain ⟨x, hx⟩ := IsTypeFourGenerator.exists_isTypeFourGenerator (K := K₀) (L := L) p h4
    refine ⟨x, notMem_range_of_radius_pos hx.radius_pos,
      isUnramified_of_forall_mem_range fun w ↦ ⟨⟨w, ?_⟩, rfl⟩, Or.inl hx⟩
    rw [mem_closureAdjoin_iff, hx.dense_adjoin.closure_eq]
    trivial
  · -- type 3
    have hK₀res : IsResidueTrivial k K₀ := fun w hw ↦ h3.exists_norm_sub_lt_one hw
    have hLres : IsResidueTrivial k L := hK₀res.of_finiteDimensional
    obtain ⟨z, hzn, hzv⟩ := IsAnnulusGenerator.exists_forall_norm_eq_zpow_mul (L := L) h3
    have hzk : z ∉ Set.range (algebraMap k L) := by
      rintro ⟨c, rfl⟩
      exact hzn c (norm_algebraMap' L c)
    have hz0 : z ≠ 0 := fun h0 ↦ hzk ⟨0, by rw [map_zero, h0]⟩
    haveI := finiteDimensional_closureAdjoin hL hzk
    set K := closureAdjoin k z with hK
    set z₀ : K := ⟨z, mem_closureAdjoin_self z⟩ with hz₀_def
    have hz₀L : algebraMap K L z₀ = z := rfl
    have hz₀ : IsAnnulusGenerator k z₀ := ⟨dense_adjoin_closureAdjoin z, fun c ↦ hzn c⟩
    have himm : IsImmediate K L := isImmediate_of_forall_exists_norm_sub_lt fun w hw ↦ by
      obtain ⟨j, c, hjc⟩ := hzv w hw
      set v : L := algebraMap k L c * z ^ j with hv
      have hvw : ‖v‖ = ‖w‖ := by
        rw [hv, norm_mul, norm_algebraMap', norm_zpow, hjc, mul_comm]
      have hv0 : v ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hvw
        exact hw (norm_eq_zero.mp hvw.symm)
      have hu : ‖w / v‖ ≤ 1 := by rw [norm_div, hvw, div_self (norm_ne_zero_iff.mpr hw)]
      obtain ⟨d, -, hd⟩ := hLres (w / v) hu
      refine ⟨algebraMap k K (d * c) * z₀ ^ j, ?_⟩
      have e1 : algebraMap K L (algebraMap k K (d * c) * z₀ ^ j) = algebraMap k L d * v := by
        rw [map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply, map_mul, hv, hz₀L]
        ring
      have e2 : w - algebraMap k L d * v = v * (w / v - algebraMap k L d) := by
        rw [mul_sub, mul_div_cancel₀ _ hv0]
        ring
      rw [e1, e2, norm_mul, hvw]
      exact mul_lt_of_lt_one_right (norm_pos_iff.mpr hw) hd
    have h1 := IsAnnulusGenerator.finrank_eq_one_of_isImmediate (K := K) (L := L) p hz₀ himm
    have hall : ∀ w : L, w ∈ Set.range (algebraMap K L) := by
      have hbt := (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).mpr h1
      intro w
      have hw : w ∈ (⊥ : IntermediateField K L) := hbt ▸ IntermediateField.mem_top
      exact IntermediateField.mem_bot.mp hw
    refine ⟨z, hzk, isUnramified_of_forall_mem_range hall, Or.inr (Or.inl ⟨?_, hzn⟩)⟩
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun w ↦ ?_)
    obtain ⟨w', rfl⟩ := hall w
    exact w'.2
  · -- type 2
    set u₀ : K₀ := algebraMap k K₀ t * (y₀ - algebraMap k K₀ a) with hu₀_def
    have hG : IsGaussElement k (u₀ : L) := h2.toIsGaussElement.map L
    have hu1 : ‖(u₀ : L)‖ ≤ 1 := hG.norm_le_one
    have htr := hG.transcendental_residue
    obtain _ | ⟨hprime⟩ := hk
    · -- characteristic zero: `x = u₀`
      have hxk := notMem_range_of_transcendental_residue hu1 htr
      haveI := finiteDimensional_closureAdjoin hL hxk
      have hGK := isGaussGenerator_closureAdjoin hG
      have : CharZero (ResidueField (unitBall k)) := charZero_of_expChar_one' _
      have : CharZero (ResidueField (unitBall (closureAdjoin k (u₀ : L)))) :=
        charZero_of_injective_algebraMap (algebraMap (ResidueField (unitBall k)) _).injective
      haveI : Algebra.IsSeparable (ResidueField (unitBall (closureAdjoin k (u₀ : L))))
          (ResidueField (unitBall L)) := Algebra.IsAlgebraic.isSeparable_of_perfectField
      exact ⟨u₀, hxk, IsGaussGenerator.isUnramified (K := closureAdjoin k (u₀ : L)) (L := L) 1
        hGK, Or.inr (Or.inr hGK)⟩
    · -- characteristic `p`: a separating transcendental residue
      have : Fact p.Prime := ⟨hprime⟩
      obtain ⟨k₀, hk₀, -⟩ := exists_isCoefficientField (F := k) p
      have htop := h2.adjoin_residue_eq_top hk₀
      set ũ₀ := residue (unitBall K₀) ⟨u₀, mem_unitBall.mpr h2.norm_le_one⟩ with hũ₀
      set f := IsScalarTower.toAlgHom (ResidueField (unitBall k)) (ResidueField (unitBall K₀))
        (ResidueField (unitBall L)) with hf
      have hadj : (ResidueField (unitBall k))⟮residue (unitBall L)
          ⟨(u₀ : L), mem_unitBall.mpr hu1⟩⟯ = f.fieldRange := by
        rw [AlgHom.fieldRange_eq_map, ← htop, IntermediateField.adjoin_map, Set.image_singleton]
        rfl
      have hfinf := (finrank_fieldRange_eq (k := ResidueField (unitBall k))
        (E := ResidueField (unitBall K₀)) (F := ResidueField (unitBall L))).1
      haveI : FiniteDimensional (ResidueField (unitBall k))⟮residue (unitBall L)
          ⟨(u₀ : L), mem_unitBall.mpr hu1⟩⟯ (ResidueField (unitBall L)) := by
        rw [hadj]
        exact hfinf
      have hff : IsFunctionFieldOneVar (ResidueField (unitBall k)) (ResidueField (unitBall L)) :=
        IsFunctionFieldOneVar.of_finiteDimensional_adjoin htr
      have := isAlgClosed_residueField_unitBall k
      obtain ⟨τ, hτ, -, hτsep⟩ := hff.exists_isSeparable
      obtain ⟨⟨x, hx⟩, rfl⟩ := residue_surjective τ
      obtain ⟨hxk, hGK, hU⟩ :=
        isUnramified_closureAdjoin_of_transcendental p hL (mem_unitBall.mp hx) hτ hτsep
      exact ⟨x, hxk, hU, Or.inr (Or.inr hGK)⟩

/-! ### Theorem 2.1.10 -/

/-- **Temkin, Theorem 2.1.10** (lines 2075–2086, proof lines 4144–4153; blueprint
`thm:sm-an-uniformization-light`):
let `k` be an algebraically closed complete non-archimedean field (equal characteristic) and `L`
an analytic `k`-field which is finite over `\overline{k(y)}` for some `y ∈ L`. Then

1. `L` is finite and unramified over `\overline{k(x)}` for some `x ∈ L`;
2. there are `x ∈ L` and `ε > 0` such that `L` is finite and unramified over `\overline{k(x')}`
   for every `x' ∈ L` with `‖x - x'‖ < ε`;
3. if `x ∈ L°` has residue `x̃` transcendental over `k̃` and `L̃/k̃(x̃)` is separable, then `L` is
   finite and unramified over `\overline{k(x)}`. -/
theorem uniformization_analytic (p : ℕ) [ExpChar k p] [ExpChar (ResidueField (unitBall k)) p]
    (y : L) [FiniteDimensional (closureAdjoin k y) L] :
    (∃ x : L, IsUnramified (closureAdjoin k x) L) ∧
      (∃ x : L, ∃ ε > 0, ∀ x' : L, ‖x - x'‖ < ε → IsUnramified (closureAdjoin k x') L) ∧
      ∀ (x : L) (hx : ‖x‖ ≤ 1),
        Transcendental (ResidueField (unitBall k))
            (residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩) →
          Algebra.IsSeparable
              (ResidueField (unitBall k))⟮residue (unitBall L) ⟨x, mem_unitBall.mpr hx⟩⟯
              (ResidueField (unitBall L)) →
            IsUnramified (closureAdjoin k x) L := by
  by_cases hy : y ∈ Set.range (algebraMap k L)
  · -- `y ∈ k`: then `L = k`
    obtain ⟨c, rfl⟩ := hy
    have hcl : IsClosed (Set.range (algebraMap k L)) :=
      (algebraMap_isometry k L).isUniformInducing.isComplete_range.isClosed
    have hsurj : ∀ e : closureAdjoin k (algebraMap k L c),
        e ∈ Set.range (algebraMap k (closureAdjoin k (algebraMap k L c))) := by
      intro e
      have hbot : k⟮algebraMap k L c⟯ = ⊥ :=
        IntermediateField.adjoin_simple_eq_bot_iff.mpr (IntermediateField.algebraMap_mem _ _)
      have he : (e : L) ∈ closure (k⟮algebraMap k L c⟯ : Set L) := e.2
      rw [hbot, IntermediateField.coe_bot, hcl.closure_eq] at he
      obtain ⟨d, hd⟩ := he
      exact ⟨d, Subtype.ext hd⟩
    have hall : ∀ w : L, w ∈ Set.range (algebraMap k L) := fun w ↦ by
      obtain ⟨e, rfl⟩ := mem_range_algebraMap_of_surjective hsurj w
      obtain ⟨d, rfl⟩ := hsurj e
      exact ⟨d, rfl⟩
    have hU : ∀ x' : L, IsUnramified (closureAdjoin k x') L := fun x' ↦
      isUnramified_of_forall_mem_range fun w ↦ by
        obtain ⟨d, rfl⟩ := hall w
        exact ⟨⟨algebraMap k L d, IntermediateField.algebraMap_mem _ d⟩, rfl⟩
    refine ⟨⟨0, hU 0⟩, ⟨0, 1, one_pos, fun x' _ ↦ hU x'⟩, fun x hx htr _ ↦ ?_⟩
    exact absurd (hall x) (notMem_range_of_transcendental_residue hx htr)
  · have hL : IsOneDimensional k L := ⟨y, hy, inferInstance⟩
    obtain ⟨x, hxk, hU, -⟩ := hL.exists_isUnramified p
    have hr := radius_pos_of_notMem_range hxk
    refine ⟨⟨x, hU⟩, ⟨x, radius k x / 2, by positivity, fun x' hx' ↦ ?_⟩,
      fun x hx htr hsep ↦ (isUnramified_closureAdjoin_of_transcendental p hL hx htr hsep).2.2⟩
    exact IsUnramified.of_norm_sub_lt (ε := 1 / 2) (by norm_num) (by norm_num)
      (by linarith) hU

end Main

end DeJongAlterations.StableModification.Valuation.Analytic
