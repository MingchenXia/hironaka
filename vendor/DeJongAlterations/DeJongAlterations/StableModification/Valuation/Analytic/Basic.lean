/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Analytic fields: the bridge between norms and valuations

This file fixes the encoding of the *analytic fields* of Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), §2.1 (`semi-stable.tex`, lines 1891–1896): an analytic field
is a complete field with a non-trivial valuation `|·| : k → ℝ≥0`. In Lean an analytic field is a
type `K` with

`[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`,

and an extension of analytic fields is a `NormedAlgebra K L` (orchestrator decision OD6). The file
proves, once and for all, the dictionary between this normed encoding and Mathlib's valuation
theory (`Valuation`, `ValuationSubring`, `Valued`), in both directions.

## Main definitions

* `unitBall K`: the closed unit ball `K° = {x : ‖x‖ ≤ 1}` of a non-archimedean normed field, as the
  valuation subring of the valuation `NormedField.valuation : x ↦ ‖x‖₊`. Its maximal ideal is the
  open unit ball `K°° = {x : ‖x‖ < 1}`, its units are the elements of norm one, and its residue
  field `IsLocalRing.ResidueField (unitBall K)` is the residue field `K̃` of Temkin.
* `valueGroup K`: the value group `|K^×| ⊆ ℝ_{>0}`, a subgroup of `ℝ≥0ˣ`; the map
  `normUnits K : Kˣ →* ℝ≥0ˣ` identifies `Kˣ ⧸ (unitBall K)ˣ` with it
  (`quotientUnitGroupEquivValueGroup`).
* For a normed algebra `L` over `K` the instance `hasExtension` says that the valuation of `L`
  extends that of `K`; through Mathlib's `Valuation.HasExtension` API this provides the local
  homomorphism `unitBall K → unitBall L` and the residue field extension `K̃ → L̃`.
* For a rank-one valuation `v` on a field `F`, `WithVal v` is a nontrivially normed
  non-archimedean field (instance `WithVal.instNontriviallyNormedField`) whose unit ball is the
  valuation ring of `v` (`comap_unitBall_withVal`); its completion `v.Completion` is an analytic
  field. `toCompletion v : F →+* v.Completion` is the dense embedding.

## Main results

* `valueGroup_eq_of_denseRange`, `residueFieldEquivOfDenseRange`: a dense subfield `K` of a
  non-archimedean normed field `L` has the same value group and the same residue field.
* `isUltrametricDist_completion`, `nontriviallyNormedField_completion`: the completion of a
  (nontrivially normed) non-archimedean normed field is again one, hence an analytic field.
* `valueGroup_completion`, `residueFieldCompletionEquiv`, `comap_unitBall_completion`: completion
  preserves the value group, the residue field and the unit ball (Temkin uses this silently, e.g.
  lines 2104–2140).
* `comap_toCompletion_unitBall`: for a rank-one valuation `v` on `F`, the unit ball of the
  completion meets `F` in the valuation ring of `v`, and `valuationResidueFieldCompletionEquiv`
  identifies the residue field of `v` with that of the completion.

## Implementation notes

`unitBall K` is an abbreviation for `(NormedField.valuation (K := K)).valuationSubring`, so that
the instances of Mathlib's `Valuation.HasExtension` API (algebra structures on valuation subrings
and residue fields, locality, `Ideal.LiesOver`) apply to unit balls without unfolding. The normed
field structure on `WithVal v` is Mathlib's `Valued.toNontriviallyNormedField`, whose uniform
structure is the valuation uniformity by construction; we make it a global instance on `WithVal`.
Mathlib's `NumberField` completions (`NumberField/Completion/FinitePlace.lean`) put another,
propositionally equal, normed field structure on `adicCompletion K v`; a file importing both must
not rely on the two norms being definitionally equal.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### The unit ball of a non-archimedean normed field -/

section UnitBall

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- The closed unit ball `K° = {x | ‖x‖ ≤ 1}` of a non-archimedean normed field, as the valuation
subring of the valuation `x ↦ ‖x‖₊` (Temkin's `k°`). -/
abbrev unitBall : ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

variable {K}

@[simp]
theorem mem_unitBall {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe,
    coe_nnnorm, NNReal.coe_one]

theorem norm_coe_unitBall_le_one (x : unitBall K) : ‖(x : K)‖ ≤ 1 :=
  mem_unitBall.mp x.2

theorem mem_unitGroup_unitBall_iff {x : Kˣ} : x ∈ (unitBall K).unitGroup ↔ ‖(x : K)‖ = 1 := by
  rw [Valuation.mem_unitGroup_iff, NormedField.valuation_apply, ← NNReal.coe_inj, coe_nnnorm,
    NNReal.coe_one]

theorem mem_maximalIdeal_unitBall_iff {x : unitBall K} :
    x ∈ maximalIdeal (unitBall K) ↔ ‖(x : K)‖ < 1 := by
  rw [Valuation.mem_maximalIdeal_iff, NormedField.valuation_apply, ← NNReal.coe_lt_coe,
    coe_nnnorm, NNReal.coe_one]

theorem isUnit_unitBall_iff {x : unitBall K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_maximalIdeal, mem_maximalIdeal_unitBall_iff]
  exact ⟨fun h ↦ h.ne, fun h ↦ lt_of_le_of_ne (norm_coe_unitBall_le_one x) h⟩

theorem residue_eq_zero_iff_norm_lt_one {x : unitBall K} :
    residue (unitBall K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal_unitBall_iff]

theorem residue_eq_residue_iff {x y : unitBall K} :
    residue (unitBall K) x = residue (unitBall K) y ↔ ‖(x : K) - y‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_norm_lt_one]
  rfl

/-- The valuation of the unit ball compares elements like the norm. -/
theorem valuation_unitBall_le_iff {x y : K} :
    (unitBall K).valuation x ≤ (unitBall K).valuation y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← (Valuation.isEquiv_valuation_valuationSubring (NormedField.valuation (K := K))).le_iff_le,
    NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm,
    coe_nnnorm]

theorem valuation_unitBall_eq_iff {x y : K} :
    (unitBall K).valuation x = (unitBall K).valuation y ↔ ‖x‖ = ‖y‖ := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_unitBall_le_iff, valuation_unitBall_le_iff]

theorem valuation_unitBall_lt_iff {x y : K} :
    (unitBall K).valuation x < (unitBall K).valuation y ↔ ‖x‖ < ‖y‖ := by
  rw [lt_iff_not_ge, lt_iff_not_ge, valuation_unitBall_le_iff]

theorem mem_nonunits_unitBall_iff {x : K} : x ∈ (unitBall K).nonunits ↔ ‖x‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff, ← (unitBall K).valuation.map_one,
    valuation_unitBall_lt_iff, norm_one]

end UnitBall

theorem unitBall_ne_top (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] :
    unitBall K ≠ ⊤ := by
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
  intro h
  have : x ∈ unitBall K := h ▸ ValuationSubring.mem_top x
  exact (mem_unitBall.mp this).not_gt hx

/-! ### Ultrametric inequalities -/

section Ultra

variable {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]

theorem norm_sub_le_max (x y : E) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

/-- In a non-archimedean normed group, `‖x - y‖ < ‖x‖` forces `‖y‖ = ‖x‖`. -/
theorem norm_eq_of_norm_sub_lt {x y : E} (h : ‖x - y‖ < ‖x‖) : ‖y‖ = ‖x‖ := by
  have h1 : ‖y‖ ≤ max ‖x‖ ‖x - y‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le_max x (x - y)
  have h2 : ‖x‖ ≤ max ‖y‖ ‖x - y‖ := by
    simpa only [add_sub_cancel] using IsUltrametricDist.norm_add_le_max y (x - y)
  rw [max_eq_left h.le] at h1
  refine le_antisymm h1 ?_
  rcases le_total ‖y‖ ‖x - y‖ with h3 | h3
  · rw [max_eq_right h3] at h2
    exact absurd h2 (not_le.mpr h)
  · rwa [max_eq_left h3] at h2

end Ultra

/-! ### The value group -/

section ValueGroup

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- The value group `|K^×| ⊆ ℝ_{>0}` of a non-archimedean normed field, as a subgroup of `ℝ≥0ˣ`.
It is Mathlib's value group of the valuation `x ↦ ‖x‖₊`. -/
abbrev valueGroup : Subgroup ℝ≥0ˣ :=
  MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (NormedField.valuation (K := K)))

omit [IsUltrametricDist K] in
/-- The norm on units, `Kˣ → ℝ≥0ˣ`. -/
def normUnits : Kˣ →* ℝ≥0ˣ :=
  Units.map (nnnormHom : K →*₀ ℝ≥0).toMonoidHom

variable {K}

omit [IsUltrametricDist K] in
@[simp]
theorem coe_normUnits (x : Kˣ) : ((normUnits K x : ℝ≥0ˣ) : ℝ≥0) = ‖(x : K)‖₊ := rfl

theorem mem_valueGroup_iff {γ : ℝ≥0ˣ} : γ ∈ valueGroup K ↔ ∃ x : K, ‖x‖₊ = γ := by
  rw [← (MonoidWithZeroHom.valueGroup _).mem_toSubmonoid,
    ← MonoidWithZeroHom.valueMonoid_eq_valueGroup, MonoidWithZeroHom.mem_valueMonoid_iff]
  rfl

theorem norm_mem_valueGroup (x : Kˣ) : normUnits K x ∈ valueGroup K :=
  mem_valueGroup_iff.mpr ⟨x, rfl⟩

theorem range_normUnits : (normUnits K).range = valueGroup K := by
  ext γ
  rw [MonoidHom.mem_range, mem_valueGroup_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp only [nnnorm_zero] at hx
      exact γ.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩

theorem ker_normUnits : (normUnits K).ker = (unitBall K).unitGroup := by
  ext x
  rw [MonoidHom.mem_ker, mem_unitGroup_unitBall_iff, Units.ext_iff, coe_normUnits,
    Units.val_one, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]

/-- The value group `|K^×|` is the quotient `Kˣ ⧸ (K°)ˣ`; this identifies `valueGroup K` with the
value group of the valuation subring `unitBall K`. -/
def quotientUnitGroupEquivValueGroup : Kˣ ⧸ (unitBall K).unitGroup ≃* valueGroup K :=
  (QuotientGroup.quotientMulEquivOfEq ker_normUnits.symm).trans
    ((QuotientGroup.quotientKerEquivRange (normUnits K)).trans
      (MulEquiv.subgroupCongr range_normUnits))

@[simp]
theorem coe_quotientUnitGroupEquivValueGroup_mk (x : Kˣ) :
    ((quotientUnitGroupEquivValueGroup (QuotientGroup.mk x) : ℝ≥0ˣ) : ℝ≥0) = ‖(x : K)‖₊ := rfl

end ValueGroup

/-! ### Extensions of non-archimedean normed fields -/

section Extension

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

theorem valuation_comap_algebraMap :
    (NormedField.valuation (K := L)).comap (algebraMap K L) = NormedField.valuation := by
  ext x
  simp

/-- The valuation `x ↦ ‖x‖₊` of a normed algebra extends that of the base field. Through Mathlib's
`Valuation.HasExtension` API this provides the local homomorphism `unitBall K → unitBall L` and the
residue field extension. -/
instance hasExtension :
    (NormedField.valuation (K := K)).HasExtension (NormedField.valuation (K := L)) where
  val_isEquiv_comap := by
    rw [valuation_comap_algebraMap]
    exact Valuation.IsEquiv.refl

theorem comap_unitBall : (unitBall L).comap (algebraMap K L) = unitBall K := by
  ext x
  simp [ValuationSubring.mem_comap]

theorem algebraMap_mem_unitBall_iff {x : K} : algebraMap K L x ∈ unitBall L ↔ x ∈ unitBall K := by
  simp

@[simp]
theorem coe_algebraMap_unitBall (x : unitBall K) :
    ((algebraMap (unitBall K) (unitBall L) x : unitBall L) : L) = algebraMap K L x := rfl

theorem algebraMap_residue (x : unitBall K) :
    algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L)) (residue (unitBall K) x) =
      residue (unitBall L) (algebraMap (unitBall K) (unitBall L) x) := rfl

theorem valueGroup_le_valueGroup : valueGroup K ≤ valueGroup L := by
  intro γ hγ
  obtain ⟨x, hx⟩ := mem_valueGroup_iff.mp hγ
  exact mem_valueGroup_iff.mpr ⟨algebraMap K L x, by rw [← hx]; ext; simp⟩

end Extension

/-! ### Dense subfields: value group and residue field -/

section Dense

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

omit [IsUltrametricDist K] [IsUltrametricDist L] in
/-- A nonzero element of a normed field is approximated by an element of a dense subfield to
within less than its norm. -/
theorem exists_norm_sub_lt_norm (hd : DenseRange (algebraMap K L)) {x : L} (hx : x ≠ 0) :
    ∃ y : K, ‖x - algebraMap K L y‖ < ‖x‖ := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hd x ‖x‖ (norm_pos_iff.mpr hx)
  exact ⟨y, by rwa [dist_eq_norm] at hy⟩

omit [IsUltrametricDist K] in
/-- Every norm of an element of `L` is the norm of an element of a dense subfield. -/
theorem exists_norm_eq_of_denseRange (hd : DenseRange (algebraMap K L)) (x : L) :
    ∃ y : K, ‖y‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := exists_norm_sub_lt_norm hd hx
  exact ⟨y, by rw [← norm_algebraMap' L y]; exact norm_eq_of_norm_sub_lt hy⟩

/-- A dense subfield has the same value group. -/
theorem valueGroup_eq_of_denseRange (hd : DenseRange (algebraMap K L)) :
    valueGroup L = valueGroup K := by
  refine le_antisymm (fun γ hγ ↦ ?_) valueGroup_le_valueGroup
  obtain ⟨x, hx⟩ := mem_valueGroup_iff.mp hγ
  obtain ⟨y, hy⟩ := exists_norm_eq_of_denseRange hd x
  exact mem_valueGroup_iff.mpr ⟨y, by rw [← hx]; ext; simp [hy]⟩

/-- Every element of the unit ball of `L` is congruent modulo the open unit ball to an element of
the unit ball of a dense subfield. -/
theorem exists_unitBall_norm_sub_lt_one (hd : DenseRange (algebraMap K L)) (x : unitBall L) :
    ∃ y : unitBall K, ‖(x : L) - algebraMap K L y‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp hd x 1 one_pos
  rw [dist_eq_norm] at hy
  refine ⟨⟨y, ?_⟩, hy⟩
  rw [mem_unitBall, ← norm_algebraMap' L y]
  calc ‖algebraMap K L y‖ = ‖(x : L) - ((x : L) - algebraMap K L y)‖ := by rw [sub_sub_cancel]
    _ ≤ max ‖(x : L)‖ ‖(x : L) - algebraMap K L y‖ := norm_sub_le_max _ _
    _ ≤ 1 := max_le (norm_coe_unitBall_le_one x) hy.le

/-- The residue field extension of a dense subfield is bijective. -/
theorem bijective_algebraMap_residueField (hd : DenseRange (algebraMap K L)) :
    Function.Bijective
      (algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L))) := by
  refine ⟨(algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L))).injective, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨y, hy⟩ := exists_unitBall_norm_sub_lt_one hd x
  refine ⟨residue (unitBall K) y, ?_⟩
  rw [algebraMap_residue, residue_eq_residue_iff, coe_algebraMap_unitBall, norm_sub_rev]
  exact hy

/-- A dense subfield has the same residue field. -/
def residueFieldEquivOfDenseRange (hd : DenseRange (algebraMap K L)) :
    ResidueField (unitBall K) ≃+* ResidueField (unitBall L) :=
  RingEquiv.ofBijective _ (bijective_algebraMap_residueField hd)

@[simp]
theorem residueFieldEquivOfDenseRange_apply (hd : DenseRange (algebraMap K L))
    (x : ResidueField (unitBall K)) :
    residueFieldEquivOfDenseRange hd x =
      algebraMap (ResidueField (unitBall K)) (ResidueField (unitBall L)) x := rfl

end Dense

/-! ### The completion of a non-archimedean normed field -/

section Completion

open UniformSpace

variable (K : Type*) [NormedField K]

/-- The completion of a non-archimedean normed group is non-archimedean.
(Adapted from EnvelopeProperty, `Berkovich/ValuationCompletion.lean`.) -/
instance isUltrametricDist_completion {E : Type*} [SeminormedAddCommGroup E]
    [IsUltrametricDist E] : IsUltrametricDist (Completion E) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦ ?_
  induction a, b using Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    rw [← Completion.coe_add, Completion.norm_coe, Completion.norm_coe, Completion.norm_coe]
    exact IsUltrametricDist.norm_add_le_max a b

/-- The completion of a nontrivially normed field is nontrivially normed. -/
instance nontriviallyNormedField_completion (F : Type*) [NontriviallyNormedField F] :
    NontriviallyNormedField (Completion F) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := F)
    exact ⟨x, by rwa [Completion.norm_coe]⟩

theorem algebraMap_completion_apply (x : K) : algebraMap K (Completion K) x = x := rfl

theorem denseRange_algebraMap_completion : DenseRange (algebraMap K (Completion K)) :=
  Completion.denseRange_coe

variable [IsUltrametricDist K]

/-- Completion does not change the value group. -/
theorem valueGroup_completion : valueGroup (Completion K) = valueGroup K :=
  valueGroup_eq_of_denseRange (denseRange_algebraMap_completion K)

/-- The unit ball of the completion meets `K` in the unit ball of `K`. -/
theorem comap_unitBall_completion :
    (unitBall (Completion K)).comap (algebraMap K (Completion K)) = unitBall K :=
  comap_unitBall

/-- Completion does not change the residue field. -/
def residueFieldCompletionEquiv :
    ResidueField (unitBall K) ≃+* ResidueField (unitBall (Completion K)) :=
  residueFieldEquivOfDenseRange (denseRange_algebraMap_completion K)

end Completion

/-! ### From rank-one valuations to non-archimedean norms -/

section RankOne

open UniformSpace

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀) [hv : v.RankOne]

/-- The transported valuation on the type synonym `WithVal v` has rank one. -/
instance WithVal.rankOne : (Valued.v : Valuation (WithVal v) Γ₀).RankOne where
  hom' := (Valuation.RankOne.hom v).comp (WithVal.valueGroupOrderIso₀ v).toMonoidWithZeroHom
  strictMono' := (Valuation.RankOne.strictMono v).comp (WithVal.strictMono_valueGroupOrderIso₀ v)
  exists_val_nontrivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial v
    exact ⟨WithVal.toVal v x, hx⟩

/-- A field with a rank-one valuation `v` is a nontrivially normed field, with norm
`‖x‖ = hom (v x)` for the rank-one embedding `hom` of the value group into `ℝ≥0`; the uniform
structure is that of the valuation. -/
instance WithVal.instNontriviallyNormedField : NontriviallyNormedField (WithVal v) :=
  Valued.toNontriviallyNormedField (WithVal v) Γ₀

instance WithVal.isUltrametricDist : IsUltrametricDist (WithVal v) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (Valuation.norm_add_le (Valued.v : Valuation (WithVal v) Γ₀))

variable {v}

theorem WithVal.norm_le_norm_iff {x y : WithVal v} : ‖x‖ ≤ ‖y‖ ↔ v x.ofVal ≤ v y.ofVal :=
  Valued.toNormedField.norm_le_iff

theorem WithVal.norm_lt_norm_iff {x y : WithVal v} : ‖x‖ < ‖y‖ ↔ v x.ofVal < v y.ofVal :=
  Valued.toNormedField.norm_lt_iff

theorem WithVal.norm_le_one_iff {x : WithVal v} : ‖x‖ ≤ 1 ↔ v x.ofVal ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff

theorem WithVal.norm_lt_one_iff {x : WithVal v} : ‖x‖ < 1 ↔ v x.ofVal < 1 :=
  Valued.toNormedField.norm_lt_one_iff

variable (v)

/-- The unit ball of `WithVal v` is the valuation ring of `v`. -/
theorem comap_unitBall_withVal :
    (unitBall (WithVal v)).comap (WithVal.equiv v).symm.toRingHom = v.valuationSubring := by
  ext x
  rw [ValuationSubring.mem_comap, mem_unitBall, Valuation.mem_valuationSubring_iff]
  exact WithVal.norm_le_one_iff

/-- The dense embedding of a field into its completion for a rank-one valuation. -/
def toCompletion : F →+* v.Completion :=
  (Completion.coeRingHom : WithVal v →+* v.Completion).comp (WithVal.equiv v).symm.toRingHom

theorem toCompletion_apply (x : F) :
    toCompletion v x = ((WithVal.toVal v x : WithVal v) : v.Completion) := rfl

theorem denseRange_toCompletion : DenseRange (toCompletion v) :=
  Completion.denseRange_coe.comp (WithVal.equiv v).symm.surjective.denseRange
    (Completion.continuous_coe _)

theorem norm_toCompletion_le_iff {x y : F} :
    ‖toCompletion v x‖ ≤ ‖toCompletion v y‖ ↔ v x ≤ v y := by
  rw [toCompletion_apply, toCompletion_apply, Completion.norm_coe, Completion.norm_coe]
  exact WithVal.norm_le_norm_iff

theorem norm_toCompletion_le_one_iff {x : F} : ‖toCompletion v x‖ ≤ 1 ↔ v x ≤ 1 := by
  rw [toCompletion_apply, Completion.norm_coe]
  exact WithVal.norm_le_one_iff

theorem norm_toCompletion_lt_one_iff {x : F} : ‖toCompletion v x‖ < 1 ↔ v x < 1 := by
  rw [toCompletion_apply, Completion.norm_coe]
  exact WithVal.norm_lt_one_iff

/-- The unit ball of the completion meets `F` in the valuation ring of `v`. -/
theorem comap_toCompletion_unitBall :
    (unitBall v.Completion).comap (toCompletion v) = v.valuationSubring := by
  ext x
  rw [ValuationSubring.mem_comap, mem_unitBall, Valuation.mem_valuationSubring_iff]
  exact norm_toCompletion_le_one_iff v

/-- The valuation ring of `v` is the unit ball of `WithVal v`. -/
def valuationSubringEquivUnitBall : v.valuationSubring ≃+* unitBall (WithVal v) where
  toFun x := ⟨WithVal.toVal v x, mem_unitBall.mpr (WithVal.norm_le_one_iff.mpr x.2)⟩
  invFun y := ⟨y.1.ofVal, WithVal.norm_le_one_iff.mp (mem_unitBall.mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The residue field of a rank-one valuation is the residue field of the completion. -/
def valuationResidueFieldCompletionEquiv :
    ResidueField v.valuationSubring ≃+* ResidueField (unitBall v.Completion) :=
  (ResidueField.mapEquiv (valuationSubringEquivUnitBall v)).trans
    (residueFieldCompletionEquiv (WithVal v))

theorem valuationResidueFieldCompletionEquiv_residue (x : v.valuationSubring) :
    valuationResidueFieldCompletionEquiv v (residue _ x) =
      residue (unitBall v.Completion) ⟨toCompletion v x,
        mem_unitBall.mpr ((norm_toCompletion_le_one_iff v).mpr x.2)⟩ := rfl

end RankOne

end DeJongAlterations.StableModification.Valuation.Analytic
