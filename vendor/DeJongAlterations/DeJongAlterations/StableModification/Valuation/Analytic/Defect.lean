/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.OrthogonalBasis
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Ramification index, residue degree and the fundamental inequality

Let `L/K` be a finite extension of non-archimedean normed fields (`NormedAlgebra K L`). Temkin,
*Stable modification of relative curves*, §2.1 (`semi-stable.tex`, lines 2000–2007), uses
`e_{L/K} = [|L^×| : |K^×|]`, `f_{L/K} = [L̃ : K̃]`, the defect `[L : K] / (e f)`, and calls `L/K`
*Cartesian* (defectless) if `e f = [L : K]`, "because this happens if and only if the `K`-vector
space `L` has an orthogonal basis". This file proves the parts of this used later.

## Main definitions

* `inertiaDegree K L = f_{L/K}`, `ramificationIndex K L = e_{L/K}`.
* `IsCartesian K L`: `e_{L/K} f_{L/K} = [L : K]`.

## Main results

* `exists_norm_sum_smul_eq`: if `y₁, …, y_m ∈ L°` have `K̃`-linearly independent residues, then
  `‖∑ aᵢ yᵢ‖ = maxᵢ ‖aᵢ‖`.
* `isROrthogonal_mul`: if moreover `z₁, …, z_e ∈ L^×` have norms in distinct classes modulo
  `|K^×|`, the family `(yᵢ z_k)` is orthogonal.
* `finrank_residueField_le`, `ramificationIndex_le_finrank`,
  `ramificationIndex_mul_inertiaDegree_le` (**fundamental inequality** `e f ≤ n`); in particular
  `L̃/K̃` is finite and `|L^×|/|K^×|` is finite.
* `isCartesian_iff_exists_basis_isROrthogonal`: `L/K` is Cartesian iff `L` has an orthogonal
  `K`-basis (`IsCartesian.exists_basis_isROrthogonal`, `isCartesian_of_isROrthogonal`). Hence
  (`IsCartesian.exists_forall_norm_sub_le`) in a Cartesian extension every `x ∈ L` has a best
  approximation in `K`.
* `ramificationIndex_mul`, `inertiaDegree_mul`, `isCartesian_tower_iff`: multiplicativity of `e`
  and `f`, and Cartesian extensions in towers.
-/

noncomputable section

open IsLocalRing Module
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-! ### Orthogonality of lifts of residue bases and of value representatives -/

section Orthogonal

theorem norm_eq_one_of_residue_ne_zero {x : unitBall L} (hx : residue (unitBall L) x ≠ 0) :
    ‖(x : L)‖ = 1 :=
  isUnit_unitBall_iff.mp ((residue_ne_zero_iff_isUnit x).mp hx)

/-- If `y₁, …, y_m ∈ L°` have `K̃`-linearly independent residues, then for all `aᵢ ∈ K` the norm
`‖∑ aᵢ yᵢ‖` is `‖a_{i₀}‖` for an index `i₀` maximizing `‖aᵢ‖`. -/
theorem exists_norm_sum_smul_eq {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → unitBall L)
    (hy : LinearIndependent (ResidueField (unitBall K)) (fun i ↦ residue (unitBall L) (y i)))
    (a : ι → K) : ∃ i₀, ‖∑ i, a i • (y i : L)‖ = ‖a i₀‖ ∧ ∀ i, ‖a i‖ ≤ ‖a i₀‖ := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖a i‖) Finset.univ_nonempty
  refine ⟨i₀, ?_, fun i ↦ hi₀ i (Finset.mem_univ i)⟩
  rcases eq_or_ne (a i₀) 0 with h0 | h0
  · have ha : ∀ i, a i = 0 := fun i ↦ by
      have := hi₀ i (Finset.mem_univ i)
      rw [h0, norm_zero] at this
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    simp [ha]
  have hb : ∀ i, a i / a i₀ ∈ unitBall K := fun i ↦ by
    rw [mem_unitBall, norm_div, div_le_one (norm_pos_iff.mpr h0)]
    exact hi₀ i (Finset.mem_univ i)
  set b : ι → unitBall K := fun i ↦ ⟨a i / a i₀, hb i⟩
  set S : unitBall L := ∑ i, algebraMap (unitBall K) (unitBall L) (b i) * y i with hS
  have hSL : (S : L) = ∑ i, (a i / a i₀) • (y i : L) := by
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coe_algebraMap_unitBall, Algebra.smul_def]
  have hsum : ∑ i, a i • (y i : L) = a i₀ • (S : L) := by
    rw [hSL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul, mul_div_cancel₀ _ h0]
  have hres : residue (unitBall L) S ≠ 0 := by
    intro hS0
    have hS0' : ∑ i, residue (unitBall K) (b i) • residue (unitBall L) (y i) = 0 := by
      rw [← hS0, hS, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, Algebra.smul_def, algebraMap_residue]
    have := Fintype.linearIndependent_iff.mp hy _ hS0' i₀
    have hb0 : b i₀ = 1 := Subtype.ext (by simp [b, div_self h0])
    rw [hb0, map_one] at this
    exact one_ne_zero this
  rw [hsum, norm_smul, norm_eq_one_of_residue_ne_zero hres, mul_one]

/-- Lifts of `K̃`-linearly independent residues are `K`-linearly independent. -/
theorem linearIndependent_of_residue {ι : Type*} [Fintype ι] (y : ι → unitBall L)
    (hy : LinearIndependent (ResidueField (unitBall K)) (fun i ↦ residue (unitBall L) (y i))) :
    LinearIndependent K (fun i ↦ (y i : L)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact linearIndependent_empty_type
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨i₀, h1, h2⟩ := exists_norm_sum_smul_eq y hy a
  rw [ha, norm_zero] at h1
  exact norm_eq_zero.mp (le_antisymm (h1 ▸ h2 i) (norm_nonneg _))

/-- Let `y₁, …, y_m ∈ L°` have `K̃`-linearly independent residues and let `z₁, …, z_e ∈ L^×` have
norms in pairwise distinct classes of `|L^×|/|K^×|`. Then the family `(yᵢ z_k)` is orthogonal over
`K`. -/
theorem isROrthogonal_mul {ι κ : Type*} [Fintype ι] [Fintype κ] (y : ι → unitBall L)
    (hy : LinearIndependent (ResidueField (unitBall K)) (fun i ↦ residue (unitBall L) (y i)))
    (z : κ → L) (hz : ∀ k k', k ≠ k' → ∀ c : K, ‖z k‖ ≠ ‖c‖ * ‖z k'‖) :
    IsROrthogonal K 1 (fun p : ι × κ ↦ (y p.1 : L) * z p.2) := by
  classical
  intro a p₀
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact (IsEmpty.false p₀.1).elim
  set s : κ → L := fun k ↦ ∑ i, a (i, k) • (y i : L) with hs
  set t : κ → L := fun k ↦ s k * z k with ht
  have hsum : ∑ p : ι × κ, a p • ((y p.1 : L) * z p.2) = ∑ k, t k := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [t, s, Finset.sum_mul, smul_mul_assoc]
  -- `‖s k‖` is the norm of an element of `K`, and dominates every `‖a (i, k)‖`
  have hsk : ∀ k, ∃ c : K, ‖s k‖ = ‖c‖ ∧ ∀ i, ‖a (i, k)‖ ≤ ‖s k‖ := fun k ↦ by
    obtain ⟨i₀, h1, h2⟩ := exists_norm_sum_smul_eq y hy (fun i ↦ a (i, k))
    exact ⟨a (i₀, k), h1, fun i ↦ h1 ▸ h2 i⟩
  choose c hc hcle using hsk
  -- the nonzero terms `t k` have pairwise distinct norms
  set T := Finset.univ.filter (fun k ↦ t k ≠ 0) with hT
  have hpair : Set.Pairwise (T : Set κ) (fun k k' ↦ ‖t k‖ ≠ ‖t k'‖) := by
    intro k hk k' hk' hne heq
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk hk'
    have hck : c k ≠ 0 := by
      intro h0
      apply hk
      have : ‖s k‖ = 0 := by rw [hc k, h0, norm_zero]
      simp [t, norm_eq_zero.mp this]
    have heq' : ‖c k‖ * ‖z k‖ = ‖c k'‖ * ‖z k'‖ := by
      simpa only [t, norm_mul, hc] using heq
    apply hz k k' hne (c k' / c k)
    rw [norm_div, div_mul_eq_mul_div, eq_div_iff (norm_ne_zero_iff.mpr hck), mul_comm, heq']
  have hle : ∀ k, ‖t k‖ ≤ ‖∑ k, t k‖ := by
    intro k
    by_cases hk : t k = 0
    · rw [hk, norm_zero]
      exact norm_nonneg _
    have hkT : k ∈ T := by simp [hT, hk]
    rw [← Finset.sum_filter_ne_zero, ← hT,
      IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨k, hkT⟩ hpair]
    exact Finset.le_sup' (fun k ↦ ‖t k‖) hkT
  rw [hsum, one_mul]
  refine le_trans ?_ (hle p₀.2)
  rw [norm_smul, norm_mul, ht]
  dsimp only
  rw [norm_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖a p₀‖ * ‖(y p₀.1 : L)‖ ≤ ‖a p₀‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_coe_unitBall_le_one _) (norm_nonneg _)
    _ = ‖a (p₀.1, p₀.2)‖ := by rw [mul_one]
    _ ≤ ‖s p₀.2‖ := hcle p₀.2 p₀.1

end Orthogonal

/-! ### Residue degree and ramification index -/

section Degrees

variable (K L)

/-- The residue degree `f_{L/K} = [L̃ : K̃]`. -/
def inertiaDegree : ℕ :=
  finrank (ResidueField (unitBall K)) (ResidueField (unitBall L))

/-- The ramification index `e_{L/K} = [|L^×| : |K^×|]`. -/
def ramificationIndex : ℕ :=
  (valueGroup K).relIndex (valueGroup L)

/-- A finite extension `L/K` is *Cartesian* (defectless) if `e_{L/K} f_{L/K} = [L : K]`
(Temkin, l. 2002–2007). -/
def IsCartesian : Prop :=
  ramificationIndex K L * inertiaDegree K L = finrank K L

variable {K L} [FiniteDimensional K L]

/-- The residue field extension of a finite extension is finite, of degree at most `[L : K]`. -/
theorem rank_residueField_le :
    Module.rank (ResidueField (unitBall K)) (ResidueField (unitBall L)) ≤ finrank K L := by
  classical
  refine rank_le fun s hs ↦ ?_
  choose y hy using fun x : ResidueField (unitBall L) ↦ residue_surjective x
  have hli : LinearIndependent (ResidueField (unitBall K))
      (fun i : s ↦ residue (unitBall L) (y i)) := by
    simpa [hy] using hs
  have := (linearIndependent_of_residue (fun i : s ↦ y i) hli).fintype_card_le_finrank
  simpa using this

instance finiteDimensional_residueField :
    FiniteDimensional (ResidueField (unitBall K)) (ResidueField (unitBall L)) :=
  Module.rank_lt_aleph0_iff.mp (rank_residueField_le.trans_lt Cardinal.natCast_lt_aleph0)

theorem inertiaDegree_le_finrank : inertiaDegree K L ≤ finrank K L :=
  finrank_le_of_rank_le rank_residueField_le

omit [FiniteDimensional K L] in
theorem inertiaDegree_def :
    inertiaDegree K L = finrank (ResidueField (unitBall K)) (ResidueField (unitBall L)) := rfl

variable (K L) in
/-- The quotient `|L^×| / |K^×|`. -/
abbrev ValueGroupQuotient :=
  valueGroup L ⧸ (valueGroup K).subgroupOf (valueGroup L)

variable (K L) in
/-- The class of `x ∈ L^×` in `|L^×| / |K^×|`. -/
def valueClass : Lˣ →* ValueGroupQuotient K L :=
  (QuotientGroup.mk' _).comp ((normUnits L).codRestrict (valueGroup L) norm_mem_valueGroup)

omit [NormedAlgebra K L] [FiniteDimensional K L] in
theorem valueClass_surjective : Function.Surjective (valueClass K L) := by
  refine (QuotientGroup.mk'_surjective _).comp fun γ ↦ ?_
  have hγ : (γ : ℝ≥0ˣ) ∈ (normUnits L).range := by
    rw [range_normUnits]
    exact γ.2
  obtain ⟨x, hx⟩ := hγ
  exact ⟨x, Subtype.ext hx⟩

omit [NormedAlgebra K L] [FiniteDimensional K L] in
theorem valueClass_eq_valueClass_iff {x y : Lˣ} :
    valueClass K L x = valueClass K L y ↔ ∃ c : K, ‖(y : L)‖ = ‖c‖ * ‖(x : L)‖ := by
  rw [valueClass, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf, ← map_inv, ← map_mul,
    MonoidHom.codRestrict_apply, mem_valueGroup_iff, coe_normUnits]
  have hx : ‖(x : L)‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr x.ne_zero
  have key : ∀ c : K, ‖c‖₊ = ‖((x⁻¹ * y : Lˣ) : L)‖₊ ↔ ‖(y : L)‖ = ‖c‖ * ‖(x : L)‖ := by
    intro c
    rw [Units.val_mul, nnnorm_mul, Units.val_inv_eq_inv_val, nnnorm_inv, eq_inv_mul_iff_mul_eq₀ hx,
      ← NNReal.coe_inj, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm, mul_comm, eq_comm]
  exact exists_congr key

omit [FiniteDimensional K L] in
omit [NormedAlgebra K L] [FiniteDimensional K L] in
/-- Representatives of distinct classes of `|L^×| / |K^×|` satisfy the hypothesis of
`isROrthogonal_mul`. -/
theorem norm_ne_of_valueClass_ne {x y : Lˣ} (h : valueClass K L x ≠ valueClass K L y) (c : K) :
    ‖(x : L)‖ ≠ ‖c‖ * ‖(y : L)‖ := by
  intro hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_mul] at hc
    exact x.ne_zero (norm_eq_zero.mp hc)
  apply h
  rw [valueClass_eq_valueClass_iff]
  refine ⟨c⁻¹, ?_⟩
  rw [hc, norm_inv, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc0)]

omit [FiniteDimensional K L] in
/-- The family `1 · z_q` over a finite set of classes is linearly independent. -/
theorem linearIndependent_reps {S : Type*} [Fintype S] (z : S → Lˣ)
    (hz : Function.Injective (fun q ↦ valueClass K L (z q))) :
    LinearIndependent K (fun p : Unit × S ↦ ((1 : unitBall L) : L) * (z p.2 : L)) := by
  refine (isROrthogonal_mul (K := K) (fun _ : Unit ↦ (1 : unitBall L)) ?_ (fun q ↦ (z q : L))
    (fun q q' hqq' c ↦ norm_ne_of_valueClass_ne (fun h ↦ hqq' (hz h)) c)).linearIndependent
    one_pos fun p ↦ ?_
  · rw [linearIndependent_unique_iff, map_one]
    exact one_ne_zero
  · simp [(z p.2).ne_zero]

/-- The group `|L^×| / |K^×|` is finite. -/
instance finite_valueGroupQuotient : Finite (ValueGroupQuotient K L) := by
  classical
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (ValueGroupQuotient K L) (finrank K L + 1)
  choose z hz using fun q : ValueGroupQuotient K L ↦ valueClass_surjective (K := K) q
  have hli := linearIndependent_reps (K := K) (fun q : S ↦ z q)
    (fun q q' h ↦ Subtype.ext (by simpa [hz] using h))
  have := hli.fintype_card_le_finrank
  simp [hS] at this

omit [NormedAlgebra K L] [FiniteDimensional K L] in
theorem ramificationIndex_eq_card : ramificationIndex K L = Nat.card (ValueGroupQuotient K L) :=
  Subgroup.index_eq_card _

/-- `e_{L/K} ≤ [L : K]`. -/
theorem ramificationIndex_le_finrank : ramificationIndex K L ≤ finrank K L := by
  classical
  have := Fintype.ofFinite (ValueGroupQuotient K L)
  choose z hz using fun q : ValueGroupQuotient K L ↦ valueClass_surjective (K := K) q
  have hli := linearIndependent_reps (K := K) z (fun q q' h ↦ by simpa [hz] using h)
  have := hli.fintype_card_le_finrank
  rw [ramificationIndex_eq_card, Nat.card_eq_fintype_card]
  simpa using this

theorem ramificationIndex_pos : 0 < ramificationIndex K L := by
  rw [ramificationIndex_eq_card]
  exact Nat.card_pos

/-- **The fundamental inequality** `e_{L/K} f_{L/K} ≤ [L : K]`. -/
theorem ramificationIndex_mul_inertiaDegree_le :
    ramificationIndex K L * inertiaDegree K L ≤ finrank K L := by
  classical
  have := Fintype.ofFinite (ValueGroupQuotient K L)
  choose z hz using fun q : ValueGroupQuotient K L ↦ valueClass_surjective (K := K) q
  set B := Module.finBasis (ResidueField (unitBall K)) (ResidueField (unitBall L))
  choose y hy using fun i ↦ residue_surjective (B i)
  have hyli : LinearIndependent (ResidueField (unitBall K))
      (fun i ↦ residue (unitBall L) (y i)) := by
    simpa [hy] using B.linearIndependent
  have hli := (isROrthogonal_mul (K := K) y hyli (fun q ↦ (z q : L))
    (fun q q' hqq' c ↦ norm_ne_of_valueClass_ne (by simpa [hz] using hqq') c)).linearIndependent
    one_pos fun p ↦ by
      simp only [norm_mul, ne_eq, mul_eq_zero, norm_eq_zero, (z p.2).ne_zero, or_false]
      intro h
      apply B.ne_zero p.1
      rw [← hy, show y p.1 = 0 from Subtype.ext h, map_zero]
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm] at this
  rw [ramificationIndex_eq_card, Nat.card_eq_fintype_card, inertiaDegree]
  exact this

/-- **Cartesian extensions have orthogonal bases.** If `e_{L/K} f_{L/K} = [L : K]`, then lifts of a
`K̃`-basis of `L̃` multiplied by representatives of `|L^×|/|K^×|` form an orthogonal `K`-basis
of `L`. -/
theorem IsCartesian.exists_basis_isROrthogonal (h : IsCartesian K L) :
    ∃ b : Basis (Fin (finrank K L)) K L, IsROrthogonal K 1 b := by
  classical
  have := Fintype.ofFinite (ValueGroupQuotient K L)
  choose z hz using fun q : ValueGroupQuotient K L ↦ valueClass_surjective (K := K) q
  set B := Module.finBasis (ResidueField (unitBall K)) (ResidueField (unitBall L))
  choose y hy using fun i ↦ residue_surjective (B i)
  have hyli : LinearIndependent (ResidueField (unitBall K))
      (fun i ↦ residue (unitBall L) (y i)) := by
    simpa [hy] using B.linearIndependent
  have ho := isROrthogonal_mul (K := K) y hyli (fun q ↦ (z q : L))
    (fun q q' hqq' c ↦ norm_ne_of_valueClass_ne (by simpa [hz] using hqq') c)
  have hli := ho.linearIndependent one_pos fun p ↦ by
    simp only [norm_mul, ne_eq, mul_eq_zero, norm_eq_zero, (z p.2).ne_zero, or_false]
    intro h0
    apply B.ne_zero p.1
    rw [← hy, show y p.1 = 0 from Subtype.ext h0, map_zero]
  have hcard : Fintype.card (Fin (finrank (ResidueField (unitBall K)) (ResidueField (unitBall L))) ×
      ValueGroupQuotient K L) = finrank K L := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card,
      ← ramificationIndex_eq_card, mul_comm]
    exact h
  set b := basisOfLinearIndependentOfCardEqFinrank' _ hli hcard
  set e := Fintype.equivFinOfCardEq hcard
  refine ⟨b.reindex e, ?_⟩
  rw [Basis.coe_reindex, coe_basisOfLinearIndependentOfCardEqFinrank']
  exact ho.comp_equiv e.symm

/-- In a Cartesian extension every element has a best approximation in the base:
`inf_{c ∈ K} ‖x - c‖` is attained. -/
theorem IsCartesian.exists_forall_norm_sub_le (h : IsCartesian K L) (x : L) :
    ∃ c : K, ∀ c' : K, ‖x - algebraMap K L c‖ ≤ ‖x - algebraMap K L c'‖ := by
  obtain ⟨b, hb⟩ := h.exists_basis_isROrthogonal
  obtain ⟨c, hc⟩ := hb.exists_forall_norm_sub_smul_le b x 1
  exact ⟨c, fun c' ↦ by simpa [Algebra.algebraMap_eq_smul_one] using hc c'⟩

omit [IsUltrametricDist K] [IsUltrametricDist L] [FiniteDimensional K L] in
theorem norm_rescale_eq_one {v z : L} {c : K} (hc : c ≠ 0) (hz : z ≠ 0)
    (hvc : ‖v‖ = ‖c‖ * ‖z‖) : ‖(algebraMap K L c)⁻¹ * z⁻¹ * v‖ = 1 := by
  rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_algebraMap', hvc]
  have : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

omit [FiniteDimensional K L] in
/-- Elements of an orthogonal family whose norms lie in one class of `|L^×|/|K^×|`, rescaled to
norm one, have `K̃`-linearly independent residues. -/
theorem linearIndependent_residue_of_isROrthogonal {S : Type*} [Fintype S] (v : S → L)
    (hv : IsROrthogonal K 1 v) (z : L) (hz : z ≠ 0) (c : S → K) (hc : ∀ s, c s ≠ 0)
    (hvc : ∀ s, ‖v s‖ = ‖c s‖ * ‖z‖) :
    LinearIndependent (ResidueField (unitBall K)) (fun s ↦ residue (unitBall L)
      ⟨(algebraMap K L (c s))⁻¹ * z⁻¹ * v s,
        mem_unitBall.mpr (norm_rescale_eq_one (hc s) hz (hvc s)).le⟩) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg s₀
  choose a ha using fun s ↦ residue_surjective (g s)
  set u : S → unitBall L := fun s ↦ ⟨(algebraMap K L (c s))⁻¹ * z⁻¹ * v s,
    mem_unitBall.mpr (norm_rescale_eq_one (hc s) hz (hvc s)).le⟩ with hu
  set T : unitBall L := ∑ s, algebraMap (unitBall K) (unitBall L) (a s) * u s with hT
  have hTres : residue (unitBall L) T = 0 := by
    rw [hT, map_sum, ← hg]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, Algebra.smul_def, ← ha, algebraMap_residue]
  have hTlt : ‖(T : L)‖ < 1 := residue_eq_zero_iff_norm_lt_one.mp hTres
  -- `T = z⁻¹ ∑ (a s / c s) v s`
  have hTL : (T : L) = z⁻¹ * ∑ s, ((a s : K) / c s) • v s := by
    rw [hT]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [coe_algebraMap_unitBall, Algebra.smul_def, div_eq_mul_inv, map_mul, map_inv₀]
    simp only [hu]
    ring
  have hle := hv (fun s ↦ (a s : K) / c s) s₀
  rw [one_mul, norm_smul, norm_div, hvc s₀] at hle
  have hc0 : 0 < ‖c s₀‖ := norm_pos_iff.mpr (hc s₀)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsum : ‖∑ s, ((a s : K) / c s) • v s‖ = ‖z‖ * ‖(T : L)‖ := by
    rw [hTL, norm_mul, norm_inv, ← mul_assoc, mul_inv_cancel₀ hz0.ne', one_mul]
  rw [hsum] at hle
  have ha1 : ‖(a s₀ : K)‖ < 1 := by
    have : ‖(a s₀ : K)‖ * ‖z‖ < 1 * ‖z‖ := by
      calc ‖(a s₀ : K)‖ * ‖z‖ = ‖(a s₀ : K)‖ / ‖c s₀‖ * (‖c s₀‖ * ‖z‖) := by
            field_simp
        _ ≤ ‖z‖ * ‖(T : L)‖ := hle
        _ < ‖z‖ * 1 := mul_lt_mul_of_pos_left hTlt hz0
        _ = 1 * ‖z‖ := by ring
    exact lt_of_mul_lt_mul_right this hz0.le
  rw [← ha s₀]
  exact residue_eq_zero_iff_norm_lt_one.mpr ha1

/-- **An extension with an orthogonal basis is Cartesian** (Temkin, l. 2004–2007): if `L` has an
orthogonal `K`-basis then `e_{L/K} f_{L/K} = [L : K]`. -/
theorem isCartesian_of_isROrthogonal {ι : Type*} [Fintype ι] (b : Basis ι K L)
    (hb : IsROrthogonal K 1 b) : IsCartesian K L := by
  classical
  have := Fintype.ofFinite (ValueGroupQuotient K L)
  refine le_antisymm ramificationIndex_mul_inertiaDegree_le ?_
  set w : ι → Lˣ := fun i ↦ Units.mk0 (b i) (b.ne_zero i)
  set cls : ι → ValueGroupQuotient K L := fun i ↦ valueClass K L (w i)
  -- each class contains at most `f` basis vectors
  have hfiber : ∀ q, Fintype.card {i // cls i = q} ≤ inertiaDegree K L := by
    intro q
    rcases isEmpty_or_nonempty {i // cls i = q} with hS | ⟨⟨i₀, hi₀⟩⟩
    · simp
    have hcls : ∀ s : {i // cls i = q}, ∃ c : K, ‖b s‖ = ‖c‖ * ‖b i₀‖ := fun s ↦ by
      have : valueClass K L (w i₀) = valueClass K L (w s) := by
        change cls i₀ = cls s
        rw [hi₀, s.2]
      exact (valueClass_eq_valueClass_iff.mp this)
    choose c hc using hcls
    have hc0 : ∀ s, c s ≠ 0 := fun s h0 ↦ by
      have := hc s
      rw [h0, norm_zero, zero_mul] at this
      exact b.ne_zero s (norm_eq_zero.mp this)
    have hli := linearIndependent_residue_of_isROrthogonal (K := K)
      (b ∘ (Subtype.val : {i // cls i = q} → ι))
      (hb.comp_injective Subtype.val_injective) (b i₀) (b.ne_zero i₀) c hc0 hc
    exact hli.fintype_card_le_finrank
  calc finrank K L = Fintype.card ι := (finrank_eq_card_basis b)
    _ = ∑ q, Fintype.card {i // cls i = q} := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv cls).symm
    _ ≤ ∑ _q : ValueGroupQuotient K L, inertiaDegree K L := Finset.sum_le_sum fun q _ ↦ hfiber q
    _ = ramificationIndex K L * inertiaDegree K L := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ramificationIndex_eq_card,
          Nat.card_eq_fintype_card]

/-- **Cartesian ⇔ orthogonal basis** (Temkin, l. 2004–2007). -/
theorem isCartesian_iff_exists_basis_isROrthogonal :
    IsCartesian K L ↔ ∃ b : Basis (Fin (finrank K L)) K L, IsROrthogonal K 1 b :=
  ⟨IsCartesian.exists_basis_isROrthogonal, fun ⟨b, hb⟩ ↦ isCartesian_of_isROrthogonal b hb⟩

end Degrees

/-! ### Towers -/

section Tower

variable {M : Type*} [NormedField M] [IsUltrametricDist M] [NormedAlgebra K M] [NormedAlgebra L M]
  [IsScalarTower K L M]

/-- The residue fields of a tower of normed fields form a tower. -/
instance isScalarTower_residueField :
    IsScalarTower (ResidueField (unitBall K)) (ResidueField (unitBall L))
      (ResidueField (unitBall M)) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [algebraMap_residue, algebraMap_residue, algebraMap_residue]
  congr 1
  ext
  simp [IsScalarTower.algebraMap_apply K L M]

variable (K L M)

omit [NormedAlgebra K M] [IsScalarTower K L M] in
/-- Multiplicativity of the ramification index in towers. -/
theorem ramificationIndex_mul_ramificationIndex :
    ramificationIndex K L * ramificationIndex L M = ramificationIndex K M :=
  Subgroup.relIndex_mul_relIndex _ _ _ valueGroup_le_valueGroup valueGroup_le_valueGroup

/-- Multiplicativity of the residue degree in towers. -/
theorem inertiaDegree_mul_inertiaDegree [FiniteDimensional K L] [FiniteDimensional L M] :
    inertiaDegree K L * inertiaDegree L M = inertiaDegree K M :=
  Module.finrank_mul_finrank _ _ _

/-- A tower `M/L/K` is Cartesian iff both steps are. -/
theorem isCartesian_iff_of_tower [FiniteDimensional K L] [FiniteDimensional L M] :
    IsCartesian K M ↔ IsCartesian K L ∧ IsCartesian L M := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  have h1 := ramificationIndex_mul_inertiaDegree_le (K := K) (L := L)
  have h2 := ramificationIndex_mul_inertiaDegree_le (K := L) (L := M)
  have hn1 : 0 < finrank K L := Module.finrank_pos
  have hn2 : 0 < finrank L M := Module.finrank_pos
  have hKM : ramificationIndex K M * inertiaDegree K M =
      (ramificationIndex K L * inertiaDegree K L) * (ramificationIndex L M * inertiaDegree L M) := by
    rw [← ramificationIndex_mul_ramificationIndex K L M, ← inertiaDegree_mul_inertiaDegree K L M]
    ring
  rw [IsCartesian, IsCartesian, IsCartesian, hKM, ← Module.finrank_mul_finrank K L M]
  constructor
  · intro h
    by_contra hne
    rw [not_and_or] at hne
    rcases hne with hne | hne
    · have hlt := lt_of_le_of_ne h1 hne
      have : (ramificationIndex K L * inertiaDegree K L) *
          (ramificationIndex L M * inertiaDegree L M) < finrank K L * finrank L M :=
        calc _ ≤ (ramificationIndex K L * inertiaDegree K L) * finrank L M :=
              Nat.mul_le_mul_left _ h2
          _ < finrank K L * finrank L M := Nat.mul_lt_mul_of_pos_right hlt hn2
      omega
    · have hlt := lt_of_le_of_ne h2 hne
      have : (ramificationIndex K L * inertiaDegree K L) *
          (ramificationIndex L M * inertiaDegree L M) < finrank K L * finrank L M :=
        calc _ ≤ finrank K L * (ramificationIndex L M * inertiaDegree L M) :=
              Nat.mul_le_mul_right _ h1
          _ < finrank K L * finrank L M := Nat.mul_lt_mul_of_pos_left hlt hn1
      omega
  · rintro ⟨ha, hb⟩
    rw [ha, hb]

end Tower


end DeJongAlterations.StableModification.Valuation.Analytic
