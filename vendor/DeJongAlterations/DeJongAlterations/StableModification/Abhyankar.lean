import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Abhyankar's inequality and finite height of valuation rings

This file formalizes the elementary valuation theory of Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), §2.1 (`semi-stable.tex`, lines 1867–1960): Abhyankar's
inequality (Lemma 2.1.2 = `Abhlem`) and the finiteness of the height of a valued field of finite
transcendence degree (Corollary 2.1.3(i) = `approxcor`(i)), in the absolute form of the source and
in the relative form used for function fields over a ground field.

## Notation and main definitions

For a field `L` and a valuation subring `V` of `L`, the value group `|L^×| = Lˣ ⧸ Vˣ` is written
additively, `AddValueGroup V`; for a field `K` with `[Algebra K L]` the relative value group
`|L^×| / |K^×|` is `RelAddValueGroup K V = Lˣ ⧸ (Vˣ ⊔ Kˣ)`. The rational ranks
`ratRank V = dim_ℚ (|L^×| ⊗ ℚ)` and `relRatRank K V = E_{L/K} = dim_ℚ ((|L^×|/|K^×|) ⊗ ℚ)`
(Temkin's `E_{l/k}`) are defined as `ℤ`-ranks (`Module.rank ℤ`); `ratRank_eq_rank_rat` and
`relRatRank_eq_rank_rat` identify them with the `ℚ`-dimensions of the rationalizations.
Temkin's `F_{l/k} = trdeg (l̃/k̃)` is `Algebra.trdeg` of the residue fields; for an extension of
valued fields `vK.HasExtension vL` (Mathlib's notion) the residue field extension is the
Mathlib instance `Algebra (ResidueField vK.valuationSubring) (ResidueField vL.valuationSubring)`.

## Main results

* `algebraicIndependent_sumElim`: **orthogonality of monomials** (proof of `Abhlem`): elements
  `bᵢ ∈ Lˣ` whose classes in `|L^×|/|K^×|` are `ℤ`-linearly independent, together with elements
  `cⱼ` of the valuation ring whose residues are algebraically independent over the residue field
  of `K`, are algebraically independent over `K`.
* `relRatRank_add_trdeg_le`: **Abhyankar's inequality** `E_{L/K} + F_{L/K} ≤ trdeg (L/K)`.
* `ringKrullDim_le_ratRank`: the height (Krull dimension) of a valuation ring is at most the
  rational rank of its value group; `natCast_le_rank_of_convex_chain` and
  `krullDim_convexSubgroup_le` are the ordered-group version (chains of convex subgroups).
* `ringKrullDim_le_trdeg`, `ringKrullDim_le_of_trdeg_eq`: if `V` contains `K`, then
  `dim V ≤ trdeg (L/K)` (relative form of `approxcor`(i)).
* `ringKrullDim_le_trdeg_bot_add_one`, `ringKrullDim_le_of_trdeg_bot_eq`: the absolute form of
  `approxcor`(i): `dim V ≤ trdeg (L/P) + 1` with `P = ⊥` the prime subfield.

## Implementation notes

The value groups are quotients of the additive group `Additive Lˣ` by additive subgroups rather
than `Additive` of multiplicative quotients: with the latter the `ℤ`-module structure on
`Additive (Lˣ ⧸ H)` is not found by instance synthesis.
-/

noncomputable section

open IsLocalRing MvPolynomial
open scoped TensorProduct

namespace DeJongAlterations.StableModification

section Defs

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The image of `Kˣ` in `Lˣ` under the structure map. -/
def algebraMapUnits : Subgroup Lˣ :=
  (Units.map (algebraMap K L : K →* L)).range

variable {K L}

/-- The value group `|L^×| = Lˣ ⧸ Vˣ` of a valuation subring `V`, written additively. -/
abbrev AddValueGroup (V : ValuationSubring L) : Type _ :=
  Additive Lˣ ⧸ V.unitGroup.toAddSubgroup

variable (K) in
/-- The relative value group `|L^×| / |K^×|`, written additively. -/
abbrev RelAddValueGroup (V : ValuationSubring L) : Type _ :=
  Additive Lˣ ⧸ (V.unitGroup ⊔ algebraMapUnits K L).toAddSubgroup

/-- The rational rank `dim_ℚ (|L^×| ⊗ ℚ)` of the value group of `V`, defined as the `ℤ`-rank
of `AddValueGroup V`. -/
def ratRank (V : ValuationSubring L) : Cardinal :=
  Module.rank ℤ (AddValueGroup V)

variable (K) in
/-- The relative rational rank `E_{L/K} = dim_ℚ ((|L^×|/|K^×|) ⊗ ℚ)` (Temkin §2.1), defined as
the `ℤ`-rank of `RelAddValueGroup K V`. -/
def relRatRank (V : ValuationSubring L) : Cardinal :=
  Module.rank ℤ (RelAddValueGroup K V)

/-- The rational rank of the value group is the `ℚ`-dimension of its rationalization. -/
theorem ratRank_eq_rank_rat (V : ValuationSubring L) :
    ratRank V = Module.rank ℚ (ℚ ⊗[ℤ] AddValueGroup V) :=
  ((TensorProduct.isBaseChange ℤ (AddValueGroup V) ℚ).rank_eq).symm

/-- Temkin's `E_{L/K} = dim_ℚ ((|L^×|/|K^×|) ⊗ ℚ)` is the relative rational rank. -/
theorem relRatRank_eq_rank_rat (V : ValuationSubring L) :
    relRatRank K V = Module.rank ℚ (ℚ ⊗[ℤ] RelAddValueGroup K V) :=
  ((TensorProduct.isBaseChange ℤ (RelAddValueGroup K V) ℚ).rank_eq).symm

/-- Two units of `L` have the same class in `AddValueGroup V` if and only if they have the same
valuation: `AddValueGroup V` is the value group of `V`. -/
theorem mk_ofMul_eq_mk_ofMul_iff (V : ValuationSubring L) (x y : Lˣ) :
    (QuotientAddGroup.mk (Additive.ofMul x) : AddValueGroup V) =
        QuotientAddGroup.mk (Additive.ofMul y) ↔ V.valuation x = V.valuation y := by
  rw [QuotientAddGroup.eq, Additive.mem_toAddSubgroup, ValuationSubring.mem_unitGroup_iff]
  have hx : V.valuation (x : L) ≠ 0 := by simp
  simp [inv_mul_eq_one₀ hx]

end Defs

section Chain

/-- Let `H ≤ U₀ ≤ U₁ ≤ ⋯ ≤ Uₙ` be subgroups of a commutative group `G` such that each `Uₖ` is
saturated (`x ^ m ∈ Uₖ` with `m ≠ 0` implies `x ∈ Uₖ`). If `xᵢ ∈ U_{i+1} \ Uᵢ` for `i < n`,
then the classes of the `xᵢ` in `G ⧸ H` are `ℤ`-linearly independent. -/
theorem linearIndependent_mk_of_chain {G : Type*} [CommGroup G] (H : Subgroup G) {n : ℕ}
    (U : Fin (n + 1) → Subgroup G) (hU : Monotone U) (hH : H ≤ U 0)
    (hsat : ∀ k (x : G) (m : ℤ), m ≠ 0 → x ^ m ∈ U k → x ∈ U k)
    (x : Fin n → G) (hx : ∀ i, x i ∈ U i.succ) (hx' : ∀ i, x i ∉ U i.castSucc) :
    LinearIndependent ℤ fun i ↦
      (QuotientAddGroup.mk (Additive.ofMul (x i)) : Additive G ⧸ H.toAddSubgroup) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter fun i ↦ g i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [S, hi]⟩
  set j := S.max' hS
  have hj : g j ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hgt : ∀ i, j < i → g i = 0 := fun i hi ↦ by
    by_contra h
    exact absurd (S.le_max' i (by simp [S, h])) (not_le.mpr hi)
  have hprod : ∏ i, x i ^ g i ∈ H := by
    have h1 : (QuotientAddGroup.mk (Additive.ofMul (∏ i, x i ^ g i)) :
        Additive G ⧸ H.toAddSubgroup) = 0 := by
      rw [← hg]
      simp [ofMul_prod, ofMul_zpow]
    simpa using (QuotientAddGroup.eq_zero_iff _).mp h1
  have hrest : ∏ i ∈ Finset.univ.erase j, x i ^ g i ∈ U j.castSucc := by
    refine Subgroup.prod_mem _ fun i hi ↦ ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Subgroup.zpow_mem _ (hU (Fin.succ_le_castSucc_iff.mpr h) (hx i)) _
    · simp [hgt i h]
  have hxj : x j ^ g j ∈ U j.castSucc := by
    have h3 := Finset.mul_prod_erase Finset.univ (fun i ↦ x i ^ g i) (Finset.mem_univ j)
    have h4 : x j ^ g j = (∏ i, x i ^ g i) * (∏ i ∈ Finset.univ.erase j, x i ^ g i)⁻¹ := by
      rw [← h3, mul_inv_cancel_right]
    rw [h4]
    exact mul_mem (hU (Fin.zero_le _) (hH hprod)) (inv_mem hrest)
  exact hx' j (hsat _ _ _ hj hxj)

/-- A subgroup `H` of a linearly ordered commutative group is convex if `1 ≤ y ≤ x` with
`x ∈ H` implies `y ∈ H`. -/
def IsConvexSubgroup {G : Type*} [CommGroup G] [LinearOrder G] (H : Subgroup G) : Prop :=
  ∀ ⦃x y : G⦄, x ∈ H → 1 ≤ y → y ≤ x → y ∈ H

/-- Convex subgroups of a linearly ordered commutative group are saturated. -/
theorem IsConvexSubgroup.mem_of_zpow_mem {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] {H : Subgroup G} (hH : IsConvexSubgroup H) {x : G} {m : ℤ}
    (hm : m ≠ 0) (h : x ^ m ∈ H) : x ∈ H := by
  have hn : x ^ m.natAbs ∈ H := by
    rcases Int.natAbs_eq m with hm' | hm'
    · rw [hm', zpow_natCast] at h
      exact h
    · rw [hm', zpow_neg, zpow_natCast] at h
      exact (inv_mem_iff).mp h
  have hn0 : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  rcases le_total 1 x with hx | hx
  · exact hH hn hx (le_self_pow hx hn0)
  · have hx' : 1 ≤ x⁻¹ := one_le_inv'.mpr hx
    have := hH (by rw [inv_pow]; exact inv_mem hn) hx' (le_self_pow hx' hn0)
    exact (inv_mem_iff).mp this

/-- **Height at most rational rank** for ordered groups: a strictly increasing chain
`H₀ < H₁ < ⋯ < Hₙ` of convex subgroups of a linearly ordered commutative group `G` has
length `n ≤ rank_ℤ G`. -/
theorem natCast_le_rank_of_convex_chain {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] {n : ℕ} (H : Fin (n + 1) → Subgroup G) (hH : StrictMono H)
    (hconv : ∀ k, IsConvexSubgroup (H k)) : (n : Cardinal) ≤ Module.rank ℤ (Additive G) := by
  choose x hx hx' using fun i : Fin n ↦
    SetLike.exists_of_lt (hH (Fin.castSucc_lt_succ : i.castSucc < i.succ))
  have hli := linearIndependent_mk_of_chain ⊥ H hH.monotone bot_le
    (fun k _ _ hm h ↦ (hconv k).mem_of_zpow_mem hm h) x hx hx'
  have hli' : LinearIndependent ℤ fun i ↦ Additive.ofMul (x i) :=
    LinearIndependent.of_comp
      (QuotientAddGroup.mk' (⊥ : Subgroup G).toAddSubgroup).toIntLinearMap hli
  have hcard := hli'.cardinal_lift_le_rank
  simpa using hcard

/-- The height of a linearly ordered commutative group `G` (the Krull dimension of its poset of
convex subgroups) is at most the rational rank of `G`. -/
theorem krullDim_convexSubgroup_le {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] :
    Order.krullDim {H : Subgroup G // IsConvexSubgroup H} ≤
      (Module.rank ℤ (Additive G)).toENat := by
  rw [Order.krullDim]
  refine iSup_le fun p ↦ ?_
  have h := natCast_le_rank_of_convex_chain (fun k ↦ (p k).1)
    (fun _ _ hkk' ↦ p.strictMono hkk') fun k ↦ (p k).2
  have : (p.length : ℕ∞) ≤ (Module.rank ℤ (Additive G)).toENat :=
    Cardinal.natCast_le_toENat.mpr h
  exact_mod_cast this

variable {L : Type*} [Field L]

/-- The unit group of a valuation subring is saturated in `Lˣ`: if `x ^ m` is a unit of `B` for
some `m ≠ 0`, then so is `x` (the value group is torsion-free). -/
theorem mem_unitGroup_of_zpow_mem (B : ValuationSubring L) {x : Lˣ} {m : ℤ} (hm : m ≠ 0)
    (h : x ^ m ∈ B.unitGroup) : x ∈ B.unitGroup := by
  rw [ValuationSubring.mem_unitGroup_iff] at h ⊢
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀] at h
  by_contra hne
  exact hm ((zpow_eq_one_iff_right₀ zero_le hne).mp h)

/-- **Height at most rational rank.** The Krull dimension (height) of a valuation ring is at
most the rational rank of its value group. -/
theorem ringKrullDim_le_ratRank (V : ValuationSubring L) :
    ringKrullDim V ≤ (ratRank V).toENat := by
  rw [ringKrullDim, Order.krullDim]
  refine iSup_le fun p ↦ ?_
  let B : Fin (p.length + 1) → ValuationSubring L := fun k ↦ V.ofPrime (p (Fin.rev k)).asIdeal
  have hBmono : Monotone B := by
    intro k k' hkk'
    exact V.ofPrime_le_of_le _ _ (p.monotone (Fin.rev_le_rev.mpr hkk'))
  have hBstrict : ∀ i : Fin p.length, B i.castSucc < B i.succ := by
    intro i
    refine lt_of_le_of_ne (hBmono (Fin.castSucc_le_succ i)) fun h ↦ ?_
    have hlt : (p (Fin.rev i.succ)).asIdeal < (p (Fin.rev i.castSucc)).asIdeal := by
      rw [Fin.rev_succ, Fin.rev_castSucc]
      exact p.step _
    have h1 := V.idealOfLE_ofPrime (p (Fin.rev i.castSucc)).asIdeal
    have h2 := V.idealOfLE_ofPrime (p (Fin.rev i.succ)).asIdeal
    have : (p (Fin.rev i.castSucc)).asIdeal = (p (Fin.rev i.succ)).asIdeal := by
      rw [← h1, ← h2]
      congr 1
    exact hlt.ne this.symm
  let U : Fin (p.length + 1) → Subgroup Lˣ := fun k ↦ (B k).unitGroup
  have hU : Monotone U := fun k k' h ↦ ValuationSubring.unitGroup_le_unitGroup.mpr (hBmono h)
  have hUstrict : ∀ i : Fin p.length, U i.castSucc < U i.succ := fun i ↦
    ValuationSubring.unitGroup_strictMono (hBstrict i)
  choose x hx hx' using fun i ↦ SetLike.exists_of_lt (hUstrict i)
  have hH : V.unitGroup ≤ U 0 :=
    ValuationSubring.unitGroup_le_unitGroup.mpr (V.le_ofPrime _)
  have hli := linearIndependent_mk_of_chain V.unitGroup U hU hH
    (fun k _ _ hm h ↦ mem_unitGroup_of_zpow_mem (B k) hm h) x hx hx'
  have hcard := hli.cardinal_lift_le_rank
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] at hcard
  have : (p.length : ℕ∞) ≤ (ratRank V).toENat := Cardinal.natCast_le_toENat.mpr hcard
  exact_mod_cast this

end Chain

section Abhyankar

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Units of `L` with the same valuation have the same class in the relative value group. -/
theorem mk_ofMul_eq_of_valuation_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) {x y : Lˣ} (h : v x = v y) :
    (QuotientAddGroup.mk (Additive.ofMul x) : RelAddValueGroup K v.valuationSubring) =
      QuotientAddGroup.mk (Additive.ofMul y) := by
  rw [QuotientAddGroup.eq, Additive.mem_toAddSubgroup]
  apply Subgroup.mem_sup_left
  rw [Valuation.mem_unitGroup_iff]
  have hy : v (y : L) ≠ 0 := by simp
  simp [h, hy]

/-- The class of an element of `Kˣ` in the relative value group vanishes. -/
theorem mk_ofMul_algebraMap_eq_zero (V : ValuationSubring L) (a : Kˣ) :
    (QuotientAddGroup.mk (Additive.ofMul (Units.map (algebraMap K L : K →* L) a)) :
      RelAddValueGroup K V) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup]
  exact Subgroup.mem_sup_right ⟨a, rfl⟩

/-- Multiplying by an element of `Kˣ` does not change the class in the relative value group. -/
theorem mk_ofMul_algebraMap_mul (V : ValuationSubring L) (a : Kˣ) (x : Lˣ) :
    (QuotientAddGroup.mk (Additive.ofMul (Units.map (algebraMap K L : K →* L) a * x)) :
      RelAddValueGroup K V) = QuotientAddGroup.mk (Additive.ofMul x) := by
  rw [QuotientAddGroup.eq, Additive.mem_toAddSubgroup]
  apply Subgroup.mem_sup_right
  refine ⟨a⁻¹, ?_⟩
  simp

/-- The class of a monomial `∏ bᵢ ^ mᵢ` is the corresponding `ℤ`-linear combination of the
classes of the `bᵢ`. -/
theorem mk_ofMul_prod_pow {G : Type*} [CommGroup G] (H : AddSubgroup (Additive G)) {ι : Type*}
    (b : ι → G) (m : ι →₀ ℕ) :
    (QuotientAddGroup.mk (Additive.ofMul (m.prod fun i k ↦ b i ^ k)) : Additive G ⧸ H) =
      Finsupp.linearCombination ℤ (fun i ↦ (QuotientAddGroup.mk (Additive.ofMul (b i)) :
        Additive G ⧸ H)) (Finsupp.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero m) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  simp [Finsupp.prod, Finsupp.sum, ofMul_prod, ofMul_pow, QuotientAddGroup.mk_sum, natCast_zsmul]

/-- **Orthogonality of monomials, value part.** Let `v` be a valuation on `L`, let `bᵢ ∈ Lˣ`
have `ℤ`-linearly independent classes in `|L^×|/|K^×|`, and let `cⱼ ∈ L` be such that every
nonzero polynomial over `K` takes at `c` a value lying in `|K^×|`. Then the family `(b, c)` is
algebraically independent over `K`: the terms of `P(b, c)` grouped by the monomials in `b` have
pairwise distinct values. -/
theorem algebraicIndependent_sumElim_of_valuation {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) {ι κ : Type*} (b : ι → Lˣ)
    (c : κ → L)
    (hb : LinearIndependent ℤ fun i ↦
      (QuotientAddGroup.mk (Additive.ofMul (b i)) : RelAddValueGroup K v.valuationSubring))
    (hc : ∀ Q : MvPolynomial κ K, Q ≠ 0 →
      ∃ a : K, a ≠ 0 ∧ v (aeval c Q) = v (algebraMap K L a)) :
    AlgebraicIndependent K (Sum.elim (fun i ↦ (b i : L)) c) := by
  classical
  set b' : ι → L := fun i ↦ (b i : L)
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  set P' := sumAlgEquiv K ι κ P
  have hP'0 : P' ≠ 0 := by
    intro h
    apply hP0
    simpa [P'] using congrArg (sumAlgEquiv K ι κ).symm h
  set P₁ : MvPolynomial ι L :=
    MvPolynomial.map (aeval c : MvPolynomial κ K →ₐ[K] L).toRingHom P'
  have hcomp : aeval (Sum.elim b' c) P = aeval b' P₁ := by
    have key : ∀ Q : MvPolynomial (ι ⊕ κ) K, aeval (Sum.elim b' c) Q =
        aeval b' (MvPolynomial.map (aeval c : MvPolynomial κ K →ₐ[K] L).toRingHom
          (sumAlgEquiv K ι κ Q)) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C a => simp [sumAlgEquiv_C_inl]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        rcases n with i | j
        · simp [hp, sumAlgEquiv_X_inl, b']
        · simp [hp, sumAlgEquiv_X_inr]
    exact key P
  have hcoeff : ∀ d, P₁.coeff d = aeval c (P'.coeff d) := fun d ↦ by
    simp [P₁, coeff_map]
  have hval : ∀ d ∈ P₁.support, ∃ a : K, a ≠ 0 ∧ v (P₁.coeff d) = v (algebraMap K L a) := by
    intro d hd
    have hne : P'.coeff d ≠ 0 := by
      intro h
      apply (mem_support_iff.mp hd)
      rw [hcoeff, h, map_zero]
    rw [hcoeff]
    exact hc _ hne
  choose! a ha hva using hval
  set t : (ι →₀ ℕ) → L := fun d ↦ P₁.coeff d * ∏ i ∈ d.support, b' i ^ d i
  have hsum : aeval b' P₁ = ∑ d ∈ P₁.support, t d := by
    rw [aeval_def, eval₂_eq]
    simp [t]
  let B : (ι →₀ ℕ) → Lˣ := fun d ↦ d.prod fun i k ↦ b i ^ k
  have hB : ∀ d, (B d : L) = ∏ i ∈ d.support, b' i ^ d i := by
    intro d
    simp [B, Finsupp.prod, b']
  let u : (ι →₀ ℕ) → Lˣ := fun d ↦
    if h : a d = 0 then 1 else Units.map (algebraMap K L : K →* L) (Units.mk0 (a d) h) * B d
  have hvt : ∀ d ∈ P₁.support, v (t d) = v (u d : L) := by
    intro d hd
    simp only [t, u, dif_neg (ha d hd)]
    rw [Units.val_mul, map_mul, map_mul, hva d hd, hB]
    simp
  have hinj : ∀ d ∈ P₁.support, ∀ d' ∈ P₁.support, v (t d) = v (t d') → d = d' := by
    intro d hd d' hd' h
    rw [hvt d hd, hvt d' hd'] at h
    have h1 := mk_ofMul_eq_of_valuation_eq (K := K) v h
    simp only [u, dif_neg (ha d hd), dif_neg (ha d' hd'), mk_ofMul_algebraMap_mul, B] at h1
    rw [mk_ofMul_prod_pow, mk_ofMul_prod_pow] at h1
    exact Finsupp.mapRange_injective _ _ Nat.cast_injective (hb h1)
  have hne : P₁.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    intro h0
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hP'0
    obtain ⟨a₀, ha₀, hv₀⟩ := hc _ hd
    have h1 : P₁.coeff d = 0 := by rw [h0, coeff_zero]
    rw [hcoeff] at h1
    rw [h1, map_zero, eq_comm, Valuation.zero_iff] at hv₀
    exact ha₀ ((map_eq_zero_iff _ (algebraMap K L).injective).mp hv₀)
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image P₁.support (fun d ↦ v (t d)) hne
  have hlt : ∀ d ∈ P₁.support \ {j}, v (t d) < v (t j) := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
    exact lt_of_le_of_ne (hjmax d hd.1) fun h ↦ hd.2 (hinj d hd.1 j hj h)
  have hvsum := Valuation.map_sum_eq_of_lt v hj hlt
  have htj : v (t j) ≠ 0 := by
    rw [hvt j hj]
    simp
  rw [← hsum, ← hcomp, hP, map_zero] at hvsum
  exact htj hvsum.symm

section Extension

variable {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀) (vL : Valuation L Γ₁)
  [vK.HasExtension vL]

/-- **Orthogonality of monomials, residue part.** If `cⱼ` lie in the valuation ring of `vL`
and their residues are algebraically independent over the residue field of `vK`, then for every
nonzero polynomial `Q` over `K` the value of `Q(c)` is the maximum of the values of the
coefficients of `Q`. -/
theorem exists_valuation_aeval_eq {κ : Type*} (c : κ → vL.valuationSubring)
    (hc : AlgebraicIndependent (ResidueField vK.valuationSubring)
      fun j ↦ residue vL.valuationSubring (c j))
    (Q : MvPolynomial κ K) (hQ : Q ≠ 0) :
    ∃ m ∈ Q.support, vL (aeval (fun j ↦ (c j : L)) Q) = vL (algebraMap K L (Q.coeff m)) ∧
      ∀ m', vL (algebraMap K L (Q.coeff m')) ≤ vL (algebraMap K L (Q.coeff m)) := by
  classical
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image Q.support
    (fun m ↦ vL (algebraMap K L (Q.coeff m))) (MvPolynomial.support_nonempty.mpr hQ)
  have hmax' : ∀ m', vL (algebraMap K L (Q.coeff m')) ≤ vL (algebraMap K L (Q.coeff m₀)) := by
    intro m'
    by_cases hm' : m' ∈ Q.support
    · exact hmax m' hm'
    · rw [MvPolynomial.notMem_support_iff.mp hm']
      simp
  refine ⟨m₀, hm₀, ?_, hmax'⟩
  set a := Q.coeff m₀ with ha_def
  have ha : a ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  have hva : vL (algebraMap K L a) ≠ 0 := by simpa using ha
  set Q' := C a⁻¹ * Q with hQ'
  have hQ'coeff : ∀ m, Q'.coeff m = a⁻¹ * Q.coeff m := fun m ↦ coeff_C_mul _ _ _
  have hQ'int : ∀ m, Q'.coeff m ∈ vK.valuationSubring := by
    intro m
    rw [Valuation.mem_valuationSubring_iff, ← Valuation.HasExtension.val_map_le_one_iff vK vL,
      hQ'coeff, map_mul, map_mul, map_inv₀, map_inv₀]
    exact (inv_mul_le_one₀ (zero_lt_iff.mpr hva)).mpr (hmax' m)
  let Q'' : MvPolynomial κ vK.valuationSubring :=
    ∑ m ∈ Q'.support, monomial m ⟨Q'.coeff m, hQ'int m⟩
  have hQ''map : MvPolynomial.map (algebraMap vK.valuationSubring K) Q'' = Q' := by
    simp only [Q'', map_sum, map_monomial]
    exact Q'.as_sum.symm
  have hQ''coeff : ∀ m, ((Q''.coeff m : vK.valuationSubring) : K) = Q'.coeff m := by
    intro m
    have := congrArg (coeff m) hQ''map
    rwa [coeff_map] at this
  set y : vL.valuationSubring := aeval c Q'' with hy_def
  have hy : (y : L) = aeval (fun j ↦ (c j : L)) Q' := by
    rw [← hQ''map, aeval_map_algebraMap]
    rw [show (y : L) = algebraMap vL.valuationSubring L y from rfl, hy_def,
      ← aeval_algebraMap_apply]
    rfl
  have hres : residue vL.valuationSubring y =
      aeval (fun j ↦ residue vL.valuationSubring (c j))
        (MvPolynomial.map (residue vK.valuationSubring) Q'') := by
    rw [hy_def, aeval_def, aeval_def, eval₂_map, eval₂_comp_left]
    rfl
  have hmap_ne : MvPolynomial.map (residue vK.valuationSubring) Q'' ≠ 0 := by
    intro h
    have h0 := congrArg (coeff m₀) h
    rw [coeff_map, coeff_zero] at h0
    have h1 : Q''.coeff m₀ = 1 :=
      Subtype.ext (by rw [hQ''coeff, hQ'coeff, ← ha_def, inv_mul_cancel₀ ha]; rfl)
    rw [h1, map_one] at h0
    exact one_ne_zero h0
  have hyres : residue vL.valuationSubring y ≠ 0 := by
    rw [hres]
    intro h
    exact hmap_ne (hc.eq_zero_of_aeval_eq_zero _ h)
  have hyunit : vL (y : L) = 1 :=
    (Valuation.valuationSubring.integers vL).isUnit_iff_valuation_eq_one.mp
      ((residue_ne_zero_iff_isUnit _).mp hyres)
  have hQeq : Q = C a * Q' := by
    rw [hQ', ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  rw [hQeq, map_mul, aeval_C, map_mul, ← hy, hyunit, mul_one]

/-- **Orthogonality of monomials** (Temkin, Lemma 2.1.2 `Abhlem`, proof). For an extension of
valued fields `L/K`, elements `bᵢ ∈ Lˣ` whose classes in `|L^×|/|K^×|` are `ℤ`-linearly
independent and elements `cⱼ` of the valuation ring of `L` whose residues are algebraically
independent over the residue field of `K` are together algebraically independent over `K`. -/
theorem algebraicIndependent_sumElim {ι κ : Type*} (b : ι → Lˣ) (c : κ → vL.valuationSubring)
    (hb : LinearIndependent ℤ fun i ↦
      (QuotientAddGroup.mk (Additive.ofMul (b i)) : RelAddValueGroup K vL.valuationSubring))
    (hc : AlgebraicIndependent (ResidueField vK.valuationSubring)
      fun j ↦ residue vL.valuationSubring (c j)) :
    AlgebraicIndependent K (Sum.elim (fun i ↦ (b i : L)) fun j ↦ (c j : L)) :=
  algebraicIndependent_sumElim_of_valuation vL b _ hb fun Q hQ ↦
    let ⟨m, hm, h, _⟩ := exists_valuation_aeval_eq vK vL c hc Q hQ
    ⟨Q.coeff m, mem_support_iff.mp hm, h⟩

/-- **Abhyankar's inequality** (Temkin, Lemma 2.1.2 `Abhlem`): for an extension of valued fields
`L/K`, `E_{L/K} + F_{L/K} ≤ trdeg (L/K)`, where `E_{L/K}` is the rational rank of
`|L^×|/|K^×|` and `F_{L/K}` the transcendence degree of the residue field extension. -/
theorem relRatRank_add_trdeg_le :
    relRatRank K vL.valuationSubring +
      Algebra.trdeg (ResidueField vK.valuationSubring) (ResidueField vL.valuationSubring) ≤
      Algebra.trdeg K L := by
  classical
  rw [relRatRank, Module.rank_def, Algebra.trdeg,
    Cardinal.ciSup_add_ciSup _ Cardinal.bddAbove_of_small _ Cardinal.bddAbove_of_small]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  choose b hb using fun x : s ↦ QuotientAddGroup.mk_surjective x.1
  choose c hc using fun y : t ↦ residue_surjective y.1
  have hs' : LinearIndependent ℤ fun x : s ↦ (x : RelAddValueGroup K vL.valuationSubring) := hs
  have hind := algebraicIndependent_sumElim vK vL (fun x ↦ Additive.toMul (b x)) c
    (by convert hs' with x; simp [hb]) (by convert ht with y; simp [hc])
  have h2 := hind.cardinalMk_le_trdeg
  rwa [← Cardinal.add_def] at h2

end Extension

/-- Elements of `Lˣ` whose classes in `|L^×|/|K^×|` are `ℤ`-linearly independent are
algebraically independent over `K`. -/
theorem algebraicIndependent_of_linearIndependent (V : ValuationSubring L) {ι : Type*}
    (b : ι → Lˣ)
    (hb : LinearIndependent ℤ fun i ↦
      (QuotientAddGroup.mk (Additive.ofMul (b i)) : RelAddValueGroup K V)) :
    AlgebraicIndependent K fun i ↦ (b i : L) := by
  have hb' : LinearIndependent ℤ fun i ↦ (QuotientAddGroup.mk (Additive.ofMul (b i)) :
      RelAddValueGroup K V.valuation.valuationSubring) := by
    rwa [ValuationSubring.valuationSubring_valuation]
  have h := algebraicIndependent_sumElim_of_valuation (K := K) V.valuation b
    (Empty.elim : Empty → L) hb' fun Q hQ ↦ by
      obtain ⟨a, rfl⟩ : ∃ a, C a = Q := ⟨Q.coeff 0, (eq_C_of_isEmpty Q).symm⟩
      refine ⟨a, fun ha ↦ hQ (by rw [ha, C_0]), ?_⟩
      rw [aeval_C]
  exact h.comp Sum.inl Sum.inl_injective

/-- A valuation on `L` extends its restriction to `K`. -/
instance hasExtension_comap {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) : (v.comap (algebraMap K L)).HasExtension v :=
  ⟨Valuation.IsEquiv.refl⟩

/-- `E_{L/K} ≤ trdeg (L/K)` for every valuation subring of `L`. -/
theorem relRatRank_le_trdeg (V : ValuationSubring L) : relRatRank K V ≤ Algebra.trdeg K L := by
  have h := le_self_add.trans (relRatRank_add_trdeg_le (V.valuation.comap (algebraMap K L))
    V.valuation)
  rwa [ValuationSubring.valuationSubring_valuation] at h

end Abhyankar

section FiniteHeight

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If the image `|K^×|` of `Kˣ` in the value group of `V` lies in a submodule `N`, then
`rat.rank |L^×| ≤ E_{L/K} + rank N`. -/
theorem ratRank_le_relRatRank_add (V : ValuationSubring L)
    (N : Submodule ℤ (AddValueGroup V))
    (hN : ∀ a : Kˣ, (QuotientAddGroup.mk (Additive.ofMul
      (Units.map (algebraMap K L : K →* L) a)) : AddValueGroup V) ∈ N) :
    ratRank V ≤ relRatRank K V + Module.rank ℤ N := by
  let f0 : AddValueGroup V →+ RelAddValueGroup K V :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id _) fun x hx ↦ by
      rw [AddSubgroup.mem_comap, AddMonoidHom.id_apply, Additive.mem_toAddSubgroup]
      exact Subgroup.mem_sup_left ((Additive.mem_toAddSubgroup _ _).mp hx)
  let f : AddValueGroup V →ₗ[ℤ] RelAddValueGroup K V :=
    AddMonoidHom.toIntLinearMap (M := AddValueGroup V) (M₂ := RelAddValueGroup K V) f0
  have hker : LinearMap.ker f ≤ N := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [LinearMap.mem_ker] at hx
    have h0 : (QuotientAddGroup.mk y : RelAddValueGroup K V) = 0 := hx
    rw [QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup] at h0
    obtain ⟨u, hu, r, ⟨a, rfl⟩, huy⟩ := Subgroup.mem_sup.mp h0
    have hyr : (QuotientAddGroup.mk y : AddValueGroup V) =
        QuotientAddGroup.mk (Additive.ofMul (Units.map (algebraMap K L : K →* L) a)) := by
      rw [QuotientAddGroup.eq, Additive.mem_toAddSubgroup]
      simp only [toMul_add, toMul_neg, toMul_ofMul, ← huy]
      convert inv_mem hu using 1
      rw [mul_inv_rev, mul_assoc, mul_comm u⁻¹, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hyr]
    exact hN a
  calc ratRank V = Module.rank ℤ (LinearMap.range f) + Module.rank ℤ (LinearMap.ker f) :=
        (LinearMap.rank_range_add_rank_ker f).symm
    _ ≤ relRatRank K V + Module.rank ℤ N :=
        add_le_add (Submodule.rank_le _) (Submodule.rank_mono hker)

/-- If the valuation is trivial on `K` (that is, `K ⊆ V`), then `rat.rank |L^×| ≤ E_{L/K}`. -/
theorem ratRank_le_relRatRank (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V) :
    ratRank V ≤ relRatRank K V := by
  have h := ratRank_le_relRatRank_add (K := K) V ⊥ fun a ↦ ?_
  · simpa using h
  rw [Submodule.mem_bot, QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup]
  let w : Vˣ := ⟨⟨algebraMap K L a, hV a⟩, ⟨algebraMap K L (a⁻¹ : Kˣ), hV _⟩,
    Subtype.ext (by simp), Subtype.ext (by simp)⟩
  rw [ValuationSubring.mem_unitGroup_iff]
  exact V.valuation_unit w

/-- **Finite height over a ground field** (relative form of Temkin, Corollary 2.1.3(i)
`approxcor`): a valuation ring `V` of `L` containing `K` has Krull dimension at most
`trdeg (L/K)`. -/
theorem ringKrullDim_le_trdeg (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V) :
    ringKrullDim V ≤ (Algebra.trdeg K L).toENat := by
  refine (ringKrullDim_le_ratRank V).trans ?_
  have h := Cardinal.toENat.monotone' ((ratRank_le_relRatRank V hV).trans
    (relRatRank_le_trdeg (K := K) V))
  exact_mod_cast h

/-- A valuation ring of `L` containing `K` with `trdeg (L/K) = d` has height at most `d`. -/
theorem ringKrullDim_le_of_trdeg_eq (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V) {d : ℕ} (hd : Algebra.trdeg K L = d) :
    ringKrullDim V ≤ d := by
  have h := ringKrullDim_le_trdeg V hV
  rw [hd, Cardinal.toENat_nat] at h
  exact_mod_cast h

end FiniteHeight

section PrimeField

variable {L : Type*} [Field L]

/-- The image of the prime subfield `⊥` in the value group of `V` is cyclic: it is generated by
the class of the residue characteristic `q` (or is trivial). -/
theorem exists_mem_span_singleton_prime (V : ValuationSubring L) :
    ∃ γ : AddValueGroup V, ∀ a : (⊥ : Subfield L)ˣ,
      (QuotientAddGroup.mk (Additive.ofMul
        (Units.map (algebraMap (⊥ : Subfield L) L : (⊥ : Subfield L) →* L) a)) :
          AddValueGroup V) ∈ Submodule.span ℤ {γ} := by
  classical
  let cl : Lˣ → AddValueGroup V := fun x ↦ QuotientAddGroup.mk (Additive.ofMul x)
  have cl_mul : ∀ x y, cl (x * y) = cl x + cl y := fun x y ↦ rfl
  have cl_inv : ∀ x, cl x⁻¹ = -cl x := fun x ↦ rfl
  have cl_pow : ∀ x (e : ℕ), cl (x ^ e) = e • cl x := fun x e ↦ rfl
  have cl_eq_zero : ∀ x, x ∈ V.unitGroup → cl x = 0 := fun x hx ↦ by
    simp only [cl]
    rw [QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup]
    exact hx
  set q := ringChar (ResidueField V)
  have hunit : ∀ n : ℕ, ¬ q ∣ n → ∃ h : (n : L) ≠ 0, Units.mk0 (n : L) h ∈ V.unitGroup := by
    intro n hn
    have h1 : residue V (n : V) ≠ 0 := by
      rw [map_natCast]
      exact fun h ↦ hn ((CharP.cast_eq_zero_iff (ResidueField V) q n).mp h)
    have hu : IsUnit (n : V) := (residue_ne_zero_iff_isUnit _).mp h1
    have hu' : V.valuation (n : L) = 1 := by
      have := V.valuation_unit hu.unit
      simpa using this
    have hn0 : (n : L) ≠ 0 := by
      intro h
      rw [h, map_zero] at hu'
      exact zero_ne_one hu'
    exact ⟨hn0, by rw [ValuationSubring.mem_unitGroup_iff]; simpa using hu'⟩
  let γ : AddValueGroup V := if h : (q : L) = 0 then 0 else cl (Units.mk0 (q : L) h)
  have hnat : ∀ (n : ℕ) (h : (n : L) ≠ 0),
      cl (Units.mk0 (n : L) h) ∈ Submodule.span ℤ {γ} := by
    intro n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn Nat.cast_zero
    obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q CharP.ringChar_ne_one
    obtain ⟨hn'0, hn'u⟩ := hunit n' hn'
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      have : Units.mk0 ((q ^ 0 * n' : ℕ) : L) hn = Units.mk0 (n' : L) hn'0 := by
        ext
        simp
      rw [this, cl_eq_zero _ hn'u]
      exact zero_mem _
    · have hq : (q : L) ≠ 0 := by
        intro h
        apply hn
        rw [Nat.cast_mul, Nat.cast_pow, h, zero_pow he.ne', zero_mul]
      have : Units.mk0 ((q ^ e * n' : ℕ) : L) hn =
          Units.mk0 (q : L) hq ^ e * Units.mk0 (n' : L) hn'0 := by
        ext
        simp
      rw [this, cl_mul, cl_pow]
      have hγ : γ = cl (Units.mk0 (q : L) hq) := dif_neg hq
      rw [← hγ]
      refine add_mem (Submodule.smul_of_tower_mem _ e (Submodule.mem_span_singleton_self γ)) ?_
      rw [cl_eq_zero _ hn'u]
      exact zero_mem _
  have hmone : cl (-1) = 0 := by
    apply cl_eq_zero
    rw [ValuationSubring.mem_unitGroup_iff]
    simp
  have hint : ∀ (k : ℤ) (h : (k : L) ≠ 0),
      cl (Units.mk0 (k : L) h) ∈ Submodule.span ℤ {γ} := by
    intro k hk
    have h' : ((k.natAbs : ℕ) : L) ≠ 0 := by
      intro h
      apply hk
      rcases Int.natAbs_eq k with hk' | hk'
      · rw [hk', Int.cast_natCast]
        exact h
      · rw [hk', Int.cast_neg, Int.cast_natCast, h, neg_zero]
    rcases Int.natAbs_eq k with hk' | hk'
    · have : Units.mk0 (k : L) hk = Units.mk0 ((k.natAbs : ℕ) : L) h' := by
        ext
        simp only [Units.val_mk0]
        conv_lhs => rw [hk']
        simp
      rw [this]
      exact hnat _ h'
    · have : Units.mk0 (k : L) hk = -1 * Units.mk0 ((k.natAbs : ℕ) : L) h' := by
        ext
        simp only [Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one]
        conv_lhs => rw [hk']
        simp
      rw [this, cl_mul]
      refine add_mem ?_ (hnat _ h')
      rw [hmone]
      exact zero_mem _
  refine ⟨γ, fun a ↦ ?_⟩
  have hmem : (((a : (⊥ : Subfield L)) : L)) ∈ Subfield.closure (∅ : Set L) := by
    rw [Subfield.closure_empty]
    exact (a : (⊥ : Subfield L)).2
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp hmem
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨l, rfl⟩ := hz
  have ha0 : ((a : (⊥ : Subfield L)) : L) ≠ 0 := by
    intro h
    exact a.ne_zero (Subtype.ext h)
  have hl : (l : L) ≠ 0 := by
    intro h
    apply ha0
    rw [← hyz, h, div_zero]
  have hk : (k : L) ≠ 0 := by
    intro h
    apply ha0
    rw [← hyz, h, zero_div]
  have : Units.map (algebraMap (⊥ : Subfield L) L : (⊥ : Subfield L) →* L) a =
      Units.mk0 (k : L) hk * (Units.mk0 (l : L) hl)⁻¹ := by
    ext
    change ((a : (⊥ : Subfield L)) : L) = _
    rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, ← hyz,
      div_eq_mul_inv]
  change cl _ ∈ _
  rw [this, cl_mul, cl_inv]
  exact add_mem (hint k hk) (neg_mem (hint l hl))

/-- `rat.rank |L^×| ≤ E_{L/P} + 1` for the prime subfield `P = ⊥`. -/
theorem ratRank_le_relRatRank_bot_add_one (V : ValuationSubring L) :
    ratRank V ≤ relRatRank (⊥ : Subfield L) V + 1 := by
  obtain ⟨γ, hγ⟩ := exists_mem_span_singleton_prime V
  refine (ratRank_le_relRatRank_add (K := (⊥ : Subfield L)) V _ hγ).trans ?_
  gcongr
  exact (rank_span_le _).trans (by simp)

/-- **Finite height** (Temkin, Corollary 2.1.3(i) `approxcor`): the height of a valuation ring
of `L` is at most `trdeg (L/P) + 1`, where `P = ⊥` is the prime subfield. -/
theorem ringKrullDim_le_trdeg_bot_add_one (V : ValuationSubring L) :
    ringKrullDim V ≤ ((Algebra.trdeg (⊥ : Subfield L) L).toENat + 1 : ℕ∞) := by
  refine (ringKrullDim_le_ratRank V).trans ?_
  have h : Cardinal.toENat (ratRank V) ≤
      Cardinal.toENat (Algebra.trdeg (⊥ : Subfield L) L + 1) :=
    OrderHomClass.mono _ ((ratRank_le_relRatRank_bot_add_one V).trans
      (add_le_add_left (relRatRank_le_trdeg (K := (⊥ : Subfield L)) V) 1))
  rw [map_add, map_one] at h
  exact_mod_cast h

/-- If `L` has absolute transcendence degree `d`, every valuation ring of `L` has height at most
`d + 1` (Temkin, Corollary 2.1.3(i) `approxcor`). -/
theorem ringKrullDim_le_of_trdeg_bot_eq (V : ValuationSubring L) {d : ℕ}
    (hd : Algebra.trdeg (⊥ : Subfield L) L = d) : ringKrullDim V ≤ (d + 1 : ℕ) := by
  have h := ringKrullDim_le_trdeg_bot_add_one V
  rw [hd, Cardinal.toENat_nat] at h
  exact_mod_cast h

end PrimeField

end DeJongAlterations.StableModification
