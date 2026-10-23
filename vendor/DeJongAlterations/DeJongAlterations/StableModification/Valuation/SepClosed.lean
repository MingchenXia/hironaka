import DeJongAlterations.StableModification.Valuation.RankOneBridge
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Valued fields that are separably closed

Let `K` be a separably closed field. This file proves the properties of valuations of `K` used by
Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`semi-stable.tex`), in §4 (lines 2797–2799 and 2818): the value group `|K^×|` is divisible, the
residue field of every valuation ring of `K` is separably closed, and algebraically closed unless
the valuation is trivial, and every valuation ring of `K` is strictly henselian. It also proves the
nowhere density of proper subspaces used in the proof of Theorem 2.1.8 (lines 2210–2212). Blueprint
chapter `sm-val-basic-vb.tex`.

Temkin states the §4 facts without proof ("easily seen for analytic fields, and the general case
follows by decompletion and induction on height"). The proofs here are direct and do not use
completions or finite height: divisibility uses the separable polynomials `X^ℓ - ε X - a`, and the
residue field and the henselian property rest on `natDegree_eq_one_or_derivative_eq_zero`: over an
integrally closed domain with separably closed fraction field, a monic irreducible polynomial is
linear or has zero derivative. These two statements hold for every integrally closed local domain
with separably closed fraction field, and are proved in that generality.

## Main results

* `exists_pow_valuation_eq`, `valueGroup_exists_pow_eq`: divisibility of the value group.
* `natDegree_eq_one_or_derivative_eq_zero`: monic irreducibles over a normal domain with separably
  closed fraction field.
* `exists_isRoot_of_separable_map`, `isSepClosed_residueField`, `isAlgClosed_residueField`:
  residue fields of integrally closed local domains with separably closed fraction field; for
  valuation subrings, the instance `instIsSepClosedResidueField`,
  `isAlgClosed_residueField_of_ne_top` and `isAlgClosed_residueField_ofPrime` (residue fields of
  the points of `Spec O`).
* `henselianLocalRing_of_isSepClosed` and the instance `instHenselianLocalRingValuationSubring`:
  strict henselianity.
* `interior_submodule_eq_empty`, `interior_submodule_eq_empty_of_valued`,
  `interior_submodule_eq_empty_of_krullDimLE_one`: proper subspaces have empty interior.
-/

noncomputable section

open IsLocalRing Polynomial

namespace DeJongAlterations.StableModification.Valuation

/-! ### Divisibility of the value group -/

section Divisible

variable {K : Type*} [Field K] [IsSepClosed K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

/-- **Divisibility by a prime** (Temkin, line 2797): over a separably closed field, every value
`|a|` has an `ℓ`-th root `|b|` for a prime `ℓ`. If `ℓ = 0` in `K` one uses a root of the separable
polynomial `X^ℓ - ε X - a` for a small `ε`. -/
theorem exists_pow_valuation_eq_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (a : K) :
    ∃ b : K, v b ^ ℓ = v a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha, hℓ.ne_zero]⟩
  have ha0 : 0 < v a := (Valuation.pos_iff v).mpr ha
  by_cases hℓK : (ℓ : K) = 0
  · set ε : K := if v a ≤ 1 then a else 1 with hεdef
    have hε0 : ε ≠ 0 := by
      rw [hεdef]
      split_ifs
      · exact ha
      · exact one_ne_zero
    have hε : v ε ^ ℓ ≤ v a ^ (ℓ - 1) := by
      by_cases h : v a ≤ 1
      · rw [hεdef, if_pos h]
        exact pow_le_pow_of_le_one zero_le h (Nat.sub_le ℓ 1)
      · rw [hεdef, if_neg h, map_one, one_pow]
        exact one_le_pow₀ (not_le.mp h).le
    obtain ⟨b, hb⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : K) (-ε) (-a)
      hℓK hℓ.two_le (neg_ne_zero.mpr hε0)
    have hb' : b ^ ℓ - a = ε * b := by linear_combination hb
    have hℓ1 : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel hℓ.one_lt.le
    refine ⟨b, ?_⟩
    rcases lt_trichotomy (v b ^ ℓ) (v a) with hlt | heq | hgt
    · exfalso
      have h1 : v (b ^ ℓ - a) = v a := v.map_sub_eq_of_lt_right (by rwa [map_pow])
      rw [hb', map_mul] at h1
      have h2 : v a ^ (ℓ - 1) * v a < v ε ^ ℓ * v a := by
        calc v a ^ (ℓ - 1) * v a = v a ^ ℓ := by rw [← pow_succ, hℓ1]
          _ = (v ε * v b) ^ ℓ := by rw [h1]
          _ = v ε ^ ℓ * v b ^ ℓ := mul_pow _ _ _
          _ < v ε ^ ℓ * v a :=
            mul_lt_mul_of_pos_left hlt (pow_pos ((Valuation.pos_iff v).mpr hε0) _)
      exact absurd hε (not_le.mpr (lt_of_mul_lt_mul_right h2 zero_le))
    · exact heq
    · exfalso
      have h1 : v (b ^ ℓ - a) = v b ^ ℓ := by
        rw [← map_pow]
        exact v.map_sub_eq_of_lt_left (by rwa [map_pow])
      rw [hb', map_mul] at h1
      have hb0 : 0 < v b := by
        by_contra h
        have : v b = 0 := le_antisymm (not_lt.mp h) zero_le
        rw [this, zero_pow hℓ.ne_zero] at hgt
        exact absurd hgt (not_lt.mpr zero_le)
      have h3 : v ε = v b ^ (ℓ - 1) := by
        have : v ε * v b = v b ^ (ℓ - 1) * v b := by rw [h1, ← pow_succ, hℓ1]
        exact mul_right_cancel₀ hb0.ne' this
      have h4 : v a ^ (ℓ - 1) < v ε ^ ℓ := by
        rw [h3, ← pow_mul, mul_comm, pow_mul]
        exact pow_lt_pow_left₀ hgt zero_le (by have := hℓ.two_le; omega)
      exact absurd hε (not_le.mpr h4)
  · have : NeZero (ℓ : K) := ⟨hℓK⟩
    obtain ⟨b, hb⟩ := IsSepClosed.exists_pow_nat_eq a ℓ
    exact ⟨b, by rw [← map_pow, hb]⟩

/-- **Divisibility of the value group** of a separably closed valued field (Temkin, line 2797):
every value `|a|` has an `n`-th root `|b|` for every `n ≠ 0`. -/
theorem exists_pow_valuation_eq {n : ℕ} (hn : n ≠ 0) (a : K) : ∃ b : K, v b ^ n = v a := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd rfl hn
  | one => exact ⟨a, pow_one _⟩
  | prime p hp => exact exists_pow_valuation_eq_of_prime v hp a
  | mul m k ihm ihk =>
    obtain ⟨c, hc⟩ := ihk (right_ne_zero_of_mul hn) a
    obtain ⟨b, hb⟩ := ihm (left_ne_zero_of_mul hn) c
    exact ⟨b, by rw [pow_mul, hb, hc]⟩

/-- The value group of a valuation subring of a separably closed field is divisible. -/
theorem valueGroup_exists_pow_eq (O : ValuationSubring K) {n : ℕ} (hn : n ≠ 0)
    (γ : O.ValueGroup) : ∃ δ : O.ValueGroup, δ ^ n = γ := by
  obtain ⟨a, rfl⟩ := O.valuation_surjective γ
  obtain ⟨b, hb⟩ := exists_pow_valuation_eq O.valuation hn a
  exact ⟨O.valuation b, hb⟩

end Divisible

/-! ### Integrally closed domains with separably closed fraction field -/

section IntegrallyClosed

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R] [IsSepClosed K]

include K

omit [IsDomain R] in
/-- Over an integrally closed domain with separably closed fraction field, a monic irreducible
polynomial is linear or has zero derivative. -/
theorem natDegree_eq_one_or_derivative_eq_zero {f : R[X]} (hf : f.Monic) (hirr : Irreducible f) :
    f.natDegree = 1 ∨ derivative f = 0 := by
  have hK : Irreducible (f.map (algebraMap R K)) :=
    (hf.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr
  by_cases hd : derivative f = 0
  · exact Or.inr hd
  · left
    have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
    have hsep : (f.map (algebraMap R K)).Separable := by
      rw [separable_iff_derivative_ne_zero hK, derivative_map]
      exact (Polynomial.map_ne_zero_iff hinj).mpr hd
    have h1 := IsSepClosed.degree_eq_one_of_irreducible K hK hsep
    rw [degree_map_eq_of_injective hinj] at h1
    exact natDegree_eq_of_degree_eq_some h1

variable [IsLocalRing R]

/-- **Lifting roots of separable residue polynomials**: over an integrally closed local domain with
separably closed fraction field, a monic polynomial of positive degree whose reduction is separable
has a root. -/
theorem exists_isRoot_of_separable_map :
    ∀ (n : ℕ) (g : R[X]), g.Monic → g.natDegree = n → 0 < n →
      (g.map (residue R)).Separable → ∃ c : R, g.IsRoot c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hg hgn hn hsep
  by_cases hirr : Irreducible g
  · rcases natDegree_eq_one_or_derivative_eq_zero R K hg hirr with h1 | h0
    · refine ⟨-g.coeff 0, ?_⟩
      rw [hg.eq_X_add_C h1]
      simp
    · exfalso
      have hder : derivative (g.map (residue R)) = 0 := by
        rw [derivative_map, h0, Polynomial.map_zero]
      rw [Polynomial.Separable, hder, isCoprime_zero_right] at hsep
      have := natDegree_eq_zero_of_isUnit hsep
      rw [hg.natDegree_map] at this
      omega
  · have hg1 : g ≠ 1 := by
      rintro rfl
      simp at hgn
      omega
    rw [hg.irreducible_iff_natDegree] at hirr
    push Not at hirr
    obtain ⟨g₁, g₂, hg₁, hg₂, hprod, h₁, h₂⟩ := hirr hg1
    have hdeg : g₁.natDegree + g₂.natDegree = n := by
      rw [← hgn, ← hprod, hg₁.natDegree_mul hg₂]
    have hsep₁ : (g₁.map (residue R)).Separable := by
      rw [← hprod, Polynomial.map_mul] at hsep
      exact hsep.of_mul_left
    obtain ⟨c, hc⟩ := ih g₁.natDegree (by omega) g₁ hg₁ rfl (by omega) hsep₁
    exact ⟨c, by rw [← hprod, IsRoot, eval_mul, hc.eq_zero, zero_mul]⟩

/-- **The residue field is separably closed** (Temkin, line 2797): for an integrally closed local
domain with separably closed fraction field. -/
theorem isSepClosed_residueField : IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun p hp hirr hsep ↦ ?_
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts p).mpr (map_surjective _ residue_surjective p)) hp
  obtain ⟨c, hc⟩ := exists_isRoot_of_separable_map R K _ g hgmon rfl
    (by rw [hgdeg]; exact hirr.natDegree_pos) (by rwa [hgmap])
  exact ⟨residue R c, by rw [← hgmap, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]⟩

omit [IsDomain R] in
/-- Every element of the residue field has a `p`-th root, `p = char κ > 0`, provided `R` is not a
field. -/
theorem exists_pow_residue_eq (hR : ¬IsField R) {p : ℕ} (hp : p.Prime)
    [CharP (ResidueField R) p] (α : ResidueField R) : ∃ β : ResidueField R, β ^ p = α := by
  obtain ⟨a, rfl⟩ := residue_surjective α
  have hroot : ∃ t ∈ maximalIdeal R, ∃ b : K,
      b ^ p - algebraMap R K t * b - algebraMap R K a = 0 := by
    by_cases hpK : (p : K) = 0
    · have hm : maximalIdeal R ≠ ⊥ := by
        rwa [Ne, ← IsLocalRing.isField_iff_maximalIdeal_eq]
      obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have ht0' : algebraMap R K t ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht0
      obtain ⟨b, hb⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : K)
        (-algebraMap R K t) (-algebraMap R K a) hpK hp.two_le (neg_ne_zero.mpr ht0')
      exact ⟨t, ht, b, by linear_combination hb⟩
    · have : NeZero (p : K) := ⟨hpK⟩
      obtain ⟨b, hb⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap R K a) p
      exact ⟨0, zero_mem _, b, by rw [hb, map_zero, zero_mul, sub_zero, sub_self]⟩
  obtain ⟨t, ht, b, hb⟩ := hroot
  set F : R[X] := X ^ p - C t * X - C a with hF
  have hFmon : F.Monic := by
    have h2 := hp.two_le
    rw [hF]
    refine ((monic_X_pow p).sub_of_left ?_).sub_of_left ?_
    · rw [degree_X_pow]
      exact (degree_C_mul_X_le t).trans_lt (by exact_mod_cast (by omega : 1 < p))
    · rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
      · exact (degree_C_le).trans_lt (by exact_mod_cast hp.pos)
      · rw [degree_X_pow]
        exact (degree_C_mul_X_le t).trans_lt (by exact_mod_cast (by omega : 1 < p))
  have hint : IsIntegral R b := by
    refine ⟨F, hFmon, ?_⟩
    rw [hF]
    simp only [eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
    exact hb
  obtain ⟨b₀, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hb₀ : b₀ ^ p - t * b₀ - a = 0 := by
    apply IsFractionRing.injective R K
    rw [map_zero, map_sub, map_sub, map_mul, map_pow]
    exact hb
  refine ⟨residue R b₀, ?_⟩
  have := congrArg (residue R) hb₀
  rw [map_sub, map_sub, map_mul, map_pow, map_zero, (residue_eq_zero_iff t).mpr ht, zero_mul,
    sub_zero, sub_eq_zero] at this
  exact this

/-- **The residue field is algebraically closed** (Temkin, line 2798) if `R` is not a field: it is
separably closed and perfect. -/
theorem isAlgClosed_residueField (hR : ¬IsField R) : IsAlgClosed (ResidueField R) := by
  have := isSepClosed_residueField R K
  obtain ⟨p, hchar⟩ := CharP.exists (ResidueField R)
  rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
  · have : Fact p.Prime := ⟨hp⟩
    have : ExpChar (ResidueField R) p := ExpChar.prime hp
    have : PerfectRing (ResidueField R) p := PerfectRing.ofSurjective _ p fun α ↦ by
      obtain ⟨β, hβ⟩ := exists_pow_residue_eq R K hR hp α
      exact ⟨β, by rw [frobenius_def, hβ]⟩
    have := PerfectRing.toPerfectField (ResidueField R) p
    exact IsSepClosed.isAlgClosed_of_perfectField _
  · subst hp
    have : CharZero (ResidueField R) := CharP.charP_zero_iff_charZero _ |>.mp hchar
    exact IsSepClosed.isAlgClosed_of_perfectField _

/-- **Strict henselianity** (Temkin, line 2818): an integrally closed local domain with separably
closed fraction field is henselian; its residue field is separably closed
(`isSepClosed_residueField`). -/
theorem henselianLocalRing_of_isSepClosed : HenselianLocalRing R := by
  refine ⟨?_⟩
  suffices H : ∀ (n : ℕ) (f : R[X]), f.Monic → f.natDegree = n → ∀ a₀ : R,
      f.eval a₀ ∈ maximalIdeal R → IsUnit (f.derivative.eval a₀) →
        ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R from
    fun f hf a₀ h₁ h₂ ↦ H _ f hf rfl a₀ h₁ h₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hfn a₀ h₁ h₂
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [eval_one] at h₁
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h₁)
  by_cases hirr : Irreducible f
  · rcases natDegree_eq_one_or_derivative_eq_zero R K hf hirr with h1 | h0
    · have hfe := hf.eq_X_add_C h1
      refine ⟨-f.coeff 0, ?_, ?_⟩
      · rw [hfe]
        simp
      · rw [hfe] at h₁
        simp only [eval_add, eval_X, eval_C] at h₁
        have : -f.coeff 0 - a₀ = -(a₀ + f.coeff 0) := by ring
        rw [this]
        exact neg_mem h₁
    · rw [h0, eval_zero] at h₂
      exact absurd h₂ not_isUnit_zero
  · rw [hf.irreducible_iff_natDegree] at hirr
    push Not at hirr
    obtain ⟨g, h, hg, hh, rfl, hg0, hh0⟩ := hirr hf1
    have hdeg : g.natDegree + h.natDegree = n := by rw [← hfn, hg.natDegree_mul hh]
    rw [eval_mul] at h₁
    rw [derivative_mul, eval_add, eval_mul, eval_mul] at h₂
    have hnu : ∀ x y : R, x ∈ maximalIdeal R → ¬IsUnit (x * y) := fun x y hx hu ↦
      (mem_maximalIdeal _).mp (Ideal.mul_mem_right y _ hx) hu
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h₁ with hg₁ | hh₁
    · have hu : IsUnit (g.derivative.eval a₀) := by
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h₂ with hu | hu
        · exact isUnit_of_mul_isUnit_left hu
        · exact absurd hu (hnu _ _ hg₁)
      obtain ⟨a, ha, ha'⟩ := ih g.natDegree (by omega) g hg rfl a₀ hg₁ hu
      exact ⟨a, by rw [IsRoot, eval_mul, ha.eq_zero, zero_mul], ha'⟩
    · have hu : IsUnit (h.derivative.eval a₀) := by
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h₂ with hu | hu
        · rw [mul_comm] at hu
          exact absurd hu (hnu _ _ hh₁)
        · exact isUnit_of_mul_isUnit_right hu
      obtain ⟨a, ha, ha'⟩ := ih h.natDegree (by omega) h hh rfl a₀ hh₁ hu
      exact ⟨a, by rw [IsRoot, eval_mul, ha.eq_zero, mul_zero], ha'⟩

end IntegrallyClosed

/-! ### Valuation rings of separably closed fields -/

section ValuationSubring

variable {K : Type*} [Field K] [IsSepClosed K] (O : ValuationSubring K)

/-- A valuation ring of a separably closed field is henselian (hence strictly henselian, by
`instIsSepClosedResidueField`). -/
instance instHenselianLocalRingValuationSubring : HenselianLocalRing O :=
  henselianLocalRing_of_isSepClosed O K

/-- The residue field of a valuation ring of a separably closed field is separably closed. -/
instance instIsSepClosedResidueField : IsSepClosed (ResidueField O) :=
  isSepClosed_residueField O K

/-- The residue field of a nontrivial valuation ring of a separably closed field is algebraically
closed. -/
theorem isAlgClosed_residueField_of_ne_top (hO : O ≠ ⊤) : IsAlgClosed (ResidueField O) :=
  isAlgClosed_residueField O K (by rwa [isField_iff_eq_top])

/-- **Residue fields of the points of `Spec O`** (Temkin, lines 2797–2799): for a prime `P` of a
valuation ring `O` of a separably closed field, the residue field of the coarsening `O_P` (the
residue field of the point `P`) is algebraically closed if `P ≠ 0`; it is separably closed in all
cases (`instIsSepClosedResidueField`). -/
theorem isAlgClosed_residueField_ofPrime (P : Ideal O) [P.IsPrime] (hP : P ≠ ⊥) :
    IsAlgClosed (ResidueField (O.ofPrime P)) :=
  isAlgClosed_residueField_of_ne_top _ (by rwa [Ne, ofPrime_eq_top_iff])

end ValuationSubring

/-! ### Nowhere density of proper subspaces -/

section NowhereDense

open Topology Filter

/-- **Proper subspaces have empty interior**: a proper subspace of a topological vector space over
a topological field in which `0` is not isolated has empty interior. -/
theorem interior_submodule_eq_empty {k M : Type*} [Field k] [TopologicalSpace k]
    [(𝓝[≠] (0 : k)).NeBot] [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module k M]
    [ContinuousSMul k M] {W : Submodule k M} (hW : W ≠ ⊤) : interior (W : Set M) = ∅ := by
  have hunits : {x : k | IsUnit x} = {0}ᶜ := by
    ext x
    simp [isUnit_iff_ne_zero]
  have : (𝓝[{x : k | IsUnit x}] 0).NeBot := by
    rw [hunits]
    infer_instance
  by_contra h
  exact hW (W.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr h))

/-- The complement of a proper subspace is dense. -/
theorem dense_compl_submodule {k M : Type*} [Field k] [TopologicalSpace k]
    [(𝓝[≠] (0 : k)).NeBot] [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module k M]
    [ContinuousSMul k M] {W : Submodule k M} (hW : W ≠ ⊤) : Dense (W : Set M)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (interior_submodule_eq_empty hW)

/-- **Proper subspaces have empty interior, valued form** (Temkin, lines 2210–2212): let `K` carry
the topology of a valuation and let `k → K` be a field homomorphism whose values come arbitrarily
close to `0` (for every `w ≠ 0` there is `c ∈ kˣ` with `|c| < |w|`). Then every proper
`k`-subspace of `K` has empty interior. -/
theorem interior_submodule_eq_empty_of_valued {K Γ₀ k : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Field k] [Algebra k K]
    (hk : ∀ w : K, w ≠ 0 → ∃ c : k, c ≠ 0 ∧ Valued.v (algebraMap k K c) < Valued.v w)
    {W : Submodule k K} (hW : W ≠ ⊤) : interior (W : Set K) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hxW : x ∈ W := interior_subset hx
  rw [mem_interior_iff_mem_nhds, Valued.mem_nhds] at hx
  obtain ⟨γ, hγ⟩ := hx
  obtain ⟨y, hy⟩ : ∃ y, y ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.mpr fun y _ ↦ h y)
  have hy0 : y ≠ 0 := fun h ↦ hy (h ▸ W.zero_mem)
  obtain ⟨w, hw⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact γ.ne_zero hw.symm
  obtain ⟨c, hc0, hc⟩ := hk (w * y⁻¹) (mul_ne_zero hw0 (inv_ne_zero hy0))
  have hcy : Valued.v (algebraMap k K c * y) < Valued.v w := by
    have hvy : 0 < Valued.v y := (Valuation.pos_iff _).mpr hy0
    rw [map_mul]
    calc Valued.v (algebraMap k K c) * Valued.v y < Valued.v (w * y⁻¹) * Valued.v y :=
          mul_lt_mul_of_pos_right hc hvy
      _ = Valued.v w := by rw [map_mul, map_inv₀, mul_assoc, inv_mul_cancel₀ hvy.ne', mul_one]
  have hmem : x + algebraMap k K c * y ∈ W := by
    apply hγ
    change Valued.v.restrict (x + algebraMap k K c * y - x) < γ.1
    rw [add_sub_cancel_left, ← hw, ← Valuation.restrict_def, Valuation.restrict_lt_iff]
    exact hcy
  have hcyW : c • y ∈ W := by
    rw [Algebra.smul_def]
    have := W.sub_mem hmem hxW
    rwa [add_sub_cancel_left] at this
  apply hy
  have := W.smul_mem c⁻¹ hcyW
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

/-- If the valuation ring of `v` has height at most one and `v` is nontrivial on the image of
`k`, the values of `k` come arbitrarily close to `0`. -/
theorem exists_valuation_lt_of_krullDimLE_one {K Γ₀ k : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Field k] [Algebra k K] (v : Valuation K Γ₀)
    (hv : Ring.KrullDimLE 1 v.valuationSubring)
    (hk : ∃ c : k, v (algebraMap k K c) ≠ 0 ∧ v (algebraMap k K c) ≠ 1) :
    ∀ w : K, w ≠ 0 → ∃ c : k, c ≠ 0 ∧ v (algebraMap k K c) < v w := by
  obtain ⟨c, hc0, hc1⟩ := hk
  have hcne : c ≠ 0 := by
    rintro rfl
    simp at hc0
  obtain ⟨c₀, hc₀0, hc₀1, hc₀pos⟩ : ∃ c₀ : k, c₀ ≠ 0 ∧ v (algebraMap k K c₀) < 1 ∧
      0 < v (algebraMap k K c₀) := by
    rcases lt_or_gt_of_ne hc1 with h | h
    · exact ⟨c, hcne, h, (Valuation.pos_iff v).mpr (by simpa using hc0)⟩
    · refine ⟨c⁻¹, inv_ne_zero hcne, ?_, ?_⟩
      · rw [map_inv₀, map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
      · rw [map_inv₀, map_inv₀]
        exact inv_pos.mpr ((Valuation.pos_iff v).mpr (by simpa using hc0))
  intro w hw
  obtain ⟨n, hn⟩ := (krullDimLE_one_iff_forall_pow_le v).mp hv w _ hw hc₀1
  refine ⟨c₀ ^ (n + 1), pow_ne_zero _ hc₀0, ?_⟩
  rw [map_pow, map_pow, pow_succ]
  calc v (algebraMap k K c₀) ^ n * v (algebraMap k K c₀) < v (algebraMap k K c₀) ^ n * 1 :=
        mul_lt_mul_of_pos_left hc₀1 (pow_pos hc₀pos n)
    _ = v (algebraMap k K c₀) ^ n := mul_one _
    _ ≤ v w := hn

/-- **Nowhere density in height one** (Temkin, lines 2210–2212): if `K` carries the topology of a
valuation whose valuation ring has height at most one and which is nontrivial on `k`, every proper
`k`-subspace of `K` (for instance `k Kᵖ`) has empty interior. -/
theorem interior_submodule_eq_empty_of_krullDimLE_one {K Γ₀ k : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Field k] [Algebra k K]
    (hv : Ring.KrullDimLE 1 (Valued.v : Valuation K Γ₀).valuationSubring)
    (hk : ∃ c : k, Valued.v (algebraMap k K c) ≠ 0 ∧ Valued.v (algebraMap k K c) ≠ 1)
    {W : Submodule k K} (hW : W ≠ ⊤) : interior (W : Set K) = ∅ :=
  interior_submodule_eq_empty_of_valued (exists_valuation_lt_of_krullDimLE_one _ hv hk) hW

end NowhereDense

end DeJongAlterations.StableModification.Valuation
