import DeJongAlterations.StableModification.Abhyankar
import DeJongAlterations.StableModification.Valuation.SepClosed

/-!
# Valuations in the model situations of local uniformization (Temkin, Proposition 4.3.1)

Let `K` be a field with a valuation `v_K` (valuation ring `R`, residue field `K̃`), `L/K` a field
extension and `v_L` a valuation of `L` extending `v_K` (valuation ring `𝒪`, residue field `L̃`).
This file proves the valuation theory inside the proof of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), Proposition 4.3.1 (`cofinprop`, `semi-stable.tex`
lines 2956–3017), for a point `𝔵 ∈ 𝔊⁰`, i.e. a valuation of `L = K(C)` whose residue field has
transcendence degree one over `K̃`. Blueprint chapter `sm-local-uniformization-model.tex`.

## Main results

* `relRatRank_eq_zero` (`lem:sm-lu-value-group`, T:2981–2983): if `trdeg (L/K) ≤ 1` and some
  residue in `L̃` is transcendental over `K̃`, then `E_{L/K} = 0` by Abhyankar's inequality
  (`relRatRank_add_trdeg_le`).
* `exists_valuation_eq_algebraMap` (T:2983–2985): if moreover `K` is separably closed, then
  `|L^×| = |K^×|`: the group `|L^×|/|K^×|` is torsion, and `|K^×|` is divisible
  (`Valuation.exists_pow_valuation_eq`).
* `exists_node_parameter` (stage 1, T:2985–2987): for `u, w ∈ 𝒪` with `u ≠ 0` and `uw = a ∈ K`
  there are `π, b ∈ R` with `|u| = |π|` and `a = πb`.
* `adjoin_linearResidues_eq_top` (`lem:sm-lu-residue-generators`, T:2998–3005): if
  `L = K(T)`, `T ∈ 𝒪`, `K` is separably closed and `L̃/K̃` is transcendental, then `L̃` is generated
  over `K̃` by the residues of the elements `(T - a)/π ∈ 𝒪`, `a, π ∈ K`.
* `exists_transcendental_residue_sub` (T:3005–3011): if in addition the residue of `T` is algebraic
  over `K̃` (the centre is a closed point of the closed fibre), there are `a, π ∈ R` with
  `0 < |π| < 1`, `|T - a| = |π|` and the residue of `(T - a)/π` transcendental over `K̃`.

## Adaptations

* Temkin writes an element of `L∖R` of absolute value one as a product of powers of
  `fᵢ(T)/πᵢ` with `fᵢ` irreducible and replaces an inseparable `f` by `f + ωT`, `ω ∈ π𝔪_R`,
  "because the residues coincide"; `f + ωT` is separable but in general not irreducible, and one
  has to factor it again. We argue by induction on the degree: a reducible `p` is handled by its
  factors, a separable irreducible `p` is linear (`IsSepClosed.degree_eq_one_of_irreducible`), and
  for an inseparable irreducible `p` the polynomial `p + ωT` (same residue) is separable of the same
  degree `≥ 2`, hence reducible.
* The perturbation needs `|ω| < |π|`, which exists only if `v_K` is nontrivial; for trivial
  `v_K` every polynomial over `K` has coefficients in `R` and its residue lies in `K̃[T̃]`
  (`residue_aeval_mem_adjoin`).
* Temkin's `L` is `K(T)` with the restricted valuation (line 2999); we assume
  `IntermediateField.adjoin K {T} = ⊤` and deduce `trdeg (L/K) ≤ 1`
  (`trdeg_le_one_of_adjoin_eq_top`). The condition `trdeg (L̃/K̃) = 1` is used only through one
  transcendental residue.
-/

noncomputable section

open IsLocalRing Polynomial

namespace DeJongAlterations.StableModification.LocalUniformization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

section ValueGroup

/-- A residue transcendental over `K̃` gives `trdeg (L̃/K̃) ≥ 1`. -/
theorem one_le_trdeg_residueField {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t)) :
    1 ≤ Algebra.trdeg (ResidueField vK.valuationSubring) (ResidueField vL.valuationSubring) := by
  have h : AlgebraicIndependent (ResidueField vK.valuationSubring)
      (fun _ : PUnit ↦ residue vL.valuationSubring t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  simpa using h.cardinalMk_le_trdeg

/-- **`E_{L/K} = 0`** (Temkin, T:2981–2983; `lem:sm-lu-value-group`): if `trdeg (L/K) ≤ 1` and
`L̃/K̃` is transcendental, Abhyankar's inequality `E_{L/K} + F_{L/K} ≤ trdeg (L/K)` forces the
rational rank of `|L^×|/|K^×|` to vanish. -/
theorem relRatRank_eq_zero (htr : Algebra.trdeg K L ≤ 1) {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t)) :
    relRatRank K vL.valuationSubring = 0 := by
  have h := (relRatRank_add_trdeg_le vK vL).trans htr
  have h1 := one_le_trdeg_residueField vK vL ht
  by_contra hne
  have h2 : (1 : Cardinal) ≤ relRatRank K vL.valuationSubring :=
    Cardinal.one_le_iff_ne_zero.mpr hne
  have : (1 : Cardinal) + 1 ≤ 1 := (add_le_add h2 h1).trans h
  rw [one_add_one_eq_two] at this
  exact absurd this (by norm_num)

/-- **`|L^×| = |K^×|`** (Temkin, T:2983–2985; `lem:sm-lu-value-group`): if `K` is separably
closed, `trdeg (L/K) ≤ 1` and `L̃/K̃` is transcendental, every value of `v_L` is the value of an
element of `K`. Since `E_{L/K} = 0`, some power `x^n` (`n ≠ 0`) has the value of an element of
`K`, and `|K^×|` is divisible. -/
theorem exists_valuation_eq_algebraMap [IsSepClosed K] (htr : Algebra.trdeg K L ≤ 1)
    {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t))
    (x : L) : ∃ c : K, vL x = vL (algebraMap K L c) := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  set xu : Lˣ := Units.mk0 x hx
  have hE := relRatRank_eq_zero vK vL htr ht
  rw [relRatRank, rank_eq_zero_iff] at hE
  obtain ⟨n, hn, hnx⟩ := hE (QuotientAddGroup.mk (Additive.ofMul xu))
  rw [← QuotientAddGroup.mk_zsmul, ← ofMul_zpow, QuotientAddGroup.eq_zero_iff,
    Additive.mem_toAddSubgroup, toMul_ofMul, Subgroup.mem_sup] at hnx
  obtain ⟨y, hy, z, ⟨k, rfl⟩, hyz⟩ := hnx
  have hvy : vL (y : L) = 1 :=
    (Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.mpr
      ((ValuationSubring.mem_unitGroup_iff _ _).mp hy)
  have hval : vL x ^ n = vL (algebraMap K L k) := by
    have h := congrArg (fun w : Lˣ ↦ vL (w : L)) hyz
    simp only [Units.val_mul, map_mul, hvy, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀] at h
    exact h.symm
  -- reduce to a positive exponent
  obtain ⟨m, hm, k', hk'⟩ : ∃ m : ℕ, m ≠ 0 ∧ ∃ k' : K, vL x ^ m = vL (algebraMap K L k') := by
    obtain ⟨m, hnm⟩ := Int.eq_nat_or_neg n
    refine ⟨m, ?_, ?_⟩
    · rintro rfl
      rcases hnm with rfl | rfl <;> simp at hn
    · rcases hnm with rfl | rfl
      · exact ⟨k, by rw [← hval, zpow_natCast]⟩
      · exact ⟨k⁻¹, by rw [map_inv₀, map_inv₀, ← hval, zpow_neg, zpow_natCast, inv_inv]⟩
  obtain ⟨d, hd⟩ := Valuation.exists_pow_valuation_eq vK hm k'
  have hd' : vL (algebraMap K L d) ^ m = vL (algebraMap K L k') := by
    rw [← map_pow, ← map_pow, Valuation.HasExtension.val_map_eq_iff vK vL, map_pow, hd]
  exact ⟨d, pow_left_injective hm (hk'.trans hd'.symm)⟩

/-- **The parameter of the node stage** (Temkin, T:2985–2987): if every value of `v_L` is the value
of an element of `K`, `u, w ∈ 𝒪`, `u ≠ 0` and `u w = a ∈ K`, then there are `π, b ∈ R` with
`π ≠ 0`, `a = π b` and `|u| = |π|` (so `π ∣ a` in `R`). -/
theorem exists_node_parameter (hval : ∀ x : L, ∃ c : K, vL x = vL (algebraMap K L c))
    {u w : L} {a : K} (hu : vL u ≤ 1) (hw : vL w ≤ 1) (hu0 : u ≠ 0)
    (huw : u * w = algebraMap K L a) :
    ∃ π b : K, π ≠ 0 ∧ vK π ≤ 1 ∧ vK b ≤ 1 ∧ a = π * b ∧ vL u = vL (algebraMap K L π) := by
  obtain ⟨π, hπ⟩ := hval u
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hπ
    exact hu0 ((map_eq_zero vL).mp hπ)
  have hπL : algebraMap K L π ≠ 0 := (_root_.map_ne_zero _).mpr hπ0
  refine ⟨π, a / π, hπ0, ?_, ?_, by field_simp, hπ⟩
  · rw [← Valuation.HasExtension.val_map_le_one_iff vK vL, ← hπ]
    exact hu
  · rw [← Valuation.HasExtension.val_map_le_one_iff vK vL, map_div₀, ← huw, map_div₀, map_mul,
      ← hπ, mul_div_cancel_left₀ _ ((_root_.map_ne_zero vL).mpr hu0)]
    exact hw

end ValueGroup

section Residues

/-! ### Residues of rational functions -/

/-- A residue of an element of value `< 1` vanishes. -/
theorem residue_eq_zero_of_lt_one {s : vL.valuationSubring} (h : vL (s : L) < 1) :
    residue vL.valuationSubring s = 0 := by
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring vL).lt_one_iff_lt_one.mp h

/-- An element of `𝒪` with nonzero residue has value one. -/
theorem valuation_eq_one_of_residue_ne_zero {s : vL.valuationSubring}
    (h : residue vL.valuationSubring s ≠ 0) : vL (s : L) = 1 :=
  le_antisymm ((Valuation.mem_valuationSubring_iff vL _).mp s.2)
    (not_lt.mp fun hlt ↦ h (residue_eq_zero_of_lt_one vL hlt))

/-- An element of `𝒪` of value one has nonzero residue. -/
theorem residue_ne_zero_of_valuation_eq_one {s : vL.valuationSubring} (h : vL (s : L) = 1) :
    residue vL.valuationSubring s ≠ 0 := by
  rw [Ne, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring vL).lt_one_iff_lt_one, h]
  exact lt_irrefl 1

/-- The residue of an element of `𝒪` which is the image of an element of `R` comes from `K̃`. -/
theorem residue_eq_algebraMap {s : vL.valuationSubring} {c : K} (hc : vK c ≤ 1)
    (hs : (s : L) = algebraMap K L c) :
    residue vL.valuationSubring s =
      algebraMap (ResidueField vK.valuationSubring) (ResidueField vL.valuationSubring)
        (residue vK.valuationSubring ⟨c, (Valuation.mem_valuationSubring_iff vK c).mpr hc⟩) := by
  have : s = algebraMap vK.valuationSubring vL.valuationSubring
      ⟨c, (Valuation.mem_valuationSubring_iff vK c).mpr hc⟩ :=
    Subtype.ext (by rw [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]; exact hs)
  rw [this]
  rfl

variable (T : L)

variable (K) in
/-- The residues of the elements `(T - a)/π` of `𝒪`, `a, π ∈ K` (Temkin, T:3005–3006). -/
def linearResidues : Set (ResidueField vL.valuationSubring) :=
  {z | ∃ (a π : K) (s : vL.valuationSubring),
    (s : L) = (T - algebraMap K L a) / algebraMap K L π ∧ residue vL.valuationSubring s = z}

/-- The subfield of `L̃` generated over `K̃` by `linearResidues`. -/
abbrev linearResidueField : IntermediateField (ResidueField vK.valuationSubring)
    (ResidueField vL.valuationSubring) :=
  IntermediateField.adjoin (ResidueField vK.valuationSubring) (linearResidues K vL T)

theorem residue_mem_linearResidueField_of_eq_algebraMap {s : vL.valuationSubring} {c : K}
    (hc : vK c ≤ 1) (hs : (s : L) = algebraMap K L c) :
    residue vL.valuationSubring s ∈ linearResidueField vK vL T := by
  rw [residue_eq_algebraMap vK vL hc hs]
  exact IntermediateField.algebraMap_mem _ _

/-- **Polynomials with coefficients in `R`** (used when `v_K` is trivial): if `T ∈ 𝒪` and the
coefficients of `q` lie in `R`, the residue of `q(T)` lies in `K̃[T̃]`. -/
theorem residue_aeval_mem_adjoin (hT : vL T ≤ 1) (q : K[X]) (hq : ∀ i, vK (q.coeff i) ≤ 1)
    (s : vL.valuationSubring) (hs : (s : L) = aeval T q) :
    residue vL.valuationSubring s ∈ linearResidueField vK vL T := by
  let tO : vL.valuationSubring := ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩
  have htO : residue vL.valuationSubring tO ∈ linearResidueField vK vL T := by
    refine IntermediateField.subset_adjoin _ _ ⟨0, 1, tO, ?_, rfl⟩
    simp [tO]
  let c : ℕ → vL.valuationSubring := fun i ↦
    ⟨algebraMap K L (q.coeff i), (Valuation.mem_valuationSubring_iff vL _).mpr
      ((Valuation.HasExtension.val_map_le_one_iff vK vL _).mpr (hq i))⟩
  have hsum : s = ∑ i ∈ Finset.range (q.natDegree + 1), c i * tO ^ i := by
    apply Subtype.ext
    rw [hs, aeval_eq_sum_range]
    push_cast
    simp [c, tO, Algebra.smul_def]
  rw [hsum, map_sum]
  refine IntermediateField.sum_mem _ fun i _ ↦ ?_
  rw [map_mul, map_pow]
  exact IntermediateField.mul_mem _
    (residue_mem_linearResidueField_of_eq_algebraMap vK vL T (hq i) rfl)
    (pow_mem htO i)

/-- `trdeg (K(T)/K) ≤ 1`. -/
theorem trdeg_le_one_of_adjoin_eq_top (hgen : IntermediateField.adjoin K {T} = ⊤) :
    Algebra.trdeg K L ≤ 1 := by
  have : Algebra.IsAlgebraic (Algebra.adjoin K {T}) L := by
    refine ⟨fun x ↦ ?_⟩
    have hx : x ∈ IntermediateField.adjoin K {T} := hgen ▸ IntermediateField.mem_top
    obtain ⟨r, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K x).mp hx
    by_cases hq : aeval T q = 0
    · rw [hq, div_zero]
      exact isAlgebraic_zero
    let r' : Algebra.adjoin K {T} := ⟨aeval T r, aeval_mem_adjoin_singleton K T⟩
    let q' : Algebra.adjoin K {T} := ⟨aeval T q, aeval_mem_adjoin_singleton K T⟩
    have hq' : q' ≠ 0 := fun h ↦ hq (congrArg Subtype.val h)
    refine ⟨C q' * X - C r', fun h ↦ hq' ?_, ?_⟩
    · have := congrArg (coeff · 1) h
      simpa using this
    · simp only [map_sub, map_mul, aeval_C, aeval_X]
      change aeval T q * (aeval T r / aeval T q) - aeval T r = 0
      field_simp
      ring
  have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({T} : Set L)
  rwa [Cardinal.mk_singleton] at h

variable [IsSepClosed K]

/-- **Residues of `p(T)/π`** (Temkin, T:2998–3005): if `T ∈ 𝒪`, `K` is separably closed and every
value of `v_L` is the value of an element of `K`, then for every polynomial `p` over `K` and every
`π ∈ K` with `p(T)/π ∈ 𝒪`, the residue of `p(T)/π` lies in the subfield generated over `K̃` by the
residues of the elements `(T - a)/π'`. Induction on the degree: reducible polynomials are handled
by their factors, separable irreducible ones are linear, and an inseparable irreducible `p` is
replaced by `p + ωT` with `|ω| < |π|` (same residue, separable, reducible). -/
theorem residue_mem_linearResidueField (hT : vL T ≤ 1)
    (hval : ∀ x : L, ∃ c : K, vL x = vL (algebraMap K L c)) :
    ∀ (n : ℕ) (p : K[X]), p.natDegree = n → ∀ (π : K) (s : vL.valuationSubring),
      (s : L) = aeval T p / algebraMap K L π →
        residue vL.valuationSubring s ∈ linearResidueField vK vL T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- preliminary: an element of value one written as `q(T)/π`
  have key : ∀ (q : K[X]) (π : K) (s : vL.valuationSubring),
      (s : L) = aeval T q / algebraMap K L π → vL (s : L) = 1 →
        aeval T q ≠ 0 ∧ π ≠ 0 ∧ vL (aeval T q) = vL (algebraMap K L π) := by
    intro q π s hs h1
    have hπ : π ≠ 0 := by
      rintro rfl
      rw [map_zero, div_zero] at hs
      rw [hs, map_zero] at h1
      exact zero_ne_one h1
    have hπL : algebraMap K L π ≠ 0 := (_root_.map_ne_zero _).mpr hπ
    have hq : aeval T q ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hs
      rw [hs, map_zero] at h1
      exact zero_ne_one h1
    refine ⟨hq, hπ, ?_⟩
    rw [hs, map_div₀] at h1
    exact (div_eq_one_iff_eq ((_root_.map_ne_zero vL).mpr hπL)).mp h1
  -- every `q(T)` has the value of an element of `K`, and `q(T)/π_q ∈ 𝒪`
  have hnorm : ∀ q : K[X], aeval T q ≠ 0 → ∃ π' : K, π' ≠ 0 ∧ ∃ s' : vL.valuationSubring,
      (s' : L) = aeval T q / algebraMap K L π' ∧ vL (s' : L) = 1 := by
    intro q hq
    obtain ⟨π', hπ'⟩ := hval (aeval T q)
    have hπ'0 : π' ≠ 0 := by
      rintro rfl
      rw [map_zero, map_zero] at hπ'
      exact hq ((map_eq_zero vL).mp hπ')
    have hv : vL (aeval T q / algebraMap K L π') = 1 := by
      rw [map_div₀, hπ', div_self ((_root_.map_ne_zero vL).mpr ((_root_.map_ne_zero _).mpr hπ'0))]
    exact ⟨π', hπ'0, ⟨_, (Valuation.mem_valuationSubring_iff vL _).mpr hv.le⟩, rfl, hv⟩
  -- the reducible case, for any monic polynomial of degree `n`
  have hred : ∀ (q : K[X]), q.natDegree = n → ¬ Irreducible q → 0 < n →
      ∀ (π : K) (s : vL.valuationSubring), (s : L) = aeval T q / algebraMap K L π →
        vL (s : L) = 1 → residue vL.valuationSubring s ∈ linearResidueField vK vL T := by
    intro q hqn hirr hn π s hs h1
    obtain ⟨hq0, hπ, hvq⟩ := key q π s hs h1
    have hqne : q ≠ 0 := by rintro rfl; simp at hq0
    have hnu : ¬ IsUnit q := by
      intro hu
      have := natDegree_eq_zero_of_isUnit hu
      omega
    obtain ⟨q₁, q₂, rfl, hq₁, hq₂⟩ : ∃ q₁ q₂, q = q₁ * q₂ ∧ ¬ IsUnit q₁ ∧ ¬ IsUnit q₂ := by
      by_contra hcon
      push Not at hcon
      exact hirr ⟨hnu, fun a b hab ↦ by
        by_contra hab'
        push Not at hab'
        exact hab'.2 (hcon a b hab hab'.1)⟩
    have h₁0 : q₁ ≠ 0 := left_ne_zero_of_mul hqne
    have h₂0 : q₂ ≠ 0 := right_ne_zero_of_mul hqne
    have hdeg := natDegree_mul h₁0 h₂0
    have hd₁ : 0 < q₁.natDegree := by
      by_contra h
      exact hq₁ (isUnit_iff_degree_eq_zero.mpr (by
        rw [degree_eq_natDegree h₁0]; exact_mod_cast Nat.eq_zero_of_not_pos h))
    have hd₂ : 0 < q₂.natDegree := by
      by_contra h
      exact hq₂ (isUnit_iff_degree_eq_zero.mpr (by
        rw [degree_eq_natDegree h₂0]; exact_mod_cast Nat.eq_zero_of_not_pos h))
    rw [map_mul] at hq0
    obtain ⟨π₁, hπ₁, s₁, hs₁, h₁⟩ := hnorm q₁ (left_ne_zero_of_mul hq0)
    obtain ⟨π₂, hπ₂, s₂, hs₂, h₂⟩ := hnorm q₂ (right_ne_zero_of_mul hq0)
    have hm₁ := ih q₁.natDegree (by omega) q₁ rfl π₁ s₁ hs₁
    have hm₂ := ih q₂.natDegree (by omega) q₂ rfl π₂ s₂ hs₂
    -- the unit `π₁ π₂ / π` of `R`
    have hπL : algebraMap K L π ≠ 0 := (_root_.map_ne_zero _).mpr hπ
    have hπ₁L : algebraMap K L π₁ ≠ 0 := (_root_.map_ne_zero _).mpr hπ₁
    have hπ₂L : algebraMap K L π₂ ≠ 0 := (_root_.map_ne_zero _).mpr hπ₂
    have hcv : vL (algebraMap K L (π₁ * π₂ / π)) = 1 := by
      have e₁ : vL (aeval T q₁) = vL (algebraMap K L π₁) := by
        rw [hs₁, map_div₀] at h₁
        exact (div_eq_one_iff_eq ((_root_.map_ne_zero vL).mpr hπ₁L)).mp h₁
      have e₂ : vL (aeval T q₂) = vL (algebraMap K L π₂) := by
        rw [hs₂, map_div₀] at h₂
        exact (div_eq_one_iff_eq ((_root_.map_ne_zero vL).mpr hπ₂L)).mp h₂
      rw [map_div₀ (algebraMap K L), map_mul (algebraMap K L), map_div₀ vL, map_mul vL, ← e₁,
        ← e₂, ← map_mul vL, ← map_mul (aeval T), hvq, div_self ((_root_.map_ne_zero vL).mpr hπL)]
    have hc : vK (π₁ * π₂ / π) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff vK vL _).mp hcv.le
    let c : vL.valuationSubring := ⟨algebraMap K L (π₁ * π₂ / π),
      (Valuation.mem_valuationSubring_iff vL _).mpr hcv.le⟩
    have hsplit : s = c * s₁ * s₂ := by
      apply Subtype.ext
      simp only [c, MulMemClass.coe_mul, hs, hs₁, hs₂, map_mul, map_div₀]
      field_simp
    rw [hsplit, map_mul, map_mul]
    exact IntermediateField.mul_mem _ (IntermediateField.mul_mem _
      (residue_mem_linearResidueField_of_eq_algebraMap vK vL T hc rfl) hm₁) hm₂
  intro p hpn π s hs
  by_cases hs1 : vL (s : L) < 1
  · rw [residue_eq_zero_of_lt_one vL hs1]
    exact IntermediateField.zero_mem _
  have h1 : vL (s : L) = 1 :=
    le_antisymm ((Valuation.mem_valuationSubring_iff vL _).mp s.2) (not_lt.mp hs1)
  obtain ⟨hp0, hπ, hvp⟩ := key p π s hs h1
  have hpne : p ≠ 0 := by rintro rfl; simp at hp0
  have hπL : algebraMap K L π ≠ 0 := (_root_.map_ne_zero _).mpr hπ
  -- degree zero: `p(T)/π ∈ K`
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [eq_C_of_natDegree_eq_zero hpn, aeval_C] at hs
    have hv : vK (p.coeff 0 / π) ≤ 1 := by
      rw [← Valuation.HasExtension.val_map_le_one_iff vK vL, map_div₀, ← hs]
      exact h1.le
    exact residue_mem_linearResidueField_of_eq_algebraMap vK vL T hv (by rw [hs, map_div₀])
  -- reduce to a monic polynomial
  set c := p.leadingCoeff with hcdef
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  set p₁ := C c⁻¹ * p with hp₁
  have hp₁m : p₁.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc0)
  have hp₁n : p₁.natDegree = n := by rw [hp₁, natDegree_C_mul (inv_ne_zero hc0), hpn]
  have hs' : (s : L) = aeval T p₁ / algebraMap K L (π * c⁻¹) := by
    rw [hs, hp₁, map_mul, aeval_C, map_mul, map_inv₀]
    have : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
    field_simp
  clear_value c p₁
  by_cases hirr : Irreducible p₁
  · by_cases hsep : p₁.Separable
    · -- separable irreducible polynomials are linear
      have hdeg1 : p₁.natDegree = 1 := by
        have := IsSepClosed.degree_eq_one_of_irreducible K hirr hsep
        rw [degree_eq_natDegree hp₁m.ne_zero] at this
        exact_mod_cast this
      have hlin := hp₁m.eq_X_add_C hdeg1
      refine IntermediateField.subset_adjoin _ _ ⟨-p₁.coeff 0, π * c⁻¹, s, ?_, rfl⟩
      rw [hs']
      congr 1
      conv_lhs => rw [hlin]
      simp [sub_eq_add_neg]
    · -- inseparable: perturb by `ωT`
      have hder : derivative p₁ = 0 := by
        by_contra h
        exact hsep ((separable_iff_derivative_ne_zero hirr).mpr h)
      have hn2 : 2 ≤ n := by
        by_contra h
        have hn1 : p₁.natDegree = 1 := by omega
        exact hsep (by rw [hp₁m.eq_X_add_C hn1]; exact separable_X_add_C _)
      by_cases hnt : ∃ ω₀ : K, ω₀ ≠ 0 ∧ vK ω₀ < 1
      · obtain ⟨ω₀, hω₀, hvω₀⟩ := hnt
        set π' := π * c⁻¹ with hπ'
        have hπ'0 : π' ≠ 0 := mul_ne_zero hπ (inv_ne_zero hc0)
        set ω := ω₀ * π' with hω
        have hω0 : ω ≠ 0 := mul_ne_zero hω₀ hπ'0
        set q := p₁ + C ω * X with hq
        have hqn : q.natDegree = n := by
          rw [hq, natDegree_add_eq_left_of_natDegree_lt, hp₁n]
          rw [natDegree_C_mul_X ω hω0, hp₁n]
          omega
        have hqsep : q.Separable := by
          rw [separable_def, hq, derivative_add, hder, zero_add, derivative_C_mul_X]
          exact ⟨0, C ω⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hω0, C_1]⟩
        have hqirr : ¬ Irreducible q := by
          intro hqi
          have := IsSepClosed.degree_eq_one_of_irreducible K hqi hqsep
          have hq0 : q ≠ 0 := by
            intro h
            rw [h, natDegree_zero] at hqn
            omega
          rw [degree_eq_natDegree hq0, hqn] at this
          have : n = 1 := by exact_mod_cast this
          omega
        -- the values: `|ωT| < |π'| = |p₁(T)|`
        have hvp₁ : vL (aeval T p₁) = vL (algebraMap K L π') := by
          obtain ⟨-, -, h⟩ := key p₁ π' s hs' h1
          exact h
        have hvωT : vL (algebraMap K L ω * T) < vL (aeval T p₁) := by
          rw [hvp₁, map_mul]
          calc vL (algebraMap K L ω) * vL T ≤ vL (algebraMap K L ω) := mul_le_of_le_one_right' hT
            _ < vL (algebraMap K L π') := by
              rw [Valuation.HasExtension.val_map_lt_iff vK vL, hω, map_mul]
              exact mul_lt_of_lt_one_left ((Valuation.pos_iff vK).mpr hπ'0) hvω₀
        have haevq : aeval T q = aeval T p₁ + algebraMap K L ω * T := by
          simp [hq]
        have hvq : vL (aeval T q / algebraMap K L π') = 1 := by
          rw [map_div₀, haevq, Valuation.map_add_eq_of_lt_left vL hvωT, hvp₁,
            div_self ((_root_.map_ne_zero vL).mpr ((_root_.map_ne_zero _).mpr hπ'0))]
        let s' : vL.valuationSubring :=
          ⟨aeval T q / algebraMap K L π', (Valuation.mem_valuationSubring_iff vL _).mpr hvq.le⟩
        have hres : residue vL.valuationSubring s = residue vL.valuationSubring s' := by
          rw [← sub_eq_zero, ← map_sub]
          apply residue_eq_zero_of_lt_one
          have : ((s - s' : vL.valuationSubring) : L) =
              -(algebraMap K L ω * T / algebraMap K L π') := by
            simp only [AddSubgroupClass.coe_sub, s', hs', haevq]
            ring
          rw [this, Valuation.map_neg, map_div₀,
            div_lt_one₀ ((Valuation.pos_iff vL).mpr ((_root_.map_ne_zero _).mpr hπ'0)), ← hvp₁]
          exact hvωT
        rw [hres]
        exact hred q hqn hqirr hn π' s' rfl hvq
      · -- trivial valuation on `K`: all coefficients lie in `R`
        push Not at hnt
        have hall : ∀ x : K, vK x ≤ 1 := by
          intro x
          by_cases hx : x = 0
          · simp [hx]
          have h1 := hnt x⁻¹ (inv_ne_zero hx)
          rw [map_inv₀] at h1
          exact (one_le_inv₀ ((Valuation.pos_iff vK).mpr hx)).mp h1
        refine residue_aeval_mem_adjoin vK vL T hT (C (π * c⁻¹)⁻¹ * p₁) (fun i ↦ hall _) s ?_
        rw [hs', map_mul (aeval T), aeval_C, map_inv₀ (algebraMap K L), div_eq_inv_mul]
  · exact hred p₁ hp₁n hirr hn (π * c⁻¹) s hs' h1

/-- **`L̃ = K̃(residues of (T - a)/π)`** (Temkin, T:2998–3005; `lem:sm-lu-residue-generators`): let
`K` be separably closed, `L = K(T)` with `T ∈ 𝒪`, and `L̃/K̃` transcendental. Then `L̃` is generated
over `K̃` by the residues of the elements `(T - a)/π ∈ 𝒪`, `a, π ∈ K`. -/
theorem adjoin_linearResidues_eq_top (hgen : IntermediateField.adjoin K {T} = ⊤) (hT : vL T ≤ 1)
    {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t)) :
    linearResidueField vK vL T = ⊤ := by
  have hval := exists_valuation_eq_algebraMap vK vL (trdeg_le_one_of_adjoin_eq_top T hgen) ht
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨g, rfl⟩ := residue_surjective z
  by_cases hg1 : vL (g : L) < 1
  · rw [residue_eq_zero_of_lt_one vL hg1]
    exact IntermediateField.zero_mem _
  have hgv : vL (g : L) = 1 :=
    le_antisymm ((Valuation.mem_valuationSubring_iff vL _).mp g.2) (not_lt.mp hg1)
  have hgmem : (g : L) ∈ IntermediateField.adjoin K {T} := hgen ▸ IntermediateField.mem_top
  obtain ⟨r, q, hrq⟩ := (IntermediateField.mem_adjoin_simple_iff K (g : L)).mp hgmem
  have hq : aeval T q ≠ 0 := by
    intro h
    rw [h, div_zero] at hrq
    rw [hrq, map_zero] at hgv
    exact zero_ne_one hgv
  obtain ⟨π, hπ⟩ := hval (aeval T q)
  have hπ0 : algebraMap K L π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact hq ((map_eq_zero vL).mp hπ)
  have hvπ : vL (algebraMap K L π) ≠ 0 := (_root_.map_ne_zero vL).mpr hπ0
  have hvq : vL (aeval T q / algebraMap K L π) = 1 := by rw [map_div₀, hπ, div_self hvπ]
  have hvr : vL (aeval T r / algebraMap K L π) = 1 := by
    have e : aeval T r = (g : L) * aeval T q := by rw [hrq]; field_simp
    rw [map_div₀, e, map_mul, hgv, one_mul, hπ, div_self hvπ]
  let sq : vL.valuationSubring :=
    ⟨_, (Valuation.mem_valuationSubring_iff vL _).mpr hvq.le⟩
  let sr : vL.valuationSubring :=
    ⟨_, (Valuation.mem_valuationSubring_iff vL _).mpr hvr.le⟩
  have hprod : g * sq = sr := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, sq, sr, hrq]
    field_simp
  have hsq0 : residue vL.valuationSubring sq ≠ 0 :=
    residue_ne_zero_of_valuation_eq_one vL hvq
  have hres : residue vL.valuationSubring g =
      residue vL.valuationSubring sr / residue vL.valuationSubring sq := by
    rw [← hprod, map_mul, mul_div_cancel_right₀ _ hsq0]
  rw [hres]
  exact IntermediateField.div_mem _
    (residue_mem_linearResidueField vK vL T hT hval _ r rfl π sr rfl)
    (residue_mem_linearResidueField vK vL T hT hval _ q rfl π sq rfl)

/-- **A linear coordinate with transcendental residue** (Temkin, T:3005–3011): let `K` be separably
closed, `L = K(T)` with `T ∈ 𝒪`, `L̃/K̃` transcendental, and suppose that the residue of `T` is
algebraic over `K̃` (the centre on `𝔸¹_R` is a closed point of the closed fibre). Then there are
`a, π ∈ R` with `π ≠ 0`, `|π| < 1`, `|T - a| = |π|` and the residue of `(T - a)/π` transcendental
over `K̃`. -/
theorem exists_transcendental_residue_sub (hgen : IntermediateField.adjoin K {T} = ⊤)
    (hT : vL T ≤ 1) {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t))
    (halg : IsAlgebraic (ResidueField vK.valuationSubring)
      (residue vL.valuationSubring ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩)) :
    ∃ a π : K, vK a ≤ 1 ∧ π ≠ 0 ∧ vK π < 1 ∧
      vL (T - algebraMap K L a) = vL (algebraMap K L π) ∧
      ∃ s : vL.valuationSubring, (s : L) = (T - algebraMap K L a) / algebraMap K L π ∧
        Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring s) := by
  have htop := adjoin_linearResidues_eq_top vK vL T hgen hT ht
  -- some generator is transcendental
  obtain ⟨z, ⟨a, π, s, hs, rfl⟩, hz⟩ : ∃ z ∈ linearResidues K vL T,
      Transcendental (ResidueField vK.valuationSubring) z := by
    by_contra hcon
    push Not at hcon
    have : Algebra.IsAlgebraic (ResidueField vK.valuationSubring) (linearResidueField vK vL T) :=
      IntermediateField.isAlgebraic_adjoin fun x hx ↦ (Classical.not_not.mp (hcon x hx)).isIntegral
    have hta : IsAlgebraic (ResidueField vK.valuationSubring)
        (⟨residue vL.valuationSubring t, htop ▸ IntermediateField.mem_top⟩ :
          linearResidueField vK vL T) := Algebra.IsAlgebraic.isAlgebraic _
    exact ht ((isAlgebraic_algHom_iff (IntermediateField.val _) Subtype.val_injective).mpr hta)
  have hs1 : vL (s : L) = 1 := by
    by_contra h
    have hlt : vL (s : L) < 1 := lt_of_le_of_ne ((Valuation.mem_valuationSubring_iff vL _).mp s.2) h
    rw [residue_eq_zero_of_lt_one vL hlt] at hz
    exact hz isAlgebraic_zero
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [hs, map_zero, div_zero, map_zero] at hs1
    exact zero_ne_one hs1
  have hπL : algebraMap K L π ≠ 0 := (_root_.map_ne_zero _).mpr hπ
  have hvπ0 : vL (algebraMap K L π) ≠ 0 := (_root_.map_ne_zero vL).mpr hπL
  have hvTa : vL (T - algebraMap K L a) = vL (algebraMap K L π) := by
    rw [hs, map_div₀] at hs1
    exact (div_eq_one_iff_eq hvπ0).mp hs1
  -- a residue of the form `r̄ T̃ + r̄'` or `r̄'` with `r, r' ∈ R` is algebraic
  have halgT : IsIntegral (ResidueField vK.valuationSubring)
      (residue vL.valuationSubring ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩) :=
    halg.isIntegral
  -- `a ∈ R`
  have ha : vK a ≤ 1 := by
    by_contra ha
    push Not at ha
    have haL : 1 < vL (algebraMap K L a) :=
      lt_of_not_ge fun h ↦ (not_le.mpr ha) ((Valuation.HasExtension.val_map_le_one_iff vK vL a).mp h)
    have hTa : vL T < vL (algebraMap K L a) := hT.trans_lt haL
    have hva : vL (T - algebraMap K L a) = vL (algebraMap K L a) := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right vL (by rwa [Valuation.map_neg])]
      exact Valuation.map_neg vL _
    have hc : vK (-a / π) ≤ 1 := by
      rw [← Valuation.HasExtension.val_map_le_one_iff vK vL, map_div₀ (algebraMap K L), map_neg,
        map_div₀ vL, Valuation.map_neg, ← hvTa, hva, div_self (by rw [← hva, hvTa]; exact hvπ0)]
    let c : vL.valuationSubring := ⟨algebraMap K L (-a / π),
      (Valuation.mem_valuationSubring_iff vL _).mpr
        ((Valuation.HasExtension.val_map_le_one_iff vK vL _).mpr hc)⟩
    have hres : residue vL.valuationSubring s = residue vL.valuationSubring c := by
      rw [← sub_eq_zero, ← map_sub]
      apply residue_eq_zero_of_lt_one
      have : ((s - c : vL.valuationSubring) : L) = T / algebraMap K L π := by
        simp only [AddSubgroupClass.coe_sub, c, hs, map_div₀, map_neg]
        ring
      rw [this, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvπ0), ← hvTa, hva]
      exact hTa
    rw [hres, residue_eq_algebraMap vK vL hc rfl] at hz
    exact hz (isAlgebraic_algebraMap _)
  -- `|π| < 1`
  have hπ1 : vK π < 1 := by
    have hle : vL (algebraMap K L π) ≤ 1 := by
      rw [← hvTa]
      exact (Valuation.map_sub vL _ _).trans (max_le hT
        ((Valuation.HasExtension.val_map_le_one_iff vK vL a).mpr ha))
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (Valuation.HasExtension.val_map_lt_one_iff vK vL π).mp hlt
    exfalso
    have heqK : vK π = 1 := (Valuation.HasExtension.val_map_eq_one_iff vK vL π).mp heq
    have hc₁ : vK π⁻¹ ≤ 1 := by rw [map_inv₀, heqK, inv_one]
    have hc₂ : vK (a / π) ≤ 1 := by rw [map_div₀, heqK, div_one]; exact ha
    let c₁ : vL.valuationSubring := ⟨algebraMap K L π⁻¹, (Valuation.mem_valuationSubring_iff vL _).mpr
      ((Valuation.HasExtension.val_map_le_one_iff vK vL _).mpr hc₁)⟩
    let c₂ : vL.valuationSubring := ⟨algebraMap K L (a / π),
      (Valuation.mem_valuationSubring_iff vL _).mpr
        ((Valuation.HasExtension.val_map_le_one_iff vK vL _).mpr hc₂)⟩
    let tO : vL.valuationSubring := ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩
    have hsplit : s = c₁ * tO - c₂ := by
      apply Subtype.ext
      simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, c₁, c₂, tO, hs, map_div₀,
        map_inv₀]
      field_simp
    rw [hsplit, map_sub, map_mul, residue_eq_algebraMap vK vL (s := c₁) hc₁ rfl,
      residue_eq_algebraMap vK vL (s := c₂) hc₂ rfl] at hz
    exact hz ((isIntegral_algebraMap.mul halgT).sub isIntegral_algebraMap).isAlgebraic
  exact ⟨a, π, ha, hπ, hπ1, hvTa, s, hs, hz⟩

end Residues

end DeJongAlterations.StableModification.LocalUniformization
