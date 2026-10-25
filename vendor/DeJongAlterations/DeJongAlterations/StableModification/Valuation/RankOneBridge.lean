import DeJongAlterations.StableModification.Valuation.FiniteHeight
import Mathlib.RingTheory.Valuation.RankOne

/-!
# Height one is rank one

A valuation `v` of a field `K` has *rank one* (Mathlib's `Valuation.RankOne`: it is nontrivial and
its value group embeds into `ℝ≥0` as an ordered group) if and only if its valuation ring has Krull
dimension (height) one. This is the bridge that lets a valued field of height one be treated as a
non-archimedean normed field, as Temkin does without comment (*Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), §2.1, `semi-stable.tex` lines 1893–1895: "we automatically
provide any valued field of height one with the `π`-adic topology"). Blueprint lemma
`lem:sm-val-height-one-rank-one` of `sm-val-basic-vb.tex`.

## Main results

* `krullDimLE_one_iff_forall_pow_le`: `dim O_v ≤ 1` if and only if for all `x ≠ 0` and `|y| < 1`
  some power `|y|ⁿ` is at most `|x|`.
* `mulArchimedean_valueGroup₀_iff_forall_pow_le`, `mulArchimedean_valueGroup₀_iff_krullDimLE_one`:
  the same condition is the archimedean property of the value group `ValueGroup₀ v`.
* `mulArchimedean_valueGroup_iff_krullDimLE_one`: for a valuation subring `O`, the value group
  `O.ValueGroup` is archimedean iff `dim O ≤ 1`.
* `nonempty_rankOne_iff_ringKrullDim_eq_one`: `v` has rank one iff `dim O_v = 1`
  (via Hölder's theorem, Mathlib's `Valuation.nonempty_rankOne_iff_mulArchimedean`).
* `rankOneOfRingKrullDimEqOne`, `rankOneOfHeightEqOne`: the rank-one structure on the valuation of
  a valuation subring of height one.
-/

noncomputable section

open IsLocalRing MonoidWithZeroHom

namespace DeJongAlterations.StableModification.Valuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Height at most one, ring-theoretically**: the valuation ring of `v` has Krull dimension at
most one if and only if for all `x ≠ 0` and all `y` with `v y < 1` some power `v y ^ n` is at most
`v x`. -/
theorem krullDimLE_one_iff_forall_pow_le (v : Valuation K Γ₀) :
    Ring.KrullDimLE 1 v.valuationSubring ↔
      ∀ x y : K, x ≠ 0 → v y < 1 → ∃ n : ℕ, v y ^ n ≤ v x := by
  set O := v.valuationSubring
  constructor
  · intro h x y hx hy
    by_cases hx1 : 1 ≤ v x
    · exact ⟨0, by simpa using hx1⟩
    push Not at hx1
    have hxO : x ∈ O := hx1.le
    have hyO : y ∈ O := hy.le
    have hrad : (⟨y, hyO⟩ : O) ∈ (Ideal.span {(⟨x, hxO⟩ : O)}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro J ⟨hJx, hJp⟩
      have hJne : J ≠ ⊥ := by
        intro hJ
        have : (⟨x, hxO⟩ : O) ∈ J := hJx (Ideal.mem_span_singleton_self _)
        rw [hJ, Ideal.mem_bot] at this
        exact hx (congrArg Subtype.val this)
      rw [IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJne)]
      exact (v.mem_maximalIdeal_iff).mpr hy
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
    refine ⟨n, ?_⟩
    have hval : y ^ n = (a : K) * x := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    rw [← map_pow, hval, map_mul]
    exact mul_le_of_le_one_left' a.2
  · intro h
    rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
    intro I hI hIp
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hx0' : (x : K) ≠ 0 := fun h0 ↦ hx0 (Subtype.ext h0)
    suffices hle : maximalIdeal O ≤ I by
      rw [le_antisymm (le_maximalIdeal hIp.ne_top) hle]
      exact maximalIdeal.isMaximal O
    intro y hy
    obtain ⟨n, hn⟩ := h x y hx0' ((v.mem_maximalIdeal_iff).mp hy)
    have hq : (y : K) ^ n * (x : K)⁻¹ ∈ O := by
      change v _ ≤ 1
      rw [map_mul, map_inv₀, ← div_eq_mul_inv, map_pow]
      exact div_le_one_of_le₀ hn zero_le
    have hyn : y ^ n = ⟨_, hq⟩ * x := by
      ext
      simp [hx0']
    have : y ^ n ∈ I := by
      rw [hyn]
      exact I.mul_mem_left _ hxI
    exact hIp.mem_of_pow_mem n this

/-- For a surjective valuation, the archimedean property of the value group is the condition of
`krullDimLE_one_iff_forall_pow_le`. -/
theorem mulArchimedean_iff_forall_pow_le_of_surjective (v : Valuation K Γ₀)
    (hv : Function.Surjective v) :
    MulArchimedean Γ₀ ↔ ∀ x y : K, x ≠ 0 → v y < 1 → ∃ n : ℕ, v y ^ n ≤ v x := by
  constructor
  · intro h x y hx hy
    by_cases hy0 : y = 0
    · exact ⟨1, by simp [hy0]⟩
    have hy1 : 1 < v y⁻¹ := by
      rw [map_inv₀]
      exact one_lt_inv₀ ((Valuation.pos_iff v).mpr hy0) |>.mpr hy
    obtain ⟨n, hn⟩ := h.arch (v x⁻¹) hy1
    refine ⟨n, ?_⟩
    rw [map_inv₀, map_inv₀, inv_pow] at hn
    exact (inv_le_inv₀ ((Valuation.pos_iff v).mpr hx)
      (pow_pos ((Valuation.pos_iff v).mpr hy0) n)).mp hn
  · intro h
    refine ⟨fun g {γ} hγ ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hv g
    obtain ⟨b, rfl⟩ := hv γ
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hγ
    by_cases ha0 : a = 0
    · exact ⟨0, by simp [ha0]⟩
    obtain ⟨n, hn⟩ := h a⁻¹ b⁻¹ (inv_ne_zero ha0) (by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hγ)
    refine ⟨n, ?_⟩
    rw [map_inv₀, map_inv₀, inv_pow] at hn
    exact (inv_le_inv₀ (pow_pos ((Valuation.pos_iff v).mpr hb0) n)
      ((Valuation.pos_iff v).mpr ha0)).mp hn

/-- The value group `ValueGroup₀ v` (the subgroup generated by the values of `v`) is archimedean if
and only if for all `x ≠ 0` and `v y < 1` some power `v y ^ n` is at most `v x`. -/
theorem mulArchimedean_valueGroup₀_iff_forall_pow_le (v : Valuation K Γ₀) :
    MulArchimedean (ValueGroup₀ (.ofClass v)) ↔
      ∀ x y : K, x ≠ 0 → v y < 1 → ∃ n : ℕ, v y ^ n ≤ v x := by
  rw [mulArchimedean_iff_forall_pow_le_of_surjective v.restrict
    (ValueGroup₀.restrict₀_surjective (.ofClass v))]
  simp only [← map_pow, Valuation.restrict_le_iff, Valuation.restrict_lt_one_iff]

/-- **Height one is rank one, archimedean form**: the value group of `v` is archimedean if and only
if the valuation ring of `v` has Krull dimension at most one. -/
theorem mulArchimedean_valueGroup₀_iff_krullDimLE_one (v : Valuation K Γ₀) :
    MulArchimedean (ValueGroup₀ (.ofClass v)) ↔ Ring.KrullDimLE 1 v.valuationSubring :=
  (mulArchimedean_valueGroup₀_iff_forall_pow_le v).trans
    (krullDimLE_one_iff_forall_pow_le v).symm

/-- The value group `O.ValueGroup` of a valuation subring is archimedean if and only if `O` has
Krull dimension at most one. -/
theorem mulArchimedean_valueGroup_iff_krullDimLE_one (O : ValuationSubring K) :
    MulArchimedean O.ValueGroup ↔ Ring.KrullDimLE 1 O := by
  rw [mulArchimedean_iff_forall_pow_le_of_surjective O.valuation O.valuation_surjective,
    ← krullDimLE_one_iff_forall_pow_le, O.valuationSubring_valuation]

/-- A valuation subring has Krull dimension at most zero if and only if it is the whole field. -/
theorem ringKrullDim_le_zero_iff (O : ValuationSubring K) : ringKrullDim O ≤ 0 ↔ O = ⊤ := by
  rw [← isField_iff_eq_top]
  constructor
  · intro h
    have : Ring.KrullDimLE 0 O := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    exact Ring.KrullDimLE.isField_of_isDomain
  · intro h
    rw [ringKrullDim_eq_zero_of_isField h]

/-- **Height one is rank one**: a valuation has rank one (Mathlib's `Valuation.RankOne`) if and only
if its valuation ring has Krull dimension one. -/
theorem nonempty_rankOne_iff_ringKrullDim_eq_one (v : Valuation K Γ₀) :
    Nonempty v.RankOne ↔ ringKrullDim v.valuationSubring = 1 := by
  have hO : ¬ringKrullDim v.valuationSubring ≤ 0 ↔ v.IsNontrivial := by
    rw [ringKrullDim_le_zero_iff, v.valuationSubring_eq_top_iff, not_not]
  have key : ringKrullDim v.valuationSubring = 1 ↔
      Ring.KrullDimLE 1 v.valuationSubring ∧ v.IsNontrivial := by
    rw [Ring.krullDimLE_iff, ← hO]
    constructor
    · intro h
      rw [h]
      exact ⟨le_rfl, by decide⟩
    · rintro ⟨h1, h0⟩
      push Not at h0
      induction h : ringKrullDim v.valuationSubring using WithBot.recBotCoe with
      | bot => rw [h] at h0; exact absurd h0 (not_lt.mpr bot_le)
      | coe e =>
        rw [h] at h0 h1
        induction e using ENat.recTopCoe with
        | top => exact absurd h1 (by decide)
        | coe m =>
          have h1' : m ≤ 1 := by exact_mod_cast h1
          have h0' : 0 < m := by exact_mod_cast h0
          have : m = 1 := by omega
          rw [this]
          rfl
  rw [key]
  constructor
  · rintro ⟨h⟩
    have harch := (Valuation.nonempty_rankOne_iff_mulArchimedean (v := v)).mp ⟨h⟩
    exact ⟨(mulArchimedean_valueGroup₀_iff_krullDimLE_one v).mp harch, inferInstance⟩
  · rintro ⟨h1, hnt⟩
    exact (Valuation.nonempty_rankOne_iff_mulArchimedean (v := v)).mpr
      ((mulArchimedean_valueGroup₀_iff_krullDimLE_one v).mpr h1)

/-- The rank-one structure on the valuation of a valuation subring of Krull dimension one. -/
@[instance_reducible]
def rankOneOfRingKrullDimEqOne (O : ValuationSubring K) (h : ringKrullDim O = 1) :
    O.valuation.RankOne :=
  ((nonempty_rankOne_iff_ringKrullDim_eq_one O.valuation).mpr
    (by rwa [O.valuationSubring_valuation])).some

/-- The rank-one structure on the valuation of a valuation subring of height one (for instance
the height-one coarsening of `exists_height_ofPrime_eq_one`). -/
@[instance_reducible]
def rankOneOfHeightEqOne (O : ValuationSubring K) [Finite (PrimeSpectrum O)]
    (h : height O = 1) : O.valuation.RankOne :=
  rankOneOfRingKrullDimEqOne O (by rw [ringKrullDim_eq_height, h]; rfl)

end DeJongAlterations.StableModification.Valuation
