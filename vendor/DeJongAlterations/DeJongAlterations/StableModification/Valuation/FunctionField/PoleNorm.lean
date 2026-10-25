import DeJongAlterations.StableModification.Valuation.FunctionField.Places
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.SeparablyGenerated

/-!
# The pole-order norm of a function field of one variable

Let `F/E` be a function field of one variable (`IsFunctionFieldOneVar E F`). For a place `O`
and `f ∈ F`, `PoleOrderLE O f n` says that `f` has a pole of order at most `n` at `O`, i.e.
`|x ^ n * f| ≤ 1` for all `x` in the maximal ideal, and `poleOrder O f` is the least such `n`.
The **pole-order norm** `poleNorm E f` is the least `n` bounding the pole orders at all places;
it is the maximal pole order of `f` (`exists_poleOrder_eq_poleNorm`).

This is the norm used by Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), proof of Lemma 6.2.6 (`semi-stable.tex`, lines 3771–3784: "let `‖f‖` be the maximal order
of poles of `f`"), here defined directly from the places instead of a proper normal model.

## Main results

* `poleOrderLE_pow_iff`, `poleOrder_pow`: at a place, `ord (f ^ k) = k * ord f`.
* `poleNorm_le_finrank`: `‖f‖ ≤ [F : E(f)]` for transcendental `f`.
* `poleNorm_add_le` (ultrametric), `poleNorm_smul` (`‖c f‖ = ‖f‖`, `c ≠ 0`), `poleNorm_pow`
  (`‖f ^ k‖ = k ‖f‖`), `poleNorm_eq_zero_iff` (`‖f‖ = 0 ↔ f` algebraic over `E`).
* `isAlgebraic_of_forall_exists_pow`, `forall_exists_pow_iff_mem_range`: `⋂ₙ F ^ (p ^ n) = E`.
* `finrank_frobenius_fieldRange`: the **`p`-degree** `[F : F ^ p] = p` over a perfect field of
  characteristic `p`.
* `IsFunctionFieldOneVar.exists_isSeparable`: a separating transcendental element exists over a
  perfect field.

The blueprint chapter is `blueprint/src/sm-val-funfield.tex` (plan node F2 of `PLAN-SM-VAL`).
-/

open scoped IntermediateField
open Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Valuation.FunctionField

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- `f` has a pole of order at most `n` at the valuation ring `O`: `|x ^ n * f| ≤ 1` for every `x`
with `|x| < 1`. -/
def PoleOrderLE (O : ValuationSubring F) (f : F) (n : ℕ) : Prop :=
  ∀ x : F, O.valuation x < 1 → O.valuation (x ^ n * f) ≤ 1

/-- The pole order of `f` at `O`: the least `n` with `PoleOrderLE O f n`. -/
def poleOrder (O : ValuationSubring F) (f : F) : ℕ :=
  sInf {n | PoleOrderLE O f n}

variable (E) in
/-- The **pole-order norm** of `f`: the least `n` such that `f` has a pole of order at most `n`
at every place of `F/E` (and `0` if there is none). For a function field of one variable it is
the maximal pole order, `exists_poleOrder_eq_poleNorm`. -/
def poleNorm (f : F) : ℕ :=
  sInf {n | ∀ O : ValuationSubring F, IsPlace E O → PoleOrderLE O f n}

variable {O : ValuationSubring F}

/-- A bound on the pole order can be enlarged. -/
theorem PoleOrderLE.mono {f : F} {m n : ℕ} (h : PoleOrderLE O f m) (hmn : m ≤ n) :
    PoleOrderLE O f n := by
  intro x hx
  have : x ^ n * f = x ^ (n - m) * (x ^ m * f) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  rw [this, map_mul]
  exact mul_le_one' (by rw [map_pow]; exact pow_le_one₀ zero_le hx.le) (h x hx)

/-- `f` has no pole at `O` if and only if `f ∈ O`. -/
theorem poleOrderLE_zero_iff {f : F} : PoleOrderLE O f 0 ↔ f ∈ O := by
  refine ⟨fun h => ?_, fun h x _ => ?_⟩
  · have := h 0 (by rw [map_zero]; exact zero_lt_one)
    rwa [pow_zero, one_mul, O.valuation_le_one_iff] at this
  · rw [pow_zero, one_mul, O.valuation_le_one_iff]; exact h

omit [Algebra E F] in
/-- The element `0` has no poles. -/
theorem poleOrderLE_zero_right (n : ℕ) : PoleOrderLE O 0 n := fun x _ => by simp

private theorem toNat_aux (a : ℤ) (k n : ℕ) : k * (-a).toNat ≤ n ↔ 0 ≤ (n : ℤ) + k * a := by
  rcases le_or_gt 0 a with ha | ha
  · rw [Int.toNat_of_nonpos (by omega), mul_zero]
    simp only [zero_le, true_iff]
    positivity
  · have h1 : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    rw [← Nat.cast_le (α := ℤ), Nat.cast_mul, h1]
    constructor <;> intro h <;> linarith

/-- **Local description of pole orders** at a place of a function field of one variable:
`f ^ k` has a pole of order at most `n` at `O` if and only if `k * poleOrder O f ≤ n`. -/
theorem poleOrderLE_pow_iff (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) (f : F)
    (k n : ℕ) : PoleOrderLE O (f ^ k) n ↔ k * poleOrder O f ≤ n := by
  obtain ⟨π, hπ0, hπ1, hmax, hval⟩ := hO.exists_uniformizer hF
  by_cases hf : f = 0
  · subst hf
    have h0 : poleOrder O (0 : F) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.sInf_le (poleOrderLE_zero_right 0))
    rw [h0, mul_zero]
    simp only [zero_le, iff_true]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · intro x hx
      rw [pow_zero, mul_one, map_pow]; exact pow_le_one₀ zero_le hx.le
    · rw [zero_pow hk.ne']; exact poleOrderLE_zero_right n
  obtain ⟨m, hm⟩ := hval f hf
  set σ := O.valuation π
  -- `PoleOrderLE O (f ^ k) n ↔ 0 ≤ n + k * m`
  have key : ∀ k n : ℕ, PoleOrderLE O (f ^ k) n ↔ 0 ≤ (n : ℤ) + k * m := by
    intro k n
    have hcalc : ∀ x : F, O.valuation (x ^ n * f ^ k) = O.valuation x ^ n * σ ^ ((k : ℤ) * m) := by
      intro x
      rw [map_mul, map_pow, map_pow, hm, ← zpow_natCast (σ ^ m) k, ← zpow_mul, mul_comm m]
    constructor
    · intro h
      have := h π hπ1
      rw [hcalc, ← zpow_natCast, ← zpow_add₀ hπ0.ne'] at this
      exact (zpow_le_one_iff_right_of_lt_one₀ hπ0 hπ1).mp this
    · intro h x hx
      rw [hcalc]
      calc O.valuation x ^ n * σ ^ ((k : ℤ) * m) ≤ σ ^ n * σ ^ ((k : ℤ) * m) := by
            gcongr <;> first | exact zero_le | exact hmax x hx
        _ = σ ^ ((n : ℤ) + k * m) := by rw [← zpow_natCast, ← zpow_add₀ hπ0.ne']
        _ ≤ 1 := (zpow_le_one_iff_right_of_lt_one₀ hπ0 hπ1).mpr h
  have hord : poleOrder O f = (-m).toNat := by
    have hmem : PoleOrderLE O f (-m).toNat := by
      rw [← pow_one f, key, Nat.cast_one, one_mul]
      have := Int.self_le_toNat (-m); omega
    refine le_antisymm (Nat.sInf_le hmem) ?_
    have hspec : PoleOrderLE O f (poleOrder O f) :=
      Nat.sInf_mem (s := {n | PoleOrderLE O f n}) ⟨_, hmem⟩
    have h' := (key 1 (poleOrder O f)).mp (by rwa [pow_one])
    rw [Nat.cast_one, one_mul] at h'
    omega
  rw [key, hord, toNat_aux]

/-- At a place of a function field of one variable, `PoleOrderLE O f n ↔ ord_O f ≤ n`. -/
theorem poleOrderLE_iff (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) {f : F} {n : ℕ} :
    PoleOrderLE O f n ↔ poleOrder O f ≤ n := by
  simpa using poleOrderLE_pow_iff hF hO f 1 n

/-- Pole orders are multiplicative: `ord_O (f ^ k) = k * ord_O f`. -/
theorem poleOrder_pow (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) (f : F) (k : ℕ) :
    poleOrder O (f ^ k) = k * poleOrder O f := by
  have h : ∀ n, poleOrder O (f ^ k) ≤ n ↔ k * poleOrder O f ≤ n := fun n => by
    rw [← poleOrderLE_iff hF hO, poleOrderLE_pow_iff hF hO]
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

/-- The pole order vanishes exactly on the elements of the place. -/
theorem poleOrder_eq_zero_iff (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) {f : F} :
    poleOrder O f = 0 ↔ f ∈ O := by
  rw [← poleOrderLE_zero_iff, poleOrderLE_iff hF hO, Nat.le_zero]

/-- `E(f⁻¹) = E(f)`. -/
theorem adjoin_inv_eq (f : F) : E⟮f⁻¹⟯ = E⟮f⟯ :=
  le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self E f)))
    (IntermediateField.adjoin_simple_le_iff.mpr (by
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self E f⁻¹)))

/-- Every element has bounded poles: for transcendental `f` the bound is `[F : E(f)]`. -/
theorem forall_poleOrderLE_finrank (hF : IsFunctionFieldOneVar E F) {f : F}
    (hf : Transcendental E f) :
    ∀ O, IsPlace E O → PoleOrderLE O f (Module.finrank E⟮f⟯ F) := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hs : Transcendental E f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  have := hF.finiteDimensional_adjoin hs
  intro O hO x hx
  by_cases hfO : O.valuation f ≤ 1
  · rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le hx.le) hfO
  push Not at hfO
  have hslt : O.valuation f⁻¹ < 1 := (O.valuation.one_lt_val_iff hf0).mp hfO
  have hb := pow_finrank_le hO.algebraMap_mem (inv_ne_zero hf0) hslt hx
  rw [adjoin_inv_eq] at hb
  rw [map_mul, map_pow]
  calc O.valuation x ^ Module.finrank E⟮f⟯ F * O.valuation f
      ≤ O.valuation f⁻¹ * O.valuation f := by gcongr
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hf0, map_one]

/-- The pole orders of an element are bounded over all places. -/
theorem exists_forall_poleOrderLE (hF : IsFunctionFieldOneVar E F) (f : F) :
    ∃ n, ∀ O, IsPlace E O → PoleOrderLE O f n := by
  by_cases hf : IsAlgebraic E f
  · exact ⟨0, fun O hO => poleOrderLE_zero_iff.mpr (hO.mem_of_isAlgebraic hf)⟩
  · exact ⟨_, forall_poleOrderLE_finrank hF hf⟩

/-- `f` has a pole of order at most `‖f‖` at every place. -/
theorem poleNorm_spec (hF : IsFunctionFieldOneVar E F) (f : F) :
    ∀ O, IsPlace E O → PoleOrderLE O f (poleNorm E f) :=
  Nat.sInf_mem (s := {n | ∀ O : ValuationSubring F, IsPlace E O → PoleOrderLE O f n})
    (exists_forall_poleOrderLE hF f)

/-- `‖f‖ ≤ n` if and only if the pole order of `f` is at most `n` at every place. -/
theorem poleNorm_le_iff (hF : IsFunctionFieldOneVar E F) {f : F} {n : ℕ} :
    poleNorm E f ≤ n ↔ ∀ O, IsPlace E O → PoleOrderLE O f n :=
  ⟨fun h O hO => (poleNorm_spec hF f O hO).mono h, fun h => Nat.sInf_le h⟩

/-- `‖f‖ ≤ n` if and only if `ord_O f ≤ n` for every place `O`. -/
theorem poleNorm_le_iff' (hF : IsFunctionFieldOneVar E F) {f : F} {n : ℕ} :
    poleNorm E f ≤ n ↔ ∀ O, IsPlace E O → poleOrder O f ≤ n := by
  rw [poleNorm_le_iff hF]
  exact forall₂_congr fun O hO => poleOrderLE_iff hF hO

/-- Every pole order is at most the pole-order norm. -/
theorem poleOrder_le_poleNorm (hF : IsFunctionFieldOneVar E F) (hO : IsPlace E O) (f : F) :
    poleOrder O f ≤ poleNorm E f :=
  (poleNorm_le_iff' hF).mp le_rfl O hO

/-- The pole-order norm is the **maximal pole order**: it is attained at some place. -/
theorem exists_poleOrder_eq_poleNorm (hF : IsFunctionFieldOneVar E F) (f : F) :
    ∃ O, IsPlace E O ∧ poleOrder O f = poleNorm E f := by
  by_cases h0 : poleNorm E f = 0
  · obtain ⟨t, ht⟩ := hF.exists_transcendental
    obtain ⟨O, hO, -⟩ := exists_isPlace_notMem ht
    exact ⟨O, hO, by rw [h0]; exact Nat.le_zero.mp (h0 ▸ poleOrder_le_poleNorm hF hO f)⟩
  have : ¬ poleNorm E f ≤ poleNorm E f - 1 := by omega
  rw [poleNorm_le_iff' hF] at this
  push Not at this
  obtain ⟨O, hO, hlt⟩ := this
  exact ⟨O, hO, le_antisymm (poleOrder_le_poleNorm hF hO f) (by omega)⟩

/-- **Pole bound.** `‖f‖ ≤ [F : E(f)]` for transcendental `f`. -/
theorem poleNorm_le_finrank (hF : IsFunctionFieldOneVar E F) {f : F} (hf : Transcendental E f) :
    poleNorm E f ≤ Module.finrank E⟮f⟯ F :=
  Nat.sInf_le (forall_poleOrderLE_finrank hF hf)

/-- `‖0‖ = 0`. -/
theorem poleNorm_zero : poleNorm E (0 : F) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le fun _ _ => poleOrderLE_zero_right 0)

/-- The pole-order norm is **ultrametric**. -/
theorem poleNorm_add_le (hF : IsFunctionFieldOneVar E F) (f g : F) :
    poleNorm E (f + g) ≤ max (poleNorm E f) (poleNorm E g) := by
  refine Nat.sInf_le fun O hO x hx => ?_
  have hf := (poleNorm_spec hF f O hO).mono (le_max_left _ (poleNorm E g)) x hx
  have hg := (poleNorm_spec hF g O hO).mono (le_max_right (poleNorm E f) _) x hx
  rw [mul_add]
  exact (Valuation.map_add _ _ _).trans (max_le hf hg)

/-- `‖c f‖ ≤ ‖f‖` for every constant `c`. -/
theorem poleNorm_smul_le (hF : IsFunctionFieldOneVar E F) (c : E) (f : F) :
    poleNorm E (c • f) ≤ poleNorm E f := by
  refine Nat.sInf_le fun O hO x hx => ?_
  rw [Algebra.smul_def, mul_left_comm, map_mul]
  exact mul_le_one' ((O.valuation_le_one_iff _).mpr (hO.algebraMap_mem c))
    (poleNorm_spec hF f O hO x hx)

/-- `‖c f‖ = ‖f‖` for every nonzero constant `c`. -/
theorem poleNorm_smul (hF : IsFunctionFieldOneVar E F) {c : E} (hc : c ≠ 0) (f : F) :
    poleNorm E (c • f) = poleNorm E f := by
  refine le_antisymm (poleNorm_smul_le hF c f) ?_
  have := poleNorm_smul_le hF c⁻¹ (c • f)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- `‖-f‖ = ‖f‖`. -/
theorem poleNorm_neg (hF : IsFunctionFieldOneVar E F) (f : F) : poleNorm E (-f) = poleNorm E f := by
  rw [← neg_one_smul E f, poleNorm_smul hF (neg_ne_zero.mpr one_ne_zero)]

/-- `‖f - g‖ ≤ max ‖f‖ ‖g‖`. -/
theorem poleNorm_sub_le (hF : IsFunctionFieldOneVar E F) (f g : F) :
    poleNorm E (f - g) ≤ max (poleNorm E f) (poleNorm E g) := by
  rw [sub_eq_add_neg, ← poleNorm_neg hF g]
  exact poleNorm_add_le hF f (-g)

/-- `‖f ^ k‖ = k * ‖f‖`. -/
theorem poleNorm_pow (hF : IsFunctionFieldOneVar E F) (f : F) (k : ℕ) :
    poleNorm E (f ^ k) = k * poleNorm E f := by
  obtain ⟨O₁, hO₁, h₁⟩ := exists_poleOrder_eq_poleNorm hF f
  refine le_antisymm ((poleNorm_le_iff' hF).mpr fun O hO => ?_) ?_
  · rw [poleOrder_pow hF hO]
    exact Nat.mul_le_mul_left k (poleOrder_le_poleNorm hF hO f)
  · rw [← h₁, ← poleOrder_pow hF hO₁]
    exact poleOrder_le_poleNorm hF hO₁ _

/-- `‖f‖ = 0` if and only if `f` is algebraic over `E`. -/
theorem poleNorm_eq_zero_iff (hF : IsFunctionFieldOneVar E F) {f : F} :
    poleNorm E f = 0 ↔ IsAlgebraic E f := by
  rw [← Nat.le_zero, poleNorm_le_iff hF, ← forall_isPlace_mem_iff]
  exact forall₂_congr fun O _ => poleOrderLE_zero_iff

/-- If `E` is algebraically closed in `F`, then `‖f‖ = 0` if and only if `f ∈ E`. -/
theorem poleNorm_eq_zero_iff_mem_range (hF : IsFunctionFieldOneVar E F)
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) {f : F} :
    poleNorm E f = 0 ↔ f ∈ (algebraMap E F).range := by
  rw [poleNorm_eq_zero_iff hF]
  refine ⟨halg f, ?_⟩
  rintro ⟨c, rfl⟩
  exact isAlgebraic_algebraMap c


section PDegree

/-- **Perfect-power closure.** An element which is a `p ^ n`-th power for every `n` (some
`p > 1`) has no poles, hence is algebraic over `E`. -/
theorem isAlgebraic_of_forall_exists_pow (hF : IsFunctionFieldOneVar E F) {p : ℕ} (hp : 1 < p)
    {f : F} (h : ∀ n : ℕ, ∃ g : F, g ^ p ^ n = f) : IsAlgebraic E f := by
  rw [← poleNorm_eq_zero_iff hF]
  obtain ⟨g, hg⟩ := h (poleNorm E f)
  have h1 : poleNorm E f = p ^ poleNorm E f * poleNorm E g := by
    conv_lhs => rw [← hg]
    rw [poleNorm_pow hF]
  have h2 : poleNorm E f < p ^ poleNorm E f := Nat.lt_pow_self hp
  by_contra hne
  have h3 : poleNorm E g ≠ 0 := fun h0 => hne (by rw [h1, h0, mul_zero])
  have h4 : p ^ poleNorm E f ≤ p ^ poleNorm E f * poleNorm E g :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h3)
  omega

/-- Over a perfect field `E` of characteristic `p` algebraically closed in `F`, the elements
that are `p ^ n`-th powers for every `n` are exactly the constants: `⋂ₙ F ^ (p ^ n) = E`. -/
theorem forall_exists_pow_iff_mem_range (hF : IsFunctionFieldOneVar E F) (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectField E]
    (halg : ∀ x : F, IsAlgebraic E x → x ∈ (algebraMap E F).range) {f : F} :
    (∀ n : ℕ, ∃ g : F, g ^ p ^ n = f) ↔ f ∈ (algebraMap E F).range := by
  have : CharP E p := (algebraMap E F).charP (algebraMap E F).injective p
  have : ExpChar E p := ExpChar.prime Fact.out
  have : PerfectRing E p := PerfectField.toPerfectRing p
  refine ⟨fun h => halg f (isAlgebraic_of_forall_exists_pow hF (Fact.out : p.Prime).one_lt h),
    ?_⟩
  rintro ⟨c, rfl⟩ n
  refine ⟨algebraMap E F ((iterateFrobeniusEquiv E p n).symm c), ?_⟩
  rw [← map_pow]
  congr 1
  rw [← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]

/-- `[E(t) : E(t ^ p)] = p` for transcendental `t`: the rational function `X ^ p` has degree
`p`. -/
theorem relfinrank_adjoin_pow (p : ℕ) {t : F} (ht : Transcendental E t) :
    IntermediateField.relfinrank E⟮t ^ p⟯ E⟮t⟯ = p := by
  set σ := RatFunc.algEquivOfTranscendental t ht
  set ψ : RatFunc E →ₐ[E] F := (IntermediateField.val E⟮t⟯).comp σ.toAlgHom with hψ
  have hψX : ψ RatFunc.X = t := by
    simp [hψ, σ, RatFunc.algEquivOfTranscendental_X]
  have h1 : (E⟮(RatFunc.X : RatFunc E) ^ p⟯).map ψ = E⟮t ^ p⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow, hψX]
  have h2 : (⊤ : IntermediateField E (RatFunc E)).map ψ = E⟮t⟯ := by
    rw [← RatFunc.adjoin_X, IntermediateField.adjoin_map, Set.image_singleton, hψX]
  rw [← h1, ← h2, IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right,
    RatFunc.finrank_eq_max_natDegree]
  have hXp : (RatFunc.X : RatFunc E) ^ p = algebraMap E[X] (RatFunc E) (X ^ p) := by
    rw [map_pow, RatFunc.algebraMap_X]
  rw [hXp, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_X_pow, natDegree_one,
    max_eq_left (Nat.zero_le _)]

/-- The Frobenius image of `E(t)` is `E(t ^ p)` when `E` is perfect. -/
theorem map_frobenius_adjoin (p : ℕ) [ExpChar F p] [ExpChar E p] [PerfectRing E p] (t : F) :
    (E⟮t⟯.toSubfield).map (frobenius F p) = (E⟮t ^ p⟯).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield,
    RingHom.map_field_closure, Set.image_union, Set.image_singleton]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_range, frobenius_def]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c ^ p, by rw [map_pow]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨algebraMap E F ((frobeniusEquiv E p).symm c), ⟨_, rfl⟩, ?_⟩
    rw [← map_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p (R := E) p c

/-- **`p`-degree.** For a function field of one variable over a perfect field of characteristic
`p`, `[F : F ^ p] = p`. -/
theorem finrank_frobenius_fieldRange (hF : IsFunctionFieldOneVar E F) (p : ℕ) [Fact p.Prime]
    [CharP F p] [PerfectField E] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  have : CharP E p := (algebraMap E F).charP (algebraMap E F).injective p
  have : ExpChar E p := ExpChar.prime Fact.out
  have : PerfectRing E p := PerfectField.toPerfectRing p
  obtain ⟨t, ht⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin ht
  set φ := frobenius F p
  set Ks := (E⟮t⟯).toSubfield
  set Fp := φ.fieldRange
  set K's := Ks.map φ
  have hK' : K's = (E⟮t ^ p⟯).toSubfield := map_frobenius_adjoin p t
  -- `[F^p : K'] = [F : K]`
  have h1 : K's.relfinrank Fp = Ks.relfinrank ⊤ := by
    rw [show Fp = (⊤ : Subfield F).map φ from RingHom.fieldRange_eq_map φ]
    exact Subfield.relfinrank_map_map Ks ⊤ φ
  have hle1 : K's ≤ Fp := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hle2 : K's ≤ Ks := by
    rw [hK']
    intro x hx
    exact (IntermediateField.adjoin_simple_le_iff.mpr
        (pow_mem (IntermediateField.mem_adjoin_simple_self E t) p) : E⟮t ^ p⟯ ≤ E⟮t⟯) hx
  have e1 := Subfield.relfinrank_mul_finrank_top hle1
  have e2 := Subfield.relfinrank_mul_finrank_top hle2
  have hKp : K's.relfinrank Ks = p := by
    rw [hK']
    exact relfinrank_adjoin_pow p ht
  have hN : Ks.relfinrank ⊤ = Module.finrank E⟮t⟯ F := by
    have := IntermediateField.relfinrank_top_right E⟮t⟯
    rwa [IntermediateField.relfinrank, IntermediateField.top_toSubfield] at this
  have hNpos : 0 < Module.finrank E⟮t⟯ F := Module.finrank_pos
  rw [Subfield.relfinrank_top_right] at hN
  rw [h1, ← e2, hKp, Subfield.relfinrank_top_right, hN] at e1
  have := Nat.eq_of_mul_eq_mul_left hNpos (e1.trans (mul_comm _ _))
  exact this


/-- **Separating elements.** A function field of one variable over a perfect field has a
transcendental element `t` with `F/E(t)` finite and separable. -/
theorem IsFunctionFieldOneVar.exists_isSeparable [PerfectField E] (hF : IsFunctionFieldOneVar E F) :
    ∃ t : F, Transcendental E t ∧ FiniteDimensional E⟮t⟯ F ∧ Algebra.IsSeparable E⟮t⟯ F := by
  have := hF.essFiniteType
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField E F
  have hcard := hs.lift_cardinalMk_eq_trdeg
  rw [hF.trdeg_eq_one] at hcard
  have hs1 : s.card = 1 := by
    have : Cardinal.mk s = 1 := by simpa using hcard
    simpa using this
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hs1
  have ht : Transcendental E t := hs.1.transcendental ⟨t, Finset.mem_singleton_self t⟩
  rw [Finset.coe_singleton] at hsep
  exact ⟨t, ht, hF.finiteDimensional_adjoin ht, hsep⟩


end PDegree

end DeJongAlterations.StableModification.Valuation.FunctionField

end
