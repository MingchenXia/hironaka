import Hironaka.Analytic.IdealProducts

set_option autoImplicit false

/-!
# A metered `ℚ`-divisor is locally `(1/q) log |G|²` up to a bounded remainder

Source: Copy-4, `sec:fixed-data` (the passage that reads a metered effective
`ℚ`-divisor as an analytic singularity) — `transcendental-nakamaye-copy4-20260911`.

`FirstPass/HolomorphicIdealSheaves.MeteredEffectiveQDivisor` records a divisor by
its weight `ψ_E`, whose local presentation is

  `ψ_E = ∑ᵢ aᵢ log |gᵢ|² + h`,  `aᵢ ∈ ℚ≥0`, `h` smooth,

whereas `FirstPass/GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType`
asks for `c ψ_𝔞 + O(1)` with a single positive rational `c` and a *coherent ideal*
`𝔞`.  Nothing related the two encodings; the frontier note
`tn-classical-frontier-20260924-run0048` lists this as the first blocking item of
Copy-4 Steps 4–5.

This module does the elementary half, which is entirely an identity between
logarithms.  Writing `aᵢ = pᵢ/q` over a common denominator,

  `∑ᵢ aᵢ log |gᵢ|² = (1/q) log |∏ᵢ gᵢ^{pᵢ}|²`,

*exactly* — not up to `O(1)`.  So locally the weight of a metered `ℚ`-divisor is
`(1/q)·ψ_{(G)} + O(1)` for the single holomorphic function `G = ∏ᵢ gᵢ^{pᵢ}`: an
analytic-singularity presentation by an **invertible** ideal.  On a compact
manifold the denominator can be made uniform (`exists_uniformDenominator`), which
supplies the single rational coefficient `c = 1/q` that
`HasAnalyticSingularitiesOfType` demands.

What is **not** here, and is the genuinely classical remaining input, is the
globalisation of the *ideal*: the locally defined `(G)` on overlapping charts must
be one global coherent ideal sheaf, which needs the quotient `G_j / G_l` to be an
invertible holomorphic germ, i.e. Riemann extension across `{G_l = 0}`.  That is
stated separately.

## Contents

* `singleLog f = log |f|²`, the weight of the one-element family `{f}`, with its
  full algebra: `singleLog_one`, `singleLog_mul`, `singleLog_pow`,
  `singleLog_prod`.  The convention `log 0 = ⊥` makes all of these exact.
* `coe_natCast_mul_eq_nsmul`: `(p : ℝ) • L = p • L` on `EReal` for `L ≠ ⊤`,
  including `p = 0`, `L = ⊥` (both sides are `0` there).
* `exists_commonDenominator`: a finite family of nonnegative rationals is
  `pᵢ/q` for one positive natural `q` and naturals `pᵢ`.
* `MeteredEffectiveQDivisor.exists_localSingleGenerator`: the local statement.
* `MeteredEffectiveQDivisor.exists_uniformDenominator`: the same with one `q`
  for the whole compact manifold.
-/

open Set Filter
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.MeteredDivisorSingleGenerator

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities

/-! ### The weight of a single holomorphic function -/

section SingleLog

variable {X : Type*}

/-- `log |f|²`, the weight of the one-element generator family `{f}`, with the
value `⊥` where `f` vanishes. -/
def singleLog (f : X → ℂ) (y : X) : EReal := generatorLog (fun _ : Fin 1 => f) y

theorem singleLog_eq_log (f : X → ℂ) (y : X) :
    singleLog f y = ENNReal.log (ENNReal.ofReal (‖f y‖ ^ 2)) := by
  simp [singleLog, generatorLog_eq_log_sum]

theorem singleLog_ne_top (f : X → ℂ) (y : X) : singleLog f y ≠ ⊤ :=
  generatorLog_ne_top _ _

@[simp] theorem singleLog_eq_bot_iff (f : X → ℂ) (y : X) :
    singleLog f y = ⊥ ↔ f y = 0 := by
  simp [singleLog]

@[simp] theorem singleLog_one (y : X) : singleLog (1 : X → ℂ) y = 0 := by
  simp [singleLog_eq_log]

/-- **The weight of a product is the sum of the weights**, exactly, including at
common zeros. -/
theorem singleLog_mul (f g : X → ℂ) (y : X) :
    singleLog (f * g) y = singleLog f y + singleLog g y := by
  rw [singleLog_eq_log, singleLog_eq_log, singleLog_eq_log]
  have h : ‖(f * g) y‖ ^ 2 = ‖f y‖ ^ 2 * ‖g y‖ ^ 2 := by
    simp only [Pi.mul_apply, norm_mul, mul_pow]
  rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.log_mul_add]

/-- **The weight of a power is the multiple of the weight.**  The multiple is the
`ℕ`-action on `EReal`, deliberately: `((p : ℝ) : EReal) * ·` would need a case
split at `⊥` for `p = 0`. -/
theorem singleLog_pow (f : X → ℂ) (p : ℕ) (y : X) :
    singleLog (f ^ p) y = p • singleLog f y := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hf : (f ^ (p + 1)) = f ^ p * f := by ring
      rw [hf, singleLog_mul, ih, succ_nsmul]

theorem singleLog_prod {N : ℕ} (F : Fin N → X → ℂ) (y : X) :
    singleLog (∏ i, F i) y = ∑ i, singleLog (F i) y := by
  classical
  induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, singleLog_mul, ih]

end SingleLog

/-! ### Real multiples versus `ℕ`-multiples on `EReal` -/

/-- On `EReal`, multiplying by a natural cast agrees with the `ℕ`-action.  At
`p = 0` both sides are `0` even at `⊥`, because `(0 : EReal) * ⊥ = 0`. -/
theorem coe_natCast_mul_eq_nsmul (p : ℕ) (L : EReal) :
    ((p : ℝ) : EReal) * L = p • L := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hcast : (((p + 1 : ℕ) : ℝ) : EReal) = ((p : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
        push_cast
        rfl
      rw [hcast, EReal.right_distrib_of_nonneg
          (EReal.coe_nonneg.mpr (by positivity)) (EReal.coe_nonneg.mpr zero_le_one),
        ih, succ_nsmul]
      simp

/-! ### A common denominator for finitely many nonnegative rationals -/

/-- For a rational, `a · den = num`. -/
theorem rat_mul_den (a : ℚ) : a * ((a.den : ℕ) : ℚ) = (a.num : ℚ) := by
  have hden : (((a.den : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast a.den_nz
  exact ((div_eq_iff hden).mp (Rat.num_div_den a)).symm

/-- Finitely many nonnegative rationals share a positive denominator. -/
theorem exists_commonDenominator {N : ℕ} (a : Fin N → ℚ) (ha : ∀ i, 0 ≤ a i) :
    ∃ (q : ℕ) (p : Fin N → ℕ), 0 < q ∧ ∀ i, (a i : ℝ) = (p i : ℝ) / (q : ℝ) := by
  classical
  set q : ℕ := ∏ j, (a j).den with hq
  have hqpos : 0 < q := Finset.prod_pos fun j _ => (a j).pos
  refine ⟨q, fun i => (a i).num.toNat * ∏ j ∈ Finset.univ.erase i, (a j).den, hqpos, ?_⟩
  intro i
  have hnum : (0 : ℤ) ≤ (a i).num := Rat.num_nonneg.mpr (ha i)
  have hsplit : ((q : ℕ) : ℚ)
      = ((a i).den : ℚ) * ∏ j ∈ Finset.univ.erase i, ((a j).den : ℚ) := by
    rw [hq]
    push_cast
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have key : a i * (q : ℚ)
      = ((a i).num.toNat : ℚ) * ∏ j ∈ Finset.univ.erase i, ((a j).den : ℚ) := by
    rw [hsplit, ← mul_assoc, rat_mul_den (a i)]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum).symm
  have hqQ : ((q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hrat : (a i)
      = ((((a i).num.toNat * ∏ j ∈ Finset.univ.erase i, (a j).den : ℕ) : ℚ)) / (q : ℚ) := by
    rw [eq_div_iff hqQ, key]
    push_cast
    ring
  have hreal := congrArg (fun r : ℚ => (r : ℝ)) hrat
  push_cast at hreal
  push_cast
  exact hreal

/-! ### Distributing a nonnegative real over a finite `EReal` sum -/

/-- A nonnegative *finite* factor distributes over a finite `EReal` sum, with no
hypothesis on the summands: the only failure mode of distributivity on `EReal`
is `∞ · (⊥ + ⊤)`, and a real coefficient excludes it. -/
theorem coe_mul_finsetSum {ι : Type*} {c : ℝ} (hc : 0 ≤ c) (s : Finset ι)
    (L : ι → EReal) :
    ((c : ℝ) : EReal) * (∑ i ∈ s, L i) = ∑ i ∈ s, ((c : ℝ) : EReal) * L i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc)
          (EReal.coe_ne_top c), ih]

/-! ### Simultaneous nonvanishing of finitely many generators -/

/-- `f` vanishes identically on no nonempty open subset of `U`.  This is the
nondegeneracy carried by each local generator of a metered `ℚ`-divisor. -/
def NowhereIdenticallyZeroOn {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (U : Set X) : Prop :=
  ∀ W : Set X, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, f y ≠ 0

/-- **Finitely many generators are simultaneously nonzero on a nonempty open
subset.**  Each zero set is closed in `U` with empty interior, so finitely many
of them cannot cover a nonempty open set; the proof shrinks the open set once per
index rather than invoking Baire. -/
theorem exists_open_forall_ne_zero {X : Type*} [TopologicalSpace X] {ι : Type*}
    (s : Finset ι) {f : ι → X → ℂ} {U : Set X} (hU : IsOpen U)
    (hcont : ∀ i ∈ s, ContinuousOn (f i) U)
    (hne : ∀ i ∈ s, NowhereIdenticallyZeroOn (f i) U)
    {W : Set X} (hWopen : IsOpen W) (hWU : W ⊆ U) (hWne : W.Nonempty) :
    ∃ V : Set X, IsOpen V ∧ V ⊆ W ∧ V.Nonempty ∧ ∀ i ∈ s, ∀ y ∈ V, f i y ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨W, hWopen, subset_rfl, hWne, by simp⟩
  | insert i s hi ih =>
      obtain ⟨V, hVopen, hVW, hVne, hVall⟩ :=
        ih (fun j hj => hcont j (Finset.mem_insert_of_mem hj))
          (fun j hj => hne j (Finset.mem_insert_of_mem hj))
      obtain ⟨y, hyV, hy⟩ :=
        hne i (Finset.mem_insert_self i s) V hVopen (hVW.trans hWU) hVne
      refine ⟨V ∩ (U ∩ f i ⁻¹' ({0} : Set ℂ)ᶜ),
        hVopen.inter ((hcont i (Finset.mem_insert_self i s)).isOpen_inter_preimage hU
          isOpen_compl_singleton),
        inter_subset_left.trans hVW,
        ⟨y, hyV, hVW.trans hWU hyV, hy⟩, ?_⟩
      intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hz.2.2
      · exact hVall j hj' z hz.1

/-! ### The local single-generator presentation -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A metered effective `ℚ`-divisor is locally `(1/q) log |G|²` plus the smooth
term of its presentation**, for a single holomorphic `G` that vanishes identically
on no nonempty open subset.  There is no error term beyond the smooth `h` already
in the presentation: the identity
`∑ᵢ (pᵢ/q) log|gᵢ|² = (1/q) log|∏ᵢ gᵢ^{pᵢ}|²` is exact, `⊥` included. -/
theorem exists_localSingleGenerator (E : MeteredEffectiveQDivisor n M) (x : M) :
    ∃ (U : Set M), IsOpen U ∧ x ∈ U ∧ ∃ (q : ℕ) (G : M → ℂ) (h : M → ℝ),
      0 < q ∧
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
      NowhereIdenticallyZeroOn G U ∧
      (∀ e : ComplexChart n M,
        ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
      ∀ y ∈ U, E.weight y
        = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog G y + (h y : EReal) := by
  classical
  obtain ⟨U, hUopen, hxU, N, a, g, h, hanonneg, hgdiff, hgne, hsmooth, hweight, -⟩ :=
    E.local_presentation x
  obtain ⟨q, p, hqpos, hpq⟩ := exists_commonDenominator a hanonneg
  refine ⟨U, hUopen, hxU, q, ∏ i, (g i) ^ (p i), h, hqpos, ?_, ?_, hsmooth, ?_⟩
  · exact MDifferentiableOn.prod fun i _ => (hgdiff i).pow (p i)
  · -- nonvanishing: shrink to where all the `g i` are nonzero
    intro W hWopen hWU hWne
    obtain ⟨V, -, hVW, ⟨y, hyV⟩, hVall⟩ :=
      exists_open_forall_ne_zero (Finset.univ : Finset (Fin N)) hUopen
        (fun i _ => (hgdiff i).continuousOn)
        (fun i _ => hgne i) hWopen hWU hWne
    refine ⟨y, hVW hyV, ?_⟩
    simp only [Finset.prod_apply, ne_eq, Finset.prod_eq_zero_iff, not_exists]
    rintro i ⟨-, hzero⟩
    exact pow_ne_zero _ (hVall i (Finset.mem_univ i) y hyV) hzero
  · intro y hyU
    rw [hweight y hyU]
    congr 1
    have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    have hstep : ∀ i : Fin N,
        ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y
          = ((1 / (q : ℝ) : ℝ) : EReal) * (p i • singleLog (g i) y) := by
      intro i
      rw [← coe_natCast_mul_eq_nsmul, ← mul_assoc, ← EReal.coe_mul, hpq i]
      congr 2
      field_simp
    calc (∑ i, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y)
        = ∑ i, ((1 / (q : ℝ) : ℝ) : EReal) * (p i • singleLog (g i) y) := by
          exact Finset.sum_congr rfl fun i _ => hstep i
      _ = ((1 / (q : ℝ) : ℝ) : EReal) * ∑ i, (p i • singleLog (g i) y) :=
          (coe_mul_finsetSum hq0 _ _).symm
      _ = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog (∏ i, (g i) ^ (p i)) y := by
          rw [singleLog_prod]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => (singleLog_pow (g i) (p i) y).symm)

/-- Raising a single generator to a positive power multiplies the coefficient, and
keeps it nondegenerate. -/
theorem nowhereIdenticallyZeroOn_pow {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    {U : Set X} (hf : NowhereIdenticallyZeroOn f U) (k : ℕ) :
    NowhereIdenticallyZeroOn (f ^ k) U := by
  intro W hWopen hWU hWne
  obtain ⟨y, hyW, hy⟩ := hf W hWopen hWU hWne
  exact ⟨y, hyW, pow_ne_zero k hy⟩

/-- **One denominator for the whole compact manifold.**  This is the single
positive rational coefficient `c = 1/q` that
`Hironaka.GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType` requires:
a finite subcover has finitely many local denominators, and replacing `G` by a
power clears their product. -/
theorem exists_uniformDenominator [CompactSpace M] (E : MeteredEffectiveQDivisor n M) :
    ∃ q : ℕ, 0 < q ∧ ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ (G : M → ℂ) (h : M → ℝ),
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
        NowhereIdenticallyZeroOn G U ∧
        (∀ e : ComplexChart n M,
          ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
        ∀ y ∈ U, E.weight y
          = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog G y + (h y : EReal) := by
  classical
  choose U hUopen hxU q G hloc hqpos hGdiff hGne hhsmooth hweight using
    fun x : M => exists_localSingleGenerator E x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hsne : ∀ x ∈ s, 0 < q x := fun x _ => hqpos x
  refine ⟨∏ x ∈ s, q x, Finset.prod_pos fun x hx => hsne x hx, ?_⟩
  intro z
  obtain ⟨x, hx, hzU⟩ := by
    simpa only [mem_iUnion, exists_prop] using hs (mem_univ z)
  set k : ℕ := ∏ w ∈ s.erase x, q w with hk
  have hkpos : 0 < k := Finset.prod_pos fun w hw => hqpos w
  have hQ : (∏ w ∈ s, q w) = q x * k := by
    rw [hk, Finset.mul_prod_erase _ _ hx]
  refine ⟨U x, hUopen x, hzU, (G x) ^ k, hloc x, (hGdiff x).pow k,
    nowhereIdenticallyZeroOn_pow (hGne x) k, hhsmooth x, ?_⟩
  intro y hy
  rw [hweight x y hy]
  congr 1
  rw [singleLog_pow, ← coe_natCast_mul_eq_nsmul, ← mul_assoc, ← EReal.coe_mul]
  congr 2
  rw [hQ]
  have hqx : ((q x : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (hqpos x).ne'
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  push_cast
  field_simp

/-! ### The denominator may be enlarged at will -/

/-- The local data `exists_uniformDenominator` produces, named so that it can be
enlarged and consumed separately. -/
def IsUniformSingleGeneratorPresentation (E : MeteredEffectiveQDivisor n M) (q : ℕ) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ (G : M → ℂ) (h : M → ℝ),
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
      NowhereIdenticallyZeroOn G U ∧
      (∀ e : ComplexChart n M,
        ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
      ∀ y ∈ U, E.weight y
        = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog G y + (h y : EReal)

/-- **Any positive multiple of a working denominator works.**  Replace the local
generator `G` by `G^m`.  This is what makes two metered divisors comparable: their
denominators `q`, `q'` are unrelated, but both `q` and `q'` divide `q q'`. -/
theorem isUniformSingleGeneratorPresentation_mul {E : MeteredEffectiveQDivisor n M}
    {q : ℕ} (hq : 0 < q) (hpres : IsUniformSingleGeneratorPresentation E q)
    {m : ℕ} (hm : 0 < m) :
    IsUniformSingleGeneratorPresentation E (m * q) := by
  intro x
  obtain ⟨U, hUopen, hxU, G, h, hGdiff, hGne, hhsmooth, hweight⟩ := hpres x
  refine ⟨U, hUopen, hxU, G ^ m, h, hGdiff.pow m,
    nowhereIdenticallyZeroOn_pow hGne m, hhsmooth, ?_⟩
  intro y hy
  rw [hweight y hy]
  congr 1
  rw [singleLog_pow, ← coe_natCast_mul_eq_nsmul, ← mul_assoc, ← EReal.coe_mul]
  congr 2
  have hqR : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hmR : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  field_simp

/-- **One denominator that also serves every multiple of itself.** -/
theorem exists_uniformDenominator_multiple [CompactSpace M]
    (E : MeteredEffectiveQDivisor n M) :
    ∃ q : ℕ, 0 < q ∧ ∀ m : ℕ, 0 < m →
      IsUniformSingleGeneratorPresentation E (m * q) := by
  obtain ⟨q, hq, hdata⟩ := exists_uniformDenominator E
  exact ⟨q, hq, fun m hm => isUniformSingleGeneratorPresentation_mul hq hdata hm⟩

end

end Hironaka.MeteredDivisorSingleGenerator
