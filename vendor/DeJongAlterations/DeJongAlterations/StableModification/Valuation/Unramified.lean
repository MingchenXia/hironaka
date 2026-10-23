import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Valuation.LocalSubring
import DeJongAlterations.StableModification.Valuation.Bounded

/-!
# Standard-unramified extensions of valued fields

Let `l/k` be a field extension, `B` a valuation subring of `l` and `A = B ∩ k`. Temkin calls a
finite extension `l/k` of valued fields *unramified* if `B` is a localization of an étale
`A`-algebra (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
§2.1, `semi-stable.tex` l. 1985–1997). Following decision OD2 of `PLAN-SM-VAL.md` (simplification
S8) we work with the explicit form produced by every proof of unramifiedness in the source
(Propositions 2.2.1, 2.2.2 and Theorem 2.1.8):

**Definition.** `x ∈ l` is a *standard-unramified generator* (`IsStdUnramifiedGenerator k B x`)
if `l = k(x)`, `x` is integral over `A` (equivalently, since `A` is integrally closed, the minimal
polynomial `f` of `x` over `k` has coefficients in `A`), and `f'(x)` is a unit of `B`. The
extension is *standard-unramified* (`IsStdUnramified k B`) if such an `x` exists.

## Main results

* `exists_isIntegral_mul_eq`, `isLocalization_integralClosure`: if `l/k` is algebraic, then `B`
  is the localization of the integral closure `Ā` of `A` in `l` at the prime `𝔪_B ∩ Ā` (the
  classical description of the valuation rings of `l` over `A`, used by Temkin in the proofs of
  2.2.1 and 2.1.8, l. 2115–2117, 2181–2183). The proof is the elementary "Gauss lemma"
  argument: if `∑ cᵢ yⁱ = 0` with `cᵢ ∈ A` and `j` is the largest index with `cⱼ` a unit, then
  `s = ∑_{i ≥ j} cᵢ y^{i-j}` and `y s` are integral over `A` and `s` is a unit of `B`.
* `IsStdUnramifiedGenerator.mul_aeval_derivative_mem`: the dual basis bound
  `f'(x) · Ā ⊆ A[x]` (Mathlib's `traceForm_dualSubmodule_adjoin`).
* `IsStdUnramifiedGenerator.stdEtalePair`, `IsStdUnramifiedGenerator.toValuationSubring`: the
  standard étale `A`-algebra `A[X]_{f'}/(f)` and its map to `B` sending `X ↦ x`, which is
  injective (`toValuationSubring_injective`).
* `IsStdUnramifiedGenerator.isLocalization`: `B` is the localization of `A[X]_{f'}/(f)` at the
  prime ideal `𝔪_B ∩ A[X]_{f'}/(f)` (plan node V6(a); Temkin l. 2132–2139). Together with the
  finiteness of the spectrum over a base of finite height this gives Temkin's Lemma 2.1.6, see
  `UnramifiedEtale.lean`.
* `isStdUnramified_top`: a finite separable extension is standard-unramified for the trivial
  valuation.
* `eq_of_comap_eq_of_valuation_lt_one_iff`, `exists_valuationSubring_of_isMaximal`: the valuation
  rings of `l` over a valuation ring `A` of `k` correspond to the maximal ideals of `Ā` (each is
  determined by its centre on `Ā`, and every maximal ideal is a centre);
  `isIntegral_of_forall_comap_eq`: if `B` is the only valuation ring of `l` over `A`, then `B`
  is integral over `A`.
* `isStdUnramifiedGenerator_of_residue`, `isStdUnramified_of_residue`,
  `IsStdUnramifiedGenerator.map_minpoly_eq`, `IsStdUnramifiedGenerator.finrank_residueField_eq`,
  `IsStdUnramifiedGenerator.isSeparable_residueField`: Temkin's Lemma 2.1.5(ii) (l. 2009–2033)
  for an extension in which `B` is integral over `A` (equivalently `Ā` is local, i.e. `B` is the
  only valuation ring of `l` over `A`, which is Temkin's definition of a henselian valued field,
  l. 1921–1927, applied to `l`): `l/k` is standard-unramified at `B` iff `[κ(B) : κ(A)] = [l : k]`
  and `κ(B)/κ(A)` is separable; moreover any `y ∈ B` integral over `A` whose residue generates
  `κ(B)/κ(A)` is then a generator.
-/

noncomputable section

open IsLocalRing Polynomial

namespace DeJongAlterations.StableModification.Valuation

variable {k l : Type*} [Field k] [Field l] [Algebra k l] (B : ValuationSubring l)

section IntegralClosure

/-- An element of `l` that is integral over `B ∩ k` lies in `B`. -/
theorem mem_of_isIntegral_comap {w : l} (hw : IsIntegral (B.comap (algebraMap k l)) w) :
    w ∈ B := by
  have : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  rw [← hy]
  exact y.2

/-- An element of `l` lying in every valuation subring of `l` that contains the image of
`B ∩ k` is integral over `B ∩ k`. -/
theorem isIntegral_of_forall_valuationSubring {w : l}
    (hw : ∀ V : ValuationSubring l,
      (∀ a : B.comap (algebraMap k l), algebraMap k l a ∈ V) → w ∈ V) :
    IsIntegral (B.comap (algebraMap k l)) w := by
  by_contra hw'
  have hR : w ∉ (integralClosure (B.comap (algebraMap k l)) l).toSubring := hw'
  obtain ⟨V, hV, hwV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hR
  exact hwV (hw V fun a ↦ hV (isIntegral_algebraMap (R := B.comap (algebraMap k l)) (x := a)))

/-- If all coefficients of the minimal polynomial of `y` over `k` lie in `B`, then `y` is integral
over `B ∩ k`. -/
theorem isIntegral_comap_of_coeff_mem {y : l} (hy : IsIntegral k y)
    (h : ∀ i, algebraMap k l ((minpoly k y).coeff i) ∈ B) :
    IsIntegral (B.comap (algebraMap k l)) y := by
  set T := B.comap (algebraMap k l)
  have hcoeffs : ((minpoly k y).coeffs : Set k) ⊆ T.toSubring := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact h n
  refine ⟨(minpoly k y).toSubring T.toSubring hcoeffs,
    (monic_toSubring _ _ _).mpr (minpoly.monic hy), ?_⟩
  have := minpoly.aeval k y
  rw [← map_toSubring (minpoly k y) T.toSubring hcoeffs, aeval_def, eval₂_map] at this
  exact this

/-- The partial sums `∑_{j ≤ i ≤ m} cᵢ y^{i-j}` of a polynomial relation. -/
def upperSum (c : ℕ → l) (y : l) (m j : ℕ) : l :=
  ∑ i ∈ Finset.Ico j (m + 1), c i * y ^ (i - j)

theorem pow_mul_upperSum (c : ℕ → l) (y : l) (m j : ℕ) :
    y ^ j * upperSum c y m j = ∑ i ∈ Finset.Ico j (m + 1), c i * y ^ i := by
  rw [upperSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_Ico] at hi
  rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' hi.1]

theorem upperSum_eq_neg (c : ℕ → l) {y : l} (hy : y ≠ 0) {m j : ℕ} (hj : j ≤ m + 1)
    (hrel : ∑ i ∈ Finset.range (m + 1), c i * y ^ i = 0) :
    upperSum c y m j = -∑ i ∈ Finset.range j, c i * y⁻¹ ^ (j - i) := by
  have h := Finset.sum_range_add_sum_Ico (fun i ↦ c i * y ^ i) hj
  rw [hrel, ← pow_mul_upperSum] at h
  have hyj : y ^ j ≠ 0 := pow_ne_zero _ hy
  have : upperSum c y m j = -(y ^ j)⁻¹ * ∑ i ∈ Finset.range j, c i * y ^ i := by
    field_simp
    linear_combination h
  rw [this, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [inv_pow]
  have hi' : y ^ j = y ^ (j - i) * y ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi.le]
  rw [hi']
  have : y ^ i ≠ 0 := pow_ne_zero _ hy
  field_simp

theorem valuation_mul_lt_one (V : ValuationSubring l) {a b : l} (ha : V.valuation a ≤ 1)
    (hb : V.valuation b < 1) : V.valuation (a * b) < 1 := by
  rw [map_mul]
  calc V.valuation a * V.valuation b ≤ 1 * V.valuation b := mul_le_mul_left ha _
    _ < 1 := by rwa [one_mul]

theorem upperSum_mem (V : ValuationSubring l) (c : ℕ → l) (hc : ∀ i, c i ∈ V) {y : l}
    {m j : ℕ} (hj : j ≤ m + 1) (hrel : ∑ i ∈ Finset.range (m + 1), c i * y ^ i = 0) :
    upperSum c y m j ∈ V := by
  rcases eq_or_ne y 0 with rfl | hy
  · -- only the term `i = j` survives
    rw [upperSum]
    refine sum_mem fun i _ ↦ mul_mem (hc i) ?_
    rcases Nat.eq_zero_or_pos (i - j) with h | h
    · rw [h, pow_zero]; exact V.one_mem
    · rw [zero_pow h.ne']; exact V.zero_mem
  rcases V.mem_or_inv_mem y with hyV | hyV
  · exact sum_mem fun i _ ↦ mul_mem (hc i) (pow_mem hyV _)
  · rw [upperSum_eq_neg c hy hj hrel]
    exact neg_mem (sum_mem fun i _ ↦ mul_mem (hc i) (pow_mem hyV _))

theorem upperSum_succ (c : ℕ → l) (y : l) {m j : ℕ} (hj : j ≤ m) :
    upperSum c y m j = c j + y * upperSum c y m (j + 1) := by
  rw [upperSum, upperSum, Finset.mul_sum, Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.sub_self,
    pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_Ico] at hi
  rw [mul_left_comm, ← pow_succ']
  congr 2
  omega

/-- A nonzero element `y` of `B`, algebraic over `k`, satisfies a relation `∑ cᵢ yⁱ = 0` with all
`cᵢ` in `B ∩ k` and some `cᵢ` a unit of `B ∩ k`. -/
theorem exists_relation_of_isAlgebraic {y : l} (hy : IsAlgebraic k y) :
    ∃ (m : ℕ) (c : ℕ → k), (∀ i, algebraMap k l (c i) ∈ B) ∧
      (∃ i ≤ m, B.valuation (algebraMap k l (c i)) = 1) ∧
      ∑ i ∈ Finset.range (m + 1), algebraMap k l (c i) * y ^ i = 0 := by
  obtain ⟨p, hp0, hpy⟩ := hy
  set m := p.natDegree
  obtain ⟨i₀, hi₀, hmax⟩ := (Finset.range (m + 1)).exists_max_image
    (fun i ↦ B.valuation (algebraMap k l (p.coeff i))) ⟨m, Finset.self_mem_range_succ m⟩
  have hc0 : p.coeff i₀ ≠ 0 := by
    intro h0
    apply hp0
    ext i
    rw [coeff_zero]
    by_cases hi : i ≤ m
    · have := hmax i (Finset.mem_range_succ_iff.mpr hi)
      rw [h0, map_zero, map_zero] at this
      simpa using this
    · exact coeff_eq_zero_of_natDegree_lt (not_le.mp hi)
  have hv0 : B.valuation (algebraMap k l (p.coeff i₀)) ≠ 0 := by
    simpa using hc0
  refine ⟨m, fun i ↦ p.coeff i / p.coeff i₀, fun i ↦ ?_, ⟨i₀, Finset.mem_range_succ_iff.mp hi₀,
    by simp [div_self hc0]⟩, ?_⟩
  · rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_div₀]
    by_cases hi : i ≤ m
    · exact div_le_one_of_le₀ (hmax i (Finset.mem_range_succ_iff.mpr hi)) zero_le
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
      simp
  · rw [aeval_eq_sum_range] at hpy
    have : ∑ i ∈ Finset.range (m + 1), algebraMap k l (p.coeff i / p.coeff i₀) * y ^ i =
        (algebraMap k l (p.coeff i₀))⁻¹ * ∑ i ∈ Finset.range (m + 1), p.coeff i • y ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_div₀, Algebra.smul_def]
      ring
    rw [this, hpy, mul_zero]

/-- **Valuation rings over `A` are localizations of the integral closure** (key step): if `l/k`
is algebraic, every `y ∈ B` can be written `y = t / s` with `s, t ∈ l` integral over `A = B ∩ k`
and `s` a unit of `B`. -/
theorem exists_isIntegral_mul_eq [Algebra.IsAlgebraic k l] {y : l} (hy : y ∈ B) :
    ∃ s t : l, IsIntegral (B.comap (algebraMap k l)) s ∧
      IsIntegral (B.comap (algebraMap k l)) t ∧ B.valuation s = 1 ∧ y * s = t := by
  classical
  obtain ⟨m, c, hcB, ⟨i₀, hi₀m, hi₀⟩, hrel⟩ :=
    exists_relation_of_isAlgebraic B (Algebra.IsAlgebraic.isAlgebraic (R := k) y)
  set c' : ℕ → l := fun i ↦ algebraMap k l (c i)
  -- `j` is the largest index `≤ m` such that `cⱼ` is a unit
  set P : ℕ → Prop := fun i ↦ B.valuation (c' i) = 1
  set j := Nat.findGreatest P m
  have hjP : P j := Nat.findGreatest_spec hi₀m hi₀
  have hjm : j ≤ m := Nat.findGreatest_le m
  have hgt : ∀ i, j < i → i ≤ m → B.valuation (c' i) < 1 := fun i h1 h2 ↦
    lt_of_le_of_ne ((B.valuation_le_one_iff _).mpr (hcB i))
      (Nat.findGreatest_is_greatest h1 h2)
  -- the integrality criterion
  have hint : ∀ j' ≤ m + 1, IsIntegral (B.comap (algebraMap k l)) (upperSum c' y m j') := by
    intro j' hj'
    refine isIntegral_of_forall_valuationSubring B fun V hV ↦ ?_
    refine upperSum_mem V c' (fun i ↦ ?_) hj' hrel
    have hci : c i ∈ B.comap (algebraMap k l) := hcB i
    exact hV ⟨c i, hci⟩
  -- `s = upperSum j` is a unit of `B`
  have hs : B.valuation (upperSum c' y m j) = 1 := by
    rw [upperSum_succ c' y hjm]
    rw [Valuation.map_add_eq_of_lt_left]
    · exact hjP
    · rw [hjP]
      refine valuation_mul_lt_one B ((B.valuation_le_one_iff _).mpr hy) ?_
      rcases eq_or_lt_of_le hjm with hjm' | hjm'
      · rw [upperSum, hjm', Finset.Ico_self, Finset.sum_empty, map_zero]
        exact zero_lt_one
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
      rw [Finset.mem_Ico] at hi
      rw [mul_comm]
      exact valuation_mul_lt_one B ((B.valuation_le_one_iff _).mpr (pow_mem hy _))
        (hgt i (by omega) (by omega))
  -- `j ≥ 1`, because `upperSum 0 = 0`
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0] at hs
    have : upperSum c' y m 0 = 0 := by
      rw [← one_mul (upperSum c' y m 0), ← pow_zero y, pow_mul_upperSum,
        ← Finset.range_eq_Ico]
      exact hrel
    rw [this, map_zero] at hs
    exact zero_ne_one hs
  obtain ⟨j₁, hj₁⟩ := Nat.exists_eq_add_one_of_ne_zero hj0
  refine ⟨upperSum c' y m j, upperSum c' y m j₁ - c' j₁, hint j (by omega), ?_, hs, ?_⟩
  · refine (hint j₁ (by omega)).sub ?_
    exact isIntegral_algebraMap (R := B.comap (algebraMap k l)) (x := ⟨c j₁, hcB j₁⟩)
  · rw [upperSum_succ c' y (j := j₁) (by omega), ← hj₁]
    ring

/-- The integral closure of `B ∩ k` in `l` is contained in `B`; this is the inclusion as an
algebra. -/
instance instAlgebraIntegralClosure :
    Algebra (integralClosure (B.comap (algebraMap k l)) l) B :=
  (RingHom.codRestrict (integralClosure (B.comap (algebraMap k l)) l).val B
    fun z ↦ mem_of_isIntegral_comap B z.2).toAlgebra

@[simp]
theorem coe_algebraMap_integralClosure (z : integralClosure (B.comap (algebraMap k l)) l) :
    ((algebraMap _ B z : B) : l) = z :=
  rfl

/-- **Valuation rings over `A` are localizations of the integral closure.** If `l/k` is
algebraic, `B` is the localization of the integral closure `Ā` of `A = B ∩ k` in `l` at the prime
ideal `𝔪_B ∩ Ā`. -/
theorem isLocalization_integralClosure [Algebra.IsAlgebraic k l] :
    IsLocalization.AtPrime B ((maximalIdeal B).comap
      (algebraMap (integralClosure (B.comap (algebraMap k l)) l) B)) := by
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun b ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · simpa [Ideal.primeCompl, mem_maximalIdeal, mem_nonunits_iff] using hs
  · obtain ⟨s, t, hs, ht, hsu, hst⟩ := exists_isIntegral_mul_eq (k := k) B b.2
    have hsB : IsUnit (⟨s, mem_of_isIntegral_comap B hs⟩ : B) :=
      (B.valuation_eq_one_iff _).mpr hsu
    have hs' : s ∈ integralClosure (B.comap (algebraMap k l)) l := hs
    have ht' : t ∈ integralClosure (B.comap (algebraMap k l)) l := ht
    refine ⟨⟨⟨t, ht'⟩, ⟨⟨s, hs'⟩, ?_⟩⟩, Subtype.ext ?_⟩
    · intro hmem
      exact (mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem) hsB
    · simpa using hst
  · have : ((algebraMap _ B a : B) : l) = (algebraMap _ B b : B) := congrArg Subtype.val h
    simp only [coe_algebraMap_integralClosure] at this
    simp [Subtype.ext this]

/-- **Uniqueness of the extension with a given centre.** Two valuation subrings of the algebraic
extension `l` with the same restriction to `k`, whose nonunits agree on the elements integral over
that restriction, coincide (one inclusion). -/
theorem le_of_comap_eq_of_valuation_lt_one [Algebra.IsAlgebraic k l] {B₁ B₂ : ValuationSubring l}
    (hA : B₁.comap (algebraMap k l) = B₂.comap (algebraMap k l))
    (hc : ∀ z : l, IsIntegral (B₁.comap (algebraMap k l)) z →
      B₂.valuation z < 1 → B₁.valuation z < 1) :
    B₁ ≤ B₂ := by
  intro y hy
  obtain ⟨s, t, hs, ht, hsu, hst⟩ := exists_isIntegral_mul_eq (k := k) B₁ hy
  have hs₂ : s ∈ B₂ := mem_of_isIntegral_comap B₂ (hA ▸ hs)
  have ht₂ : t ∈ B₂ := mem_of_isIntegral_comap B₂ (hA ▸ ht)
  have hsv : B₂.valuation s = 1 := by
    refine le_antisymm ((B₂.valuation_le_one_iff _).mpr hs₂) (not_lt.mp fun h ↦ ?_)
    have := hc s hs h
    rw [hsu] at this
    exact lt_irrefl _ this
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsv
    exact zero_ne_one hsv
  have hsinv : s⁻¹ ∈ B₂ := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hsv, inv_one]
  have : y = t * s⁻¹ := by rw [← hst, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [this]
  exact mul_mem ht₂ hsinv

/-- **Uniqueness of the extension with a given centre.** Two valuation subrings of the algebraic
extension `l` with the same restriction `A` to `k` and the same centre on the integral closure of
`A` coincide. -/
theorem eq_of_comap_eq_of_valuation_lt_one_iff [Algebra.IsAlgebraic k l]
    {B₁ B₂ : ValuationSubring l}
    (hA : B₁.comap (algebraMap k l) = B₂.comap (algebraMap k l))
    (hc : ∀ z : l, IsIntegral (B₁.comap (algebraMap k l)) z →
      (B₁.valuation z < 1 ↔ B₂.valuation z < 1)) :
    B₁ = B₂ :=
  le_antisymm (le_of_comap_eq_of_valuation_lt_one hA fun z hz ↦ (hc z hz).mpr)
    (le_of_comap_eq_of_valuation_lt_one hA.symm fun z hz ↦ (hc z (hA ▸ hz)).mp)

omit B in
/-- **Existence of the extension with a given centre.** For a valuation subring `A` of `k`, an
algebraic extension `l/k` and a maximal ideal `𝔪` of the integral closure `Ā` of `A` in `l`, there
is a valuation subring `B` of `l` with `B ∩ k = A`, containing `Ā`, whose nonunits in `Ā` are
exactly the elements of `𝔪` (so `B = Ā_𝔪` by `isLocalization_integralClosure`). -/
theorem exists_valuationSubring_of_isMaximal [Algebra.IsAlgebraic k l] (A : ValuationSubring k)
    (𝔪 : Ideal (integralClosure A l)) [𝔪.IsMaximal] :
    ∃ B : ValuationSubring l, B.comap (algebraMap k l) = A ∧
      ∀ z : integralClosure A l, (z : l) ∈ B ∧ (z ∈ 𝔪 ↔ B.valuation (z : l) < 1) := by
  set R := Localization.AtPrime 𝔪
  have hg : ∀ y : 𝔪.primeCompl, IsUnit ((integralClosure A l).val.toRingHom y) := by
    intro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr fun h0 ↦ hy ?_
    have : y = 0 := Subtype.ext h0
    rw [this]
    exact 𝔪.zero_mem
  obtain ⟨V, hV, hloc⟩ :=
    IsLocalRing.exists_factor_valuationRing (R := R) (K := l) (IsLocalization.lift hg)
  have hf : ∀ z : integralClosure A l,
      IsLocalization.lift hg (algebraMap (integralClosure A l) R z) = (z : l) :=
    fun z ↦ IsLocalization.lift_eq hg z
  have hmemV : ∀ z : integralClosure A l, (z : l) ∈ V := fun z ↦ hf z ▸ hV _
  have hcentre : ∀ z : integralClosure A l, z ∈ 𝔪 ↔ V.valuation (z : l) < 1 := by
    intro z
    set u : V := (IsLocalization.lift hg).codRestrict V.toSubring hV
      (algebraMap (integralClosure A l) R z)
    have hu : (u : l) = z := hf z
    have hiff : IsUnit (algebraMap (integralClosure A l) R z) ↔ IsUnit u :=
      ⟨fun h ↦ h.map _, fun h ↦ isUnit_of_map_unit _ _ h⟩
    rw [← hu, ← V.valuation_lt_one_iff u, mem_maximalIdeal, mem_nonunits_iff, ← hiff,
      IsLocalization.AtPrime.isUnit_to_map_iff R 𝔪 z, Ideal.mem_primeCompl_iff, not_not]
  refine ⟨V, ?_, fun z ↦ ⟨hmemV z, hcentre z⟩⟩
  have hmax : 𝔪.comap (algebraMap A (integralClosure A l)) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪)
  ext c
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hc
    by_contra hcA
    have hc0 : c ≠ 0 := fun h ↦ hcA (h ▸ A.zero_mem)
    have hinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hnu : (⟨c⁻¹, hinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hw' : c⁻¹ * (w : k) = 1 := congrArg Subtype.val hw
      have : (w : k) = c := by
        rw [← (mul_eq_one_iff_inv_eq₀ (inv_ne_zero hc0)).mp hw', inv_inv]
      exact hcA (this ▸ w.2)
    rw [← hmax, Ideal.mem_comap, hcentre] at hnu
    have hcl : ((algebraMap A (integralClosure A l) ⟨c⁻¹, hinv⟩ : integralClosure A l) : l) =
        (algebraMap k l c)⁻¹ := by
      rw [← map_inv₀]
      rfl
    rw [hcl] at hnu
    have := valuation_mul_lt_one V ((V.valuation_le_one_iff _).mpr hc) hnu
    rw [mul_inv_cancel₀ ((_root_.map_ne_zero _).mpr hc0), map_one] at this
    exact lt_irrefl _ this
  · intro hc
    exact hmemV (algebraMap A (integralClosure A l) ⟨c, hc⟩)

/-- **The henselian case.** If `B` is the only valuation subring of the algebraic extension `l`
lying over `A = B ∩ k` (Temkin's definition of a henselian valued field, `semi-stable.tex`
l. 1921–1927, applied to `l`), then every element of `B` is integral over `A`. -/
theorem isIntegral_of_forall_comap_eq [Algebra.IsAlgebraic k l]
    (huniq : ∀ B' : ValuationSubring l,
      B'.comap (algebraMap k l) = B.comap (algebraMap k l) → B' = B)
    {b : l} (hb : b ∈ B) : IsIntegral (B.comap (algebraMap k l)) b := by
  set A := B.comap (algebraMap k l)
  set N : Submodule (integralClosure A l) l :=
    LinearMap.range (Algebra.linearMap (integralClosure A l) l)
  set I : Ideal (integralClosure A l) := N.colon {b}
  by_cases h1 : (1 : integralClosure A l) ∈ I
  · rw [Submodule.mem_colon_singleton, one_smul] at h1
    obtain ⟨c, hc⟩ := h1
    rw [← hc]
    exact c.2
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr h1)
  obtain ⟨B', hB'A, hB'⟩ := exists_valuationSubring_of_isMaximal A 𝔪
  have hBB' : B' = B := huniq B' hB'A
  subst hBB'
  obtain ⟨s, t, hs, ht, hsu, hst⟩ := exists_isIntegral_mul_eq (k := k) B' hb
  have hs' : s ∈ integralClosure A l := hB'A ▸ hs
  have ht' : t ∈ integralClosure A l := hB'A ▸ ht
  have hsI : (⟨s, hs'⟩ : integralClosure A l) ∈ I := by
    rw [Submodule.mem_colon_singleton]
    refine ⟨⟨t, ht'⟩, ?_⟩
    change t = s * b
    rw [← hst, mul_comm]
  have := ((hB' ⟨s, hs'⟩).2.mp (hI𝔪 hsI))
  rw [hsu] at this
  exact absurd this (lt_irrefl _)

end IntegralClosure

section StdUnramified

variable (k) in
/-- `x ∈ l` is a **standard-unramified generator** of `l/k` for the valuation subring `B` of `l`
(plan `PLAN-SM-VAL.md`, S8): `l = k(x)`, `x` is integral over `A = B ∩ k` (that is, its minimal
polynomial `f` over `k` has coefficients in `A`) and `f'(x)` is a unit of `B`. -/
structure IsStdUnramifiedGenerator (x : l) : Prop where
  adjoin_eq_top : IntermediateField.adjoin k {x} = ⊤
  isIntegral : IsIntegral (B.comap (algebraMap k l)) x
  valuation_aeval_derivative : B.valuation (aeval x (derivative (minpoly k x))) = 1

variable (k) in
/-- The extension `l/k` is **standard-unramified** at `B` (Temkin's "unramified", in the explicit
form S8 of `PLAN-SM-VAL.md`) if it has a standard-unramified generator. -/
def IsStdUnramified : Prop :=
  ∃ x, IsStdUnramifiedGenerator k B x

/-- Elements of `B` evaluated at polynomials over `B ∩ k`, computed in `l`. -/
theorem coe_aeval_comap (p : (B.comap (algebraMap k l))[X]) (y : B) :
    ((aeval y p : B) : l) = aeval (y : l) p := by
  have := aeval_algHom_apply (IsScalarTower.toAlgHom (B.comap (algebraMap k l)) B l) y p
  simp only [IsScalarTower.toAlgHom_apply, ValuationSubring.algebraMap_apply] at this
  exact this.symm

namespace IsStdUnramifiedGenerator

variable {B} {x : l} (hx : IsStdUnramifiedGenerator k B x)
include hx

theorem mem : x ∈ B :=
  mem_of_isIntegral_comap B hx.isIntegral

theorem isIntegral_field : IsIntegral k x :=
  hx.isIntegral.tower_top

theorem minpoly_eq :
    minpoly k x = (minpoly (B.comap (algebraMap k l)) x).map (algebraMap _ k) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' k hx.isIntegral

theorem aeval_derivative_minpoly_comap :
    aeval x (derivative (minpoly (B.comap (algebraMap k l)) x)) =
      aeval x (derivative (minpoly k x)) := by
  rw [hx.minpoly_eq, derivative_map, aeval_map_algebraMap]

theorem aeval_derivative_mem : aeval x (derivative (minpoly k x)) ∈ B := by
  rw [← ValuationSubring.valuation_le_one_iff, hx.valuation_aeval_derivative]

theorem aeval_derivative_ne_zero : aeval x (derivative (minpoly k x)) ≠ 0 := by
  intro h
  have := hx.valuation_aeval_derivative
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem algebra_adjoin_eq_top : Algebra.adjoin k {x} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    hx.isIntegral_field.isAlgebraic, hx.adjoin_eq_top, IntermediateField.top_toSubalgebra]

theorem finiteDimensional : FiniteDimensional k l := by
  have := IntermediateField.adjoin.finiteDimensional hx.isIntegral_field
  rw [hx.adjoin_eq_top] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem isSeparable_elem : IsSeparable k x :=
  (separable_iff_derivative_ne_zero (minpoly.irreducible hx.isIntegral_field)).mpr fun h ↦
    hx.aeval_derivative_ne_zero (by rw [h, map_zero])

theorem isSeparable : Algebra.IsSeparable k l := by
  rw [← separableClosure.eq_top_iff, eq_top_iff, ← hx.adjoin_eq_top,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact mem_separableClosure_iff.mpr hx.isSeparable_elem

theorem isAlgebraic : Algebra.IsAlgebraic k l := by
  have := hx.finiteDimensional
  infer_instance

/-- The **dual basis bound** `f'(x) · Ā ⊆ A[x]`: if `z` is integral over `A = B ∩ k`, then
`f'(x) z = p(x)` for a polynomial `p` over `A`. -/
theorem mul_aeval_derivative_mem {z : l} (hz : IsIntegral (B.comap (algebraMap k l)) z) :
    ∃ p : (B.comap (algebraMap k l))[X], aeval x (derivative (minpoly k x)) * z = aeval x p := by
  have := hx.finiteDimensional
  have := hx.isSeparable
  have hmem : z ∈ (Algebra.traceForm k l).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin (B.comap (algebraMap k l)) {x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro w hw
    rw [Algebra.traceForm_apply, Submodule.mem_one]
    have hwint : IsIntegral (B.comap (algebraMap k l)) w :=
      adjoin_le_integralClosure hx.isIntegral hw
    have htr : IsIntegral (B.comap (algebraMap k l)) (Algebra.trace k l (z * w)) :=
      Algebra.isIntegral_trace (hz.mul hwint)
    exact IsIntegrallyClosed.isIntegral_iff.mp htr
  rw [traceForm_dualSubmodule_adjoin _ k hx.algebra_adjoin_eq_top hx.isIntegral] at hmem
  obtain ⟨w, hw, hwz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hw
  obtain ⟨p, hp⟩ := hw
  refine ⟨p, ?_⟩
  rw [← hwz, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hx.aeval_derivative_ne_zero, one_mul]
  exact hp.symm

/-- The standard étale pair `(f, f')` over `A = B ∩ k`, where `f` is the minimal polynomial of
`x` over `A`; its algebra is `A[X]_{f'}/(f)`. -/
def stdEtalePair : StandardEtalePair (B.comap (algebraMap k l)) where
  f := minpoly _ x
  monic_f := minpoly.monic hx.isIntegral
  g := derivative (minpoly _ x)
  cond := ⟨1, 0, 1, by ring⟩

theorem hasMap : hx.stdEtalePair.HasMap (⟨x, hx.mem⟩ : B) := by
  constructor
  · apply Subtype.ext
    rw [coe_aeval_comap]
    exact minpoly.aeval _ x
  · rw [B.valuation_eq_one_iff, coe_aeval_comap]
    change B.valuation (aeval x (derivative (minpoly _ x))) = 1
    rw [hx.aeval_derivative_minpoly_comap]
    exact hx.valuation_aeval_derivative

/-- The map `A[X]_{f'}/(f) → B` sending `X` to `x`. -/
def toValuationSubring : hx.stdEtalePair.Ring →ₐ[B.comap (algebraMap k l)] B :=
  hx.stdEtalePair.lift _ hx.hasMap

@[simp]
theorem toValuationSubring_X : hx.toValuationSubring hx.stdEtalePair.X = ⟨x, hx.mem⟩ :=
  StandardEtalePair.lift_X _ _ _

theorem toValuationSubring_aeval (p : (B.comap (algebraMap k l))[X]) :
    ((hx.toValuationSubring (aeval hx.stdEtalePair.X p) : B) : l) = aeval x p := by
  rw [← aeval_algHom_apply, toValuationSubring_X, coe_aeval_comap]

/-- The map `A[X]_{f'}/(f) → B` is injective. -/
theorem toValuationSubring_injective : Function.Injective hx.toValuationSubring := by
  set P := hx.stdEtalePair
  let Q : StandardEtalePresentation (B.comap (algebraMap k l)) P.Ring :=
    ⟨P, P.X, P.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, n, hp⟩ := Q.exists_mul_aeval_x_g_pow_eq_aeval_x z
  change z * aeval P.X P.g ^ n = aeval P.X p at hp
  have h1 : aeval x p = 0 := by
    rw [← hx.toValuationSubring_aeval, ← hp, map_mul, hz, zero_mul]
    rfl
  have hdvd : minpoly _ x ∣ p := minpoly.isIntegrallyClosed_dvd hx.isIntegral h1
  have h2 : aeval P.X p = 0 := by
    obtain ⟨q, rfl⟩ := hdvd
    rw [map_mul]
    have : aeval P.X P.f = 0 := P.hasMap_X.1
    change aeval P.X (minpoly _ x) * aeval P.X q = 0
    rw [show minpoly _ x = P.f from rfl, this, zero_mul]
  rw [h2] at hp
  exact (P.hasMap_X.2.pow n).mul_left_eq_zero.mp hp

/-- **`B` is a localization of the standard étale algebra** `A[X]_{f'}/(f)` at the prime ideal
`𝔪_B ∩ A[X]_{f'}/(f)` (plan node V6(a); Temkin, `semi-stable.tex` l. 2132–2139). -/
theorem isLocalization :
    letI := hx.toValuationSubring.toRingHom.toAlgebra
    IsLocalization.AtPrime B ((maximalIdeal B).comap hx.toValuationSubring) := by
  let := hx.toValuationSubring.toRingHom.toAlgebra
  have := hx.isAlgebraic
  set P := hx.stdEtalePair
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun b ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · have hs' : hx.toValuationSubring s ∉ maximalIdeal B := hs
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hs'
    exact hs'
  · obtain ⟨s, t, hs, ht, hsu, hst⟩ := exists_isIntegral_mul_eq (k := k) B b.2
    obtain ⟨p₁, hp₁⟩ := hx.mul_aeval_derivative_mem hs
    obtain ⟨p₂, hp₂⟩ := hx.mul_aeval_derivative_mem ht
    have hunit : B.valuation (aeval x p₁) = 1 := by
      rw [← hp₁, map_mul, hx.valuation_aeval_derivative, hsu, one_mul]
    refine ⟨⟨aeval P.X p₂, ⟨aeval P.X p₁, ?_⟩⟩, Subtype.ext ?_⟩
    · change hx.toValuationSubring (aeval P.X p₁) ∉ maximalIdeal B
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not, B.valuation_eq_one_iff,
        hx.toValuationSubring_aeval]
      exact hunit
    · change (b : l) * (hx.toValuationSubring (aeval P.X p₁) : l) =
        (hx.toValuationSubring (aeval P.X p₂) : l)
      rw [hx.toValuationSubring_aeval, hx.toValuationSubring_aeval, ← hp₁, ← hp₂, ← hst]
      ring
  · rw [hx.toValuationSubring_injective h]

end IsStdUnramifiedGenerator

/-- A finite separable extension is standard-unramified for the trivial valuation `B = l`. -/
theorem isStdUnramified_top [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    IsStdUnramified k (⊤ : ValuationSubring l) := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element k l
  have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  refine ⟨x, hx, isIntegral_comap_of_coeff_mem _ hint fun _ ↦ trivial, ?_⟩
  · have hne : aeval x (derivative (minpoly k x)) ≠ 0 :=
      (Algebra.IsSeparable.isSeparable k x).aeval_derivative_ne_zero (minpoly.aeval k x)
    have : IsUnit (⟨_, trivial⟩ : (⊤ : ValuationSubring l)) :=
      isUnit_iff_ne_zero.mpr fun h ↦ hne (congrArg Subtype.val h)
    exact ((⊤ : ValuationSubring l).valuation_eq_one_iff _).mp this

end StdUnramified

section Residue

/-- Reduction commutes with evaluation of polynomials over `B ∩ k`. -/
theorem residue_aeval_comap (p : (B.comap (algebraMap k l))[X]) (y : B) :
    residue B (aeval y p) =
      aeval (residue B y) (p.map (residue (B.comap (algebraMap k l)))) := by
  rw [← ResidueField.algebraMap_eq (R := B.comap (algebraMap k l)), aeval_map_algebraMap]
  have := aeval_algHom_apply
    (IsScalarTower.toAlgHom (B.comap (algebraMap k l)) B (ResidueField B)) y p
  simp only [IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq] at this
  exact this.symm

theorem aeval_derivative_minpoly_comap_eq {y : l} (hy : IsIntegral (B.comap (algebraMap k l)) y) :
    aeval y (derivative (minpoly (B.comap (algebraMap k l)) y)) =
      aeval y (derivative (minpoly k y)) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' k hy, derivative_map, aeval_map_algebraMap]

/-- **Unramified criterion via the residue field** (Temkin, Lemma 2.1.5(ii), the direction
"`f = n` and `l̃/k̃` separable implies unramified", for an extension with unique valuation ring
over `A`). Let `l/k` be finite, `A = B ∩ k`, and suppose `[κ(B) : κ(A)] = [l : k]` and
`κ(B)/κ(A)` is separable. If `y ∈ B` is integral over `A` and its residue generates
`κ(B)/κ(A)`, then `y` is a standard-unramified generator of `l/k` at `B`. -/
theorem isStdUnramifiedGenerator_of_residue [FiniteDimensional k l] {y : l} (hyB : y ∈ B)
    (hint : IsIntegral (B.comap (algebraMap k l)) y)
    (hn : Module.finrank (ResidueField (B.comap (algebraMap k l))) (ResidueField B) =
      Module.finrank k l)
    (hsep : Algebra.IsSeparable (ResidueField (B.comap (algebraMap k l))) (ResidueField B))
    (hgen : IntermediateField.adjoin (ResidueField (B.comap (algebraMap k l)))
      {residue B ⟨y, hyB⟩} = ⊤) :
    IsStdUnramifiedGenerator k B y := by
  set A := B.comap (algebraMap k l)
  set κ := ResidueField A
  set ybar := residue B ⟨y, hyB⟩
  set fA := minpoly A y
  have hfA : fA.Monic := minpoly.monic hint
  set fbar := fA.map (residue A)
  have hfbar : fbar.Monic := hfA.map _
  have hdeg : fbar.natDegree = (minpoly k y).natDegree := by
    rw [hfA.natDegree_map, minpoly.isIntegrallyClosed_eq_field_fractions' k hint,
      hfA.natDegree_map]
  have hroot : aeval ybar fbar = 0 := by
    rw [← residue_aeval_comap]
    have : aeval (⟨y, hyB⟩ : B) fA = 0 :=
      Subtype.ext (by rw [coe_aeval_comap]; exact minpoly.aeval _ y)
    rw [this, map_zero]
  have hybar : IsIntegral κ ybar := ⟨fbar, hfbar, by rwa [← aeval_def]⟩
  have hfin : FiniteDimensional κ (ResidueField B) :=
    Module.finite_of_finrank_pos (by rw [hn]; exact Module.finrank_pos)
  have hdegbar : (minpoly κ ybar).natDegree = Module.finrank k l := by
    rw [← IntermediateField.adjoin.finrank hybar, hgen, IntermediateField.finrank_top', hn]
  have hdvd : minpoly κ ybar ∣ fbar := minpoly.dvd κ ybar hroot
  have hle1 : (minpoly κ ybar).natDegree ≤ fbar.natDegree :=
    natDegree_le_of_dvd hdvd hfbar.ne_zero
  have hle2 : (minpoly k y).natDegree ≤ Module.finrank k l := minpoly.natDegree_le y
  have heq : fbar = minpoly κ ybar :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hybar) hfbar hdvd (by omega)
  have hyk : IsIntegral k y := hint.tower_top
  refine ⟨?_, hint, ?_⟩
  · apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.adjoin.finrank hyk, IntermediateField.finrank_top']
    omega
  · set a : B := aeval (⟨y, hyB⟩ : B) (derivative fA)
    have ha : (a : l) = aeval y (derivative (minpoly k y)) := by
      rw [coe_aeval_comap]
      exact aeval_derivative_minpoly_comap_eq B hint
    have hne : residue B a ≠ 0 := by
      rw [residue_aeval_comap, ← derivative_map]
      change aeval ybar (derivative fbar) ≠ 0
      rw [heq]
      exact (Algebra.IsSeparable.isSeparable κ ybar).aeval_derivative_ne_zero
        (minpoly.aeval κ ybar)
    rw [← ha, ← B.valuation_eq_one_iff]
    exact (residue_ne_zero_iff_isUnit a).mp hne

/-- **Unramified criterion via the residue field** (Temkin, Lemma 2.1.5(ii), "if" direction):
if every element of `B` is integral over `A = B ∩ k` (for instance if `B` is the only valuation
ring of `l` over `A`), `[κ(B) : κ(A)] = [l : k]` and `κ(B)/κ(A)` is separable, then `l/k` is
standard-unramified at `B`. -/
theorem isStdUnramified_of_residue [FiniteDimensional k l]
    (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b)
    (hn : Module.finrank (ResidueField (B.comap (algebraMap k l))) (ResidueField B) =
      Module.finrank k l)
    (hsep : Algebra.IsSeparable (ResidueField (B.comap (algebraMap k l))) (ResidueField B)) :
    IsStdUnramified k B := by
  have : FiniteDimensional (ResidueField (B.comap (algebraMap k l))) (ResidueField B) :=
    Module.finite_of_finrank_pos (by rw [hn]; exact Module.finrank_pos)
  obtain ⟨ybar, hybar⟩ :=
    Field.exists_primitive_element (ResidueField (B.comap (algebraMap k l))) (ResidueField B)
  obtain ⟨b, rfl⟩ := residue_surjective ybar
  exact ⟨b, isStdUnramifiedGenerator_of_residue B b.2 (hB b b.2) hn hsep hybar⟩

namespace IsStdUnramifiedGenerator

variable {B} {x : l} (hx : IsStdUnramifiedGenerator k B x)
include hx

/-- The reduction `f̄` of the minimal polynomial of a standard-unramified generator has `x̄` as a
simple root. -/
theorem aeval_derivative_residue_ne_zero :
    aeval (residue B ⟨x, hx.mem⟩)
      (derivative ((minpoly (B.comap (algebraMap k l)) x).map
        (residue (B.comap (algebraMap k l))))) ≠ 0 := by
  rw [derivative_map, ← residue_aeval_comap, residue_ne_zero_iff_isUnit, B.valuation_eq_one_iff,
    coe_aeval_comap, hx.aeval_derivative_minpoly_comap]
  exact hx.valuation_aeval_derivative

theorem aeval_residue_eq_zero :
    aeval (residue B ⟨x, hx.mem⟩)
      ((minpoly (B.comap (algebraMap k l)) x).map (residue (B.comap (algebraMap k l)))) = 0 := by
  rw [← residue_aeval_comap]
  have : aeval (⟨x, hx.mem⟩ : B) (minpoly (B.comap (algebraMap k l)) x) = 0 :=
    Subtype.ext (by rw [coe_aeval_comap]; exact minpoly.aeval _ x)
  rw [this, map_zero]

theorem isIntegral_residue :
    IsIntegral (ResidueField (B.comap (algebraMap k l))) (residue B ⟨x, hx.mem⟩) :=
  ⟨_, (minpoly.monic hx.isIntegral).map _, by rw [← aeval_def]; exact hx.aeval_residue_eq_zero⟩

/-- The residue `x̄` of a standard-unramified generator is separable over `κ(A)`. -/
theorem isSeparable_residue :
    IsSeparable (ResidueField (B.comap (algebraMap k l))) (residue B ⟨x, hx.mem⟩) := by
  set κ := ResidueField (B.comap (algebraMap k l))
  set xbar := residue B ⟨x, hx.mem⟩
  obtain ⟨q, hq⟩ := minpoly.dvd κ xbar hx.aeval_residue_eq_zero
  refine (separable_iff_derivative_ne_zero (minpoly.irreducible hx.isIntegral_residue)).mpr
    fun h ↦ hx.aeval_derivative_residue_ne_zero ?_
  rw [hq, derivative_mul, h, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]

/-- If every element of `B` is integral over `A = B ∩ k`, then `B = A[x]` for every
standard-unramified generator `x`. -/
theorem mem_adjoin (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b) {b : l}
    (hb : b ∈ B) : b ∈ Algebra.adjoin (B.comap (algebraMap k l)) {x} := by
  set d := aeval x (derivative (minpoly k x))
  have hd0 : d ≠ 0 := hx.aeval_derivative_ne_zero
  have hdinv : d⁻¹ ∈ B := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hx.valuation_aeval_derivative,
      inv_one]
  obtain ⟨p, hp⟩ := hx.mul_aeval_derivative_mem (hB _ (mul_mem hdinv hb))
  rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul] at hp
  rw [hp, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p, rfl⟩

/-- If every element of `B` is integral over `A`, the residue field `κ(B)` is generated over
`κ(A)` by the residue of a standard-unramified generator. -/
theorem adjoin_residue_eq_top (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b) :
    IntermediateField.adjoin (ResidueField (B.comap (algebraMap k l)))
      {residue B ⟨x, hx.mem⟩} = ⊤ := by
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨b, rfl⟩ := residue_surjective z
  have hmem := hx.mem_adjoin hB b.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hb : b = aeval (⟨x, hx.mem⟩ : B) p := Subtype.ext (by rw [coe_aeval_comap]; exact hp.symm)
  rw [hb, residue_aeval_comap]
  apply IntermediateField.algebra_adjoin_le_adjoin
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨_, rfl⟩

/-- If every element of `B` is integral over `A`, the residue extension of a standard-unramified
extension is separable. -/
theorem isSeparable_residueField (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b) :
    Algebra.IsSeparable (ResidueField (B.comap (algebraMap k l))) (ResidueField B) := by
  rw [← separableClosure.eq_top_iff, eq_top_iff, ← hx.adjoin_residue_eq_top hB,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact mem_separableClosure_iff.mpr hx.isSeparable_residue

/-- **Temkin, Lemma 2.1.5(ii), "only if" direction**, for an extension with unique valuation ring
over `A`: if every element of `B` is integral over `A = B ∩ k` and `x` is a standard-unramified
generator, then the reduction of the minimal polynomial of `x` over `A` is the minimal polynomial
of `x̄` over `κ(A)`. -/
theorem map_minpoly_eq (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b) :
    (minpoly (B.comap (algebraMap k l)) x).map (residue (B.comap (algebraMap k l))) =
      minpoly (ResidueField (B.comap (algebraMap k l))) (residue B ⟨x, hx.mem⟩) := by
  set A := B.comap (algebraMap k l)
  set κ := ResidueField A
  set xbar := residue B ⟨x, hx.mem⟩
  set fA := minpoly A x
  set fbar := fA.map (residue A)
  set m := minpoly κ xbar
  have hfbar : fbar.Monic := (minpoly.monic hx.isIntegral).map _
  have hm : m.Monic := minpoly.monic hx.isIntegral_residue
  obtain ⟨h, hh⟩ : m ∣ fbar := minpoly.dvd κ xbar hx.aeval_residue_eq_zero
  have hhmonic : h.Monic := hm.of_mul_monic_left (hh ▸ hfbar)
  suffices h = 1 by rw [hh, this, mul_one]
  by_contra hne
  obtain ⟨q, hq, hqh⟩ := exists_irreducible_of_degree_pos (hhmonic.degree_pos.mpr hne)
  have : Fact (Irreducible q) := ⟨hq⟩
  have h0 : eval₂ ((AdjoinRoot.of q).comp (residue A)) (AdjoinRoot.root q) fA = 0 := by
    rw [← eval₂_map, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_eq_zero]
    exact hqh.trans ⟨m, by rw [mul_comm]; exact hh⟩
  -- the ring map `ψ : B = A[x] ≅ A[X]/(f) → κ(A)[X]/(q)`
  set e := minpoly.equivAdjoin hx.isIntegral
  set ψ' : AdjoinRoot fA →+* AdjoinRoot q :=
    AdjoinRoot.lift ((AdjoinRoot.of q).comp (residue A)) (AdjoinRoot.root q) h0
  set ι : B →+* Algebra.adjoin A {x} :=
    B.subtype.codRestrict (Algebra.adjoin A {x}) fun b ↦ hx.mem_adjoin hB b.2
  set ψ : B →+* AdjoinRoot q := ψ'.comp (e.symm.toRingEquiv.toRingHom.comp ι)
  have hroot : ((e (AdjoinRoot.root fA) : Algebra.adjoin A {x}) : l) = x := by
    have := AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := A) (x := x)
    rw [← minpoly.equivAdjoin_toAlgHom hx.isIntegral, AdjoinRoot.mk_X] at this
    exact this
  have hψ : ∀ p : A[X], ψ (aeval (⟨x, hx.mem⟩ : B) p) =
      eval₂ ((AdjoinRoot.of q).comp (residue A)) (AdjoinRoot.root q) p := by
    intro p
    have he : e (AdjoinRoot.mk fA p) = ι (aeval (⟨x, hx.mem⟩ : B) p) := by
      apply Subtype.ext
      change ((e (AdjoinRoot.mk fA p) : Algebra.adjoin A {x}) : l) =
        ((aeval (⟨x, hx.mem⟩ : B) p : B) : l)
      have := aeval_algHom_apply (e : AdjoinRoot fA →ₐ[A] Algebra.adjoin A {x})
        (AdjoinRoot.root fA) p
      rw [AdjoinRoot.aeval_eq] at this
      change ((e : AdjoinRoot fA →ₐ[A] Algebra.adjoin A {x}) (AdjoinRoot.mk fA p) : l) = _
      rw [← this, aeval_subalgebra_coe, coe_aeval_comap]
      exact congrArg (fun z ↦ aeval z p) hroot
    change ψ' (e.symm (ι (aeval (⟨x, hx.mem⟩ : B) p))) = _
    rw [← he, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_mk]
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using AdjoinRoot.induction_on with
    | ih rbar =>
      obtain ⟨r, rfl⟩ := map_surjective (residue A) residue_surjective rbar
      refine ⟨aeval (⟨x, hx.mem⟩ : B) r, ?_⟩
      rw [hψ, ← eval₂_map, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  have hker : RingHom.ker ψ = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hsurj)
  obtain ⟨gA, hgA⟩ := map_surjective (residue A) residue_surjective m
  have hG : aeval (⟨x, hx.mem⟩ : B) gA ∈ RingHom.ker ψ := by
    rw [hker, ← residue_eq_zero_iff, residue_aeval_comap, hgA]
    exact minpoly.aeval κ xbar
  rw [RingHom.mem_ker, hψ, ← eval₂_map, hgA, ← AdjoinRoot.algebraMap_eq, ← aeval_def,
    AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hG
  obtain ⟨h', hh'⟩ := ((Irreducible.dvd_symm hq (minpoly.irreducible hx.isIntegral_residue)
    hG).trans hqh)
  apply hx.aeval_derivative_residue_ne_zero
  change aeval xbar (derivative fbar) = 0
  have hm0 : aeval xbar m = 0 := minpoly.aeval κ xbar
  have hm1 : aeval xbar (minpoly κ (residue B ⟨x, hx.mem⟩)) = 0 := minpoly.aeval _ _
  rw [hh, hh']
  simp [derivative_mul, hm0, hm1]

/-- **Temkin, Lemma 2.1.5(ii), "only if" direction**: if every element of `B` is integral over
`A = B ∩ k` and `l/k` has a standard-unramified generator at `B`, then
`[κ(B) : κ(A)] = [l : k]`. -/
theorem finrank_residueField_eq (hB : ∀ b ∈ B, IsIntegral (B.comap (algebraMap k l)) b) :
    Module.finrank (ResidueField (B.comap (algebraMap k l))) (ResidueField B) =
      Module.finrank k l := by
  rw [← IntermediateField.finrank_top', ← hx.adjoin_residue_eq_top hB,
    IntermediateField.adjoin.finrank hx.isIntegral_residue, ← hx.map_minpoly_eq hB,
    (minpoly.monic hx.isIntegral).natDegree_map, ← (minpoly.monic hx.isIntegral).natDegree_map
      (algebraMap _ k), ← hx.minpoly_eq, ← IntermediateField.adjoin.finrank hx.isIntegral_field,
    hx.adjoin_eq_top, IntermediateField.finrank_top']

end IsStdUnramifiedGenerator

end Residue

end DeJongAlterations.StableModification.Valuation
