import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Reduction identities for equally weighted finite generating families. -/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1UniformVertexReduction

open HironakaActualWeightedCoefficientCompression

private theorem exists_exponent_ge {ι : Type*} [Fintype ι]
    (α : ι →₀ ℕ) {e r : ℕ} (hDegree : α.degree = e + r)
    (hBound : Fintype.card ι * (e - 1) < e + r) : ∃ i, e ≤ α i := by
  classical
  by_contra! h
  have hSum : ∑ i, α i ≤ ∑ _i : ι, (e - 1) :=
    Finset.sum_le_sum fun i _ => by have hi := h i; omega
  rw [← Finsupp.degree_eq_sum, hDegree, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hSum
  exact (not_le_of_gt hBound) hSum

/-- Pure powers of generators give a reduction of the corresponding
power of their span once the total degree forces a pure-power factor. -/
theorem purePowers_mul_span_pow {ι R : Type*} [Fintype ι] [CommRing R]
    (c : ι → R) (e r : ℕ) (hBound : Fintype.card ι * (e - 1) < e + r) :
    let I := Ideal.span (range c)
    let J := Ideal.span (range fun i => c i ^ e)
    J * I ^ r = I ^ (e + r) := by
  classical
  intro I J
  have hI : ∀ i : ι, c i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hJ : J ≤ I ^ e := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_pow (hI i) e
  apply le_antisymm
  · rw [pow_add]
    exact mul_le_mul' hJ le_rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous c x).mp hx
    rw [p.as_sum, map_sum]
    apply Ideal.sum_mem
    intro α hα
    have hαDegree : α.degree = e + r := (hp.degree_eq_sum_deg_support hα).symm
    obtain ⟨i, hi⟩ := exists_exponent_ge α hαDegree hBound
    let β := α - Finsupp.single i e
    have hSplit : Finsupp.single i e + β = α := by
      ext j
      simp only [Finsupp.add_apply, β, Finsupp.tsub_apply]
      by_cases h : i = j
      · subst j
        simpa only [Finsupp.single_eq_same] using Nat.add_sub_of_le hi
      · simp [Finsupp.single_eq_of_ne' h]
    have hβDegree : β.degree = r := by
      have hd := congrArg Finsupp.degree hSplit
      rw [map_add, Finsupp.degree_single, hαDegree] at hd
      exact Nat.add_left_cancel hd
    have hFactor : MvPolynomial.monomial α (p.coeff α) =
        MvPolynomial.monomial (Finsupp.single i e) (1 : R) *
          MvPolynomial.monomial β (p.coeff α) := by
      rw [MvPolynomial.monomial_mul, one_mul, hSplit]
    rw [hFactor, map_mul]
    apply Ideal.mul_mem_mul
    · have hMem : c i ^ e ∈ J := Ideal.subset_span ⟨i, rfl⟩
      simpa [MvPolynomial.eval_monomial] using hMem
    · exact (Ideal.mem_span_pow_iff_exists_isHomogeneous c _).mpr
        ⟨_, MvPolynomial.isHomogeneous_monomial _ hβDegree, rfl⟩

/-- The actual uniform-weight compression has a common reduction
product depending only on the uncompressed source span. -/
theorem uniformCompression_mul_span_pow {ι R : Type*} [Fintype ι] [Nonempty ι] [CommRing R]
    (w : ℕ) (c : ι → R) (hw : 0 < w) :
    let I := Ideal.span (range c)
    let e := weightedCommonMark (fun _ : ι => w) / w
    let r := Fintype.card ι * (e - 1)
    weightedCompression (fun _ : ι => w) c * I ^ r = I ^ (e + r) := by
  intro I e r
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have he : 0 < e := compressionExponent_pos (fun _ : ι => w) (fun _ => hw) i
  exact purePowers_mul_span_pow c e r (by dsimp [r]; omega)

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers IdealOrderArithmetic
  HironakaActualPowerBoundaryExponents BlowupTowers

/-- A marked reduction preserves the normalized order threshold on a
closed carrier, for any positive common compression exponent. -/
theorem cosupport_eq_of_power_reduction {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {N : Set M} (hN : IsClosedSubmanifold n N) {I J : GermIdeal n M} (hI : I.IsCoherent)
    {e r : ℕ} (he : 0 < e) (hsub : J.Le (idealPow I e))
    (hprod : J.mul (idealPow I r) = idealPow I (e + r)) (d : ℕ) :
    cosupport n N J (e * d) = cosupport n N I d := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hn
    have hex : ∃ m : ℕ, x ∉ cosupport n N I m := ⟨d, hn⟩
    let s := Nat.find hex
    have hs : x ∉ cosupport n N I s := Nat.find_spec hex
    have hs₀ : s ≠ 0 := by
      intro hZero
      rw [hZero, cosupport_zero (fun _ _ hf =>
        GermIdeal.IsCoherent.holomorphicAt_mem hI hf)] at hs
      exact hs hx.1
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hs₀
    have hmd : m < d := by
      have hFind : s ≤ d := Nat.find_min' hex hn
      omega
    have hmIn : x ∈ cosupport n N I m := by
      by_contra hmiss
      exact (Nat.find_min hex (show m < s by omega)) hmiss
    have hrIn : x ∈ cosupport n N (idealPow I r) (r * m) := by
      simpa only [Nat.mul_comm] using cosupport_subset_cosupport_idealPow m r hmIn
    have hCurrent : x ∈ cosupport n N (idealPow I (e + r)) (e * d + r * m) := by
      rw [← hprod]
      exact inter_cosupport_subset_cosupport_mul _ _ ⟨hx, hrIn⟩
    have hlt := Nat.mul_lt_mul_of_pos_left hmd he
    have hLe : (e + r) * m + 1 ≤ e * d + r * m := by
      rw [Nat.add_mul]
      omega
    have hAbove := cosupport_anti hLe hCurrent
    rw [cosupport_idealPow_mul_succ_eq_along (X := CMfd.of (n := n) M) hN hI
      (show 1 ≤ e + r by omega) m] at hAbove
    exact hs (hm ▸ hAbove)
  · intro hx
    have hPow : x ∈ cosupport n N (idealPow I e) (e * d) := by
      simpa only [Nat.mul_comm] using cosupport_subset_cosupport_idealPow d e hx
    exact ⟨hPow.1, fun f hf => hPow.2 f (hsub x f hf)⟩

end Hironaka.HironakaG1UniformVertexReduction
