import DeJongAlterations.Algebra.NodeFlatPresentation
import DeJongAlterations.Algebra.RegularLocalDomain
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Complete regular local rings of dimension one with a coefficient field

Let `K` be a field and `R` a complete regular local `K`-algebra of dimension one such that
`K → R/𝔪_R` is surjective. Then `R ≅ K[[w]]` as `K`-algebras, `w` going to any generator of
`𝔪_R`. This is the structure of the completed local ring of a curve over an algebraically closed
field at a smooth closed point, used in de Jong 1996, 4.25 (i)
(`references/dejong96-alterations/tex/page-0026.tex`).

The proof is elementary: `𝔪_R = (w)` since `R` is regular of dimension one; every `r ∈ R` is
`∑_{n<N} c_n w^n + w^N r_N` by successive division, so the evaluation `K[[W]] → R`, `W ↦ w`
(Codex's `Algebra.NodeFlatPresentation.evaluation`), is surjective by the Krull intersection
theorem; it is injective because a nonzero power series is `W^n` times a unit and `R` is a domain
with `w ≠ 0`.
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open IsLocalRing

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [IsRegularLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- In a regular local ring of dimension one the maximal ideal is principal and nonzero. -/
theorem exists_maximalIdeal_eq_span_of_ringKrullDim_eq_one (hdim : ringKrullDim R = 1) :
    ∃ w : R, w ≠ 0 ∧ maximalIdeal R = Ideal.span {w} := by
  have h1 : (maximalIdeal R).spanFinrank = 1 := by
    have := (isRegularLocalRing_iff R).mp inferInstance
    rw [hdim] at this
    exact_mod_cast this
  obtain ⟨⟨w, hw⟩, hne⟩ := (Submodule.spanFinrank_eq_one_iff _).mp h1
  refine ⟨w, ?_, hw⟩
  rintro rfl
  apply hne
  rw [hw, Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]

omit [IsAdicComplete (maximalIdeal R) R] in
/-- Successive division by a generator `w` of `𝔪_R`, using a section of the residue map. -/
theorem exists_division_step {w : R} (hw : maximalIdeal R = Ideal.span {w})
    (hres : Function.Surjective ((residue R).comp (algebraMap K R))) (r : R) :
    ∃ c : K, ∃ r' : R, r = algebraMap K R c + w * r' := by
  obtain ⟨c, hc⟩ := hres (residue R r)
  have hmem : r - algebraMap K R c ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change residue R r - residue R (algebraMap K R c) = 0
    rw [← RingHom.comp_apply, hc, sub_self]
  rw [hw, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r', hr'⟩ := hmem
  exact ⟨c, r', by rw [mul_comm, hr']; ring⟩

/-- **Cohen structure in dimension one.** A complete regular local `K`-algebra `R` of dimension one
with `K → R/𝔪_R` surjective is isomorphic to `K[[w]]` as a `K`-algebra. -/
theorem nonempty_powerSeries_algEquiv_of_ringKrullDim_eq_one (hdim : ringKrullDim R = 1)
    (hres : Function.Surjective ((residue R).comp (algebraMap K R))) :
    Nonempty (PowerSeries K ≃ₐ[K] R) := by
  obtain ⟨w, hw0, hw⟩ := exists_maximalIdeal_eq_span_of_ringKrullDim_eq_one hdim
  have hwm : w ∈ maximalIdeal R := by rw [hw]; exact Ideal.mem_span_singleton_self w
  let : IsDomain R := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing R
  let φ : PowerSeries K →ₐ[K] R :=
    Algebra.NodeFlatPresentation.evaluation (σ := Unit) (maximalIdeal R) (fun _ => w)
      (fun _ => hwm)
  have hφX : φ PowerSeries.X = w :=
    Algebra.NodeFlatPresentation.evaluation_X (σ := Unit) _ _ _ ()
  have hφC : ∀ c : K, φ (PowerSeries.C c) = algebraMap K R c := fun c => φ.commutes c
  -- injectivity
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    by_contra hF0
    obtain ⟨G, hG⟩ := PowerSeries.X_pow_order_dvd (φ := F)
    have hco := PowerSeries.coeff_order hF0
    obtain ⟨k, hk⟩ : ∃ k, F.order.toNat = k := ⟨_, rfl⟩
    rw [hk] at hG hco
    have hGu : IsUnit G := by
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      intro h0
      apply hco
      rw [hG, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
      simpa using h0
    rw [hG, map_mul, map_pow, hφX] at hF
    exact (mul_ne_zero (pow_ne_zero _ hw0) (hGu.map φ).ne_zero) hF
  -- surjectivity
  choose c r' hstep using exists_division_step (K := K) hw hres
  have hsurj : Function.Surjective φ := by
    intro r
    let seq : ℕ → R := fun n => (fun s => r' s)^[n] r
    let F : PowerSeries K := PowerSeries.mk fun n => c (seq n)
    refine ⟨F, ?_⟩
    have hexp : ∀ N : ℕ, r = (∑ n ∈ Finset.range N, algebraMap K R (c (seq n)) * w ^ n) +
        w ^ N * seq N := by
      intro N
      induction N with
      | zero => simp [seq]
      | succ N ih =>
        have hs : seq (N + 1) = r' (seq N) := Function.iterate_succ_apply' _ _ _
        have h1 := hstep (seq N)
        rw [Finset.sum_range_succ, hs]
        linear_combination ih + w ^ N * h1
    apply (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr
    intro N
    -- `F` minus its truncation is divisible by `W^N`
    let P : PowerSeries K := ∑ n ∈ Finset.range N, PowerSeries.C (c (seq n)) * PowerSeries.X ^ n
    have hdvd : PowerSeries.X ^ N ∣ F - P := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      simp only [map_sub, F, P, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single m (fun b _ hb => if_neg (Ne.symm hb))
        (fun h => absurd (Finset.mem_range.mpr hm) h), if_pos rfl, sub_self]
    obtain ⟨G, hG⟩ := hdvd
    have hφP : φ P = ∑ n ∈ Finset.range N, algebraMap K R (c (seq n)) * w ^ n := by
      simp only [P, map_sum, map_mul, map_pow, hφC, hφX]
    have hFeq : F = P + PowerSeries.X ^ N * G := by rw [← hG]; ring
    have hdiff : φ F - r = w ^ N * (φ G - seq N) := by
      rw [hFeq, map_add, map_mul, map_pow, hφX, hφP]
      conv_lhs => rw [hexp N]
      ring
    rw [SModEq.sub_mem, hdiff, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hwm N)
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end DeJongAlterations.StableModification.Resolution
