import DeJongAlterations.StableModification.Valuation.Composition
import DeJongAlterations.StableModification.Valuation.FiniteHeight
import Mathlib.Algebra.CharP.Algebra

/-!
# Heights and characteristics in the induction of Theorem 2.1.8

This file contains the bookkeeping of heights and residue characteristics needed for the
induction on the height in the proof of Theorem 2.1.8 (`valunif`) of M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.2 (`semi-stable.tex`,
lines 2205–2232), and for the étale conclusion via Lemma 2.1.1 (`finhtlem`, lines 1904–1915),
which needs a base of finite height. Blueprint chapter `sm-val-main.tex`.

## Main results

* `trdeg_residueField_comap_le`: `trdeg (κ(V)/κ(V ∩ K)) ≤ trdeg (F/K)` (the residue part of
  Abhyankar's inequality, Temkin Lemma 2.1.2).
* `finite_primeSpectrum_of_trdeg_le_one` (**finite height in transcendence degree one**): if
  `trdeg (F/K) ≤ 1` and `V ∩ K` has finite height, then so has `V`. Every fibre of the map
  `W ↦ W ∩ K` on the overrings of `V` has at most two elements, since three overrings
  `W₀ < W₁ < W₂` with the same trace on `K` would give a valuation ring of height `≥ 2` of
  `κ(W₂)` containing `κ(W₂ ∩ K)`, against Abhyankar's inequality.
* `residueSubring_eq_decompose`, `finite_primeSpectrum_decompose`, `height_decompose_lt`: the
  valuation ring induced on the residue field of a proper coarsening has smaller height.
* `expChar_residueField_of_le`, `expChar_residueField_decompose`: equal characteristic passes to
  coarsenings and to the induced valuation rings of residue fields.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation.MainUniformization

/-! ### Finite height in transcendence degree one -/

section FiniteHeight

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Abhyankar's inequality, residue part** (Temkin, Lemma 2.1.2): the residue field extension of
a valuation ring `V` of `F` over `V ∩ K` has transcendence degree at most `trdeg (F/K)`. -/
theorem trdeg_residueField_comap_le (V : ValuationSubring F) :
    Algebra.trdeg (ResidueField (V.comap (algebraMap K F))) (ResidueField V) ≤
      Algebra.trdeg K F := by
  have h := relRatRank_add_trdeg_le (V.valuation.comap (algebraMap K F)) V.valuation
  have h2 : Algebra.trdeg (ResidueField (V.valuation.valuationSubring.comap (algebraMap K F)))
      (ResidueField V.valuation.valuationSubring) ≤ Algebra.trdeg K F := le_trans le_add_self h
  rwa [ValuationSubring.valuationSubring_valuation] at h2

/-- A valuation ring with three distinct overrings `D < D₁ < ⊤` has at least three primes. -/
theorem three_le_natCard_primeSpectrum {L : Type*} [Field L] {D D₁ : ValuationSubring L}
    (h1 : D < D₁) (h2 : D₁ < ⊤) [Finite (PrimeSpectrum D)] : 3 ≤ Nat.card (PrimeSpectrum D) := by
  have hfin : Finite {S // D ≤ S} := Finite.of_equiv _ (ValuationSubring.primeSpectrumEquiv D)
  rw [Nat.card_congr (ValuationSubring.primeSpectrumEquiv D)]
  let f : Fin 3 → {S // D ≤ S} := ![⟨D, le_rfl⟩, ⟨D₁, h1.le⟩, ⟨⊤, le_top⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : (f i : ValuationSubring L) = f j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f, h1.ne, h2.ne, h1.ne', h2.ne',
      (h1.trans h2).ne, (h1.trans h2).ne']
  simpa using Nat.card_le_card_of_injective f hf

/-- No three overrings `W₀ < W₁ < W₂` have the same trace on `K` when `trdeg (F/K) ≤ 1`. -/
theorem not_comap_eq_of_lt_of_lt (htr : Algebra.trdeg K F ≤ 1) {W₀ W₁ W₂ : ValuationSubring F}
    (h01 : W₀ < W₁) (h12 : W₁ < W₂)
    (hc : W₀.comap (algebraMap K F) = W₂.comap (algebraMap K F)) : False := by
  have h02 : W₀ ≤ W₂ := h01.le.trans h12.le
  set D := decompose W₂ h02
  set D₁ := decompose W₂ h12.le
  have hDD₁ : D < D₁ := by
    refine lt_of_le_of_ne (decompose_mono W₂ h02 h12.le h01.le) fun h ↦ h01.ne ?_
    rw [← compose_decompose W₂ h02, ← compose_decompose W₂ h12.le]
    exact congrArg (compose W₂) h
  have hD₁ : D₁ < ⊤ := lt_top_iff_ne_top.mpr fun h ↦ h12.ne ((decompose_eq_top_iff W₂ _).mp h)
  have hK : ∀ x : ResidueField (W₂.comap (algebraMap K F)),
      algebraMap (ResidueField (W₂.comap (algebraMap K F))) (ResidueField W₂) x ∈ D := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue]
    refine ⟨algebraMap _ W₂ a, ?_, rfl⟩
    have ha : (a : K) ∈ W₀.comap (algebraMap K F) := by
      rw [hc]
      exact a.2
    exact ha
  have hdim := ringKrullDim_le_trdeg D hK
  have htr' := trdeg_residueField_comap_le (K := K) W₂
  have hle : ringKrullDim D ≤ 1 := by
    refine hdim.trans ?_
    have : Cardinal.toENat (Algebra.trdeg (ResidueField (W₂.comap (algebraMap K F)))
        (ResidueField W₂)) ≤ 1 := by
      have := Cardinal.toENat.monotone' (htr'.trans htr)
      simpa using this
    exact_mod_cast this
  have hfin : Finite (PrimeSpectrum D) := by
    rw [finite_primeSpectrum_iff_ringKrullDim_ne_top]
    exact ne_top_of_le_ne_top (by decide) hle
  have hht : height D ≤ 1 := by
    rw [ringKrullDim_eq_height] at hle
    exact_mod_cast hle
  have h3 := three_le_natCard_primeSpectrum hDD₁ hD₁
  rw [natCard_primeSpectrum_eq_height_add_one] at h3
  omega

/-- **Finite height in transcendence degree one** (used for Temkin's Lemma 2.1.1 in the
consumer, `semi-stable.tex` l. 3059–3061): if `trdeg (F/K) ≤ 1` and `V ∩ K` has finitely many
primes, then so has `V` (indeed `ht V ≤ 2 (ht (V ∩ K) + 1) - 1`). -/
theorem finite_primeSpectrum_of_trdeg_le_one (V : ValuationSubring F)
    [Finite (PrimeSpectrum (V.comap (algebraMap K F)))] (htr : Algebra.trdeg K F ≤ 1) :
    Finite (PrimeSpectrum V) := by
  classical
  set A := V.comap (algebraMap K F)
  have hA : Finite {S // A ≤ S} := Finite.of_equiv _ (ValuationSubring.primeSpectrumEquiv A)
  let isMax : {W // V ≤ W} → Prop := fun W ↦
    ∀ W' : ValuationSubring F, V ≤ W' →
      W'.comap (algebraMap K F) = W.1.comap (algebraMap K F) → W' ≤ W.1
  let Φ : {W // V ≤ W} → {S // A ≤ S} × Prop := fun W ↦
    (⟨W.1.comap (algebraMap K F), fun x hx ↦ W.2 hx⟩, isMax W)
  have hmax : ∀ W W' : {W // V ≤ W}, W.1 < W'.1 →
      W.1.comap (algebraMap K F) = W'.1.comap (algebraMap K F) → isMax W' ∧ ¬ isMax W := by
    intro W W' hlt hc
    refine ⟨fun W'' hW'' hc'' ↦ ?_, fun h ↦ lt_irrefl _ (hlt.trans_le (h W'.1 W'.2 hc.symm))⟩
    rcases le_total (⟨W'', hW''⟩ : {W // V ≤ W}) W' with h | h
    · exact h
    · rcases eq_or_lt_of_le (show W'.1 ≤ W'' from h) with h' | h'
      · exact h'.ge
      · exact (not_comap_eq_of_lt_of_lt htr hlt h' (hc.trans hc''.symm)).elim
  have hΦ : Function.Injective Φ := by
    intro W W' h
    have hc : W.1.comap (algebraMap K F) = W'.1.comap (algebraMap K F) :=
      congrArg Subtype.val (congrArg Prod.fst h)
    have hm : isMax W ↔ isMax W' := Iff.of_eq (congrArg Prod.snd h)
    rcases lt_trichotomy W W' with hlt | heq | hgt
    · exact ((hmax W W' hlt hc).2 (hm.mpr (hmax W W' hlt hc).1)).elim
    · exact heq
    · exact ((hmax W' W hgt hc.symm).2 (hm.mp (hmax W' W hgt hc.symm).1)).elim
  have : Finite {W // V ≤ W} := Finite.of_injective Φ hΦ
  exact Finite.of_equiv _ (ValuationSubring.primeSpectrumEquiv V).symm

end FiniteHeight

/-! ### Heights of induced valuation rings -/

section Decompose

variable {K : Type*} [Field K]

/-- The image `Õ_P` of `O` in the residue field of the coarsening `O_P` is `decompose`. -/
theorem residueSubring_eq_decompose (O : ValuationSubring K) (P : Ideal O) [P.IsPrime] :
    residueSubring O P = decompose (O.ofPrime P) (O.le_ofPrime P) := by
  ext y
  rw [mem_residueSubring_iff, mem_decompose]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, O.le_ofPrime P a.2⟩, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- Every overring of `A` is a coarsening `A.ofPrime Q`. -/
theorem exists_ofPrime_eq {A A₁ : ValuationSubring K} (h : A ≤ A₁) :
    ∃ (Q : Ideal A) (_ : Q.IsPrime), A.ofPrime Q = A₁ :=
  ⟨A.idealOfLE A₁ h, inferInstance, A.ofPrime_idealOfLE A₁ h⟩

/-- The valuation ring induced on the residue field of an overring of a valuation ring of finite
height has finite height. -/
theorem finite_primeSpectrum_decompose {A A₁ : ValuationSubring K} [Finite (PrimeSpectrum A)]
    (h : A ≤ A₁) : Finite (PrimeSpectrum (decompose A₁ h)) := by
  obtain ⟨Q, hQ, rfl⟩ := exists_ofPrime_eq h
  rw [← residueSubring_eq_decompose]
  infer_instance

/-- **The induction on the height** (Temkin, Lemma 2.1.4): the valuation ring induced on the
residue field of a proper coarsening `A₁ ≠ K` of `A` has smaller height than `A`. -/
theorem height_decompose_lt {A A₁ : ValuationSubring K} [Finite (PrimeSpectrum A)]
    (h : A ≤ A₁) (h1 : A₁ ≠ ⊤) : height (decompose A₁ h) < height A := by
  obtain ⟨Q, hQ, rfl⟩ := exists_ofPrime_eq h
  rw [← residueSubring_eq_decompose]
  have hsum := height_ofPrime_add_height_residueSubring A Q
  have hne : height (A.ofPrime Q) ≠ 0 := fun h0 ↦ h1 ((height_eq_zero_iff _).mp h0)
  omega

end Decompose

/-! ### Equal characteristic -/

section Characteristic

variable {K : Type*} [Field K]

/-- **Equal characteristic passes to coarsenings**: if `K` and `κ(A)` have exponential
characteristic `p` and `A ⊆ A₁`, then `κ(A₁)` has exponential characteristic `p`. -/
theorem expChar_residueField_of_le {A A₁ : ValuationSubring K} (h : A ≤ A₁) {p : ℕ}
    [hK : ExpChar K p] [hA : ExpChar (ResidueField A) p] : ExpChar (ResidueField A₁) p := by
  rcases hK with _ | hp
  · have : CharZero (ResidueField A) := charZero_of_expChar_one' (ResidueField A)
    refine @ExpChar.zero _ _ (charZero_of_inj_zero fun n hn ↦ ?_)
    by_contra hn0
    have hA0 : residue A (n : A) ≠ 0 := by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr hn0
    have hu : IsUnit (n : A) := (residue_ne_zero_iff_isUnit _).mp hA0
    have hu₁ : IsUnit (n : A₁) := by
      have := hu.map (ValuationSubring.inclusion A A₁ h)
      rwa [map_natCast] at this
    have := (residue_ne_zero_iff_isUnit _).mpr hu₁
    rw [map_natCast] at this
    exact this hn
  · have : CharP K p := ‹_›
    have : CharP A₁ p := A₁.subtype.charP Subtype.val_injective p
    have := CharP.of_ringHom_of_ne_zero (residue A₁) p hp.ne_zero
    exact ExpChar.prime hp

/-- **Equal characteristic passes to induced valuation rings**: the residue field of the
valuation ring `A/𝔪_{A₁}` of `κ(A₁)` is the residue field of `A`, so it has the exponential
characteristic of `κ(A)`. -/
theorem expChar_residueField_decompose {A A₁ : ValuationSubring K} (h : A ≤ A₁) {p : ℕ}
    [ExpChar (ResidueField A) p] : ExpChar (ResidueField (decompose A₁ h)) p := by
  let φ : A →+* decompose A₁ h :=
    ((residue A₁).comp (ValuationSubring.inclusion A A₁ h)).codRestrict (decompose A₁ h)
      fun a ↦ ⟨⟨a, h a.2⟩, a.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  exact expChar_of_injective_ringHom (ResidueField.map φ).injective p

end Characteristic

end DeJongAlterations.StableModification.Valuation.MainUniformization
