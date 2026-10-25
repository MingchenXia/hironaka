/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.ImmediateDegreeP
import DeJongAlterations.StableModification.Valuation.Analytic.Towers
import DeJongAlterations.StableModification.Valuation.Analytic.Krasner

/-!
# Cosets with `a = 0` and the Frobenius subfield

Let `M` be a non-archimedean normed field of characteristic `p` and `M^p` its subfield of
`p`-th powers (`frobeniusRange M p`). If `M/M^p` is finite and Cartesian, every `b ∈ M` has a
best approximation in `M^p`, so every special coset `b + S_{0,s}(M)` has a minimal element
(Temkin's `CritMin` property for `a = 0`). The Cartesian property holds as soon as
`[M : M^p] ≤ p` and either the residue field of `M` is not perfect or `|M^×|` is not
`p`-divisible; this is how it is used for fields of types 2 and 3 (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of Proposition 6.2.4,
`semi-stable.tex` lines 3951–3964, where it is read off from Schauder bases). Combined with
`ImmediateDegreeP.lean`: such fields have no immediate purely inseparable extension of degree
`p`, and every immediate Artin–Schreier extension has radius `1` (plan node C3 of
`PLAN-SM-VAL.md`).

## Main definitions

* `frobeniusRange M p`: the subfield `M^p`.
* `normedAlgebraSubfield`: a subfield with the restricted norm.

## Main results

* `exists_isMinimalInCoset_zero_of_forall`, `exists_isMinimalInCoset_zero_of_isCartesian`.
* `le_inertiaDegree_frobeniusRange`, `le_ramificationIndex_frobeniusRange`,
  `isCartesian_frobeniusRange_of_residue`, `isCartesian_frobeniusRange_of_norm`.
* `IsImmediate.not_pow_char_mem_of_critMinZero`, `IsImmediate.radius_eq_one_of_critMinZero`.

## References

Blueprint chapter `sm-val-cosets-ramif.tex`: `lem:sm-an-frobenius-cartesian`,
`lem:sm-an-critmin-zero`.
-/

noncomputable section

open IsLocalRing Polynomial IntermediateField
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### Subfields as normed fields -/

/-- A subfield `S` of a normed field `M` with the restricted norm: `M` is a normed `S`-algebra. -/
instance normedAlgebraSubfield {M : Type*} [NormedField M] (S : Subfield M) :
    NormedAlgebra S M where
  norm_smul_le c x := by
    rw [Algebra.smul_def, norm_mul]
    exact le_rfl

/-! ### The Frobenius subfield -/

section Frobenius

variable (M : Type*) [Field M] (p : ℕ) [hp : Fact p.Prime] [CharP M p]

/-- The subfield `M^p = {c ^ p}` of `p`-th powers. -/
def frobeniusRange : Subfield M := (frobenius M p).fieldRange

variable {M p}

theorem mem_frobeniusRange {x : M} : x ∈ frobeniusRange M p ↔ ∃ c : M, c ^ p = x := by
  rw [frobeniusRange, RingHom.mem_fieldRange]
  simp [frobenius_def]

theorem pow_mem_frobeniusRange (c : M) : c ^ p ∈ frobeniusRange M p :=
  mem_frobeniusRange.mpr ⟨c, rfl⟩

/-- The residue field of a field of characteristic `p` has characteristic `p`. -/
theorem charP_residueField {M : Type*} [NormedField M] [IsUltrametricDist M] [CharP M p] :
    CharP (ResidueField (unitBall M)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp.out]
  have h0 : ((p : unitBall M) : M) = 0 := by simp
  have : (p : unitBall M) = 0 := Subtype.ext (by rw [h0]; rfl)
  rw [← map_natCast (residue (unitBall M)), this, map_zero]

/-- **The Frobenius degree is invariant under finite extensions**: if `M/K` is finite, then
`[M : M^p] = [K : K^p]` (both read as `0` if infinite). -/
theorem finrank_frobeniusRange_eq_of_finiteDimensional {K : Type*} [Field K] [CharP K p]
    [Algebra K M] [FiniteDimensional K M] :
    Module.finrank (frobeniusRange M p) M = Module.finrank (frobeniusRange K p) K := by
  set f := algebraMap K M
  set K' := f.fieldRange
  set A := frobeniusRange M p
  set B := (frobeniusRange K p).map f
  have hBA : B ≤ A := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨d, rfl⟩ := mem_frobeniusRange.mp hc
    rw [map_pow]
    exact pow_mem_frobeniusRange _
  have hBK' : B ≤ K' := by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩
  have hK'map : K'.map (frobenius M p) = B := by
    ext x
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c ^ p, pow_mem_frobeniusRange c, by simp [frobenius_def, f]⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨d, rfl⟩ := mem_frobeniusRange.mp hc
      exact ⟨f d, ⟨d, rfl⟩, by simp [frobenius_def, f]⟩
  have htopmap : (⊤ : Subfield M).map (frobenius M p) = A := by
    rw [← RingHom.fieldRange_eq_map]
    rfl
  have e1 : B.relfinrank A = K'.relfinrank ⊤ := by
    rw [← hK'map, ← htopmap, Subfield.relfinrank_map_map]
  have e2 := Subfield.relfinrank_mul_relfinrank hBA (le_top : A ≤ ⊤)
  have e3 := Subfield.relfinrank_mul_relfinrank hBK' (le_top : K' ≤ ⊤)
  have e4 : B.relfinrank K' = (frobeniusRange K p).relfinrank ⊤ := by
    rw [← Subfield.relfinrank_map_map (frobeniusRange K p) ⊤ f, ← RingHom.fieldRange_eq_map]
  have e7 : K'.relfinrank ⊤ = Module.finrank K M := by
    rw [Subfield.relfinrank_top_right]
    refine (Algebra.finrank_eq_of_equiv_equiv (f.rangeRestrictFieldEquiv) (RingEquiv.refl M)
      (RingHom.ext fun c => rfl)).symm
  have hpos : 0 < Module.finrank K M := Module.finrank_pos
  rw [← Subfield.relfinrank_top_right, ← Subfield.relfinrank_top_right, ← e4]
  rw [e1, e7] at e2
  rw [e7] at e3
  have := e2.trans e3.symm
  rw [mul_comm] at this
  exact (Nat.eq_of_mul_eq_mul_right hpos this)

end Frobenius

/-! ### The Frobenius degree of a field topologically generated by one element -/

section Dense

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] (p : ℕ) [hp : Fact p.Prime]
  [CharP K p]

/-- In a complete field of characteristic `p`, the subfield `K^p` is closed. -/
theorem isClosed_frobeniusRange : IsClosed (frobeniusRange K p : Set K) := by
  have : (frobeniusRange K p : Set K) = Set.range fun x : K => x ^ p := by
    ext x
    exact mem_frobeniusRange
  rw [this]
  exact (isUniformInducing_pow_char p).isComplete_range.isClosed

/-- `K^p` is a nontrivially normed field with the restricted norm. -/
@[implicit_reducible]
def frobeniusRangeNontriviallyNormedField : NontriviallyNormedField (frobeniusRange K p) :=
  { (inferInstance : NormedField (frobeniusRange K p)) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      refine ⟨⟨x ^ p, pow_mem_frobeniusRange x⟩, ?_⟩
      change 1 < ‖x ^ p‖
      rw [norm_pow]
      exact one_lt_pow₀ hx hp.out.ne_zero }

/-- **The Frobenius degree of `\overline{k(y)}`** (the bound `[K : K^p] ≤ p` used for
one-dimensional fields; plan node C3 via A5): if `K` is complete of characteristic `p` and
`k(y)` is dense in `K` for a perfect subfield `k`, then `0 < [K : K^p] ≤ p`. -/
theorem finrank_frobeniusRange_le_of_dense {k : Type*} [Field k] [Algebra k K]
    (hk : ∀ c : k, ∃ d : k, d ^ p = c) {y : K}
    (hy : Dense (IntermediateField.adjoin k {y} : Set K)) :
    0 < Module.finrank (frobeniusRange K p) K ∧ Module.finrank (frobeniusRange K p) K ≤ p := by
  set F := frobeniusRange K p
  let := frobeniusRangeNontriviallyNormedField (K := K) p
  have : CompleteSpace F := (isClosed_frobeniusRange p).completeSpace_coe
  set c₀ : F := ⟨y ^ p, pow_mem_frobeniusRange y⟩
  have hmonic : (X ^ p - C c₀ : F[X]).Monic := monic_X_pow_sub_C c₀ hp.out.ne_zero
  have hroot : aeval y (X ^ p - C c₀ : F[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr rfl
  have hint : IsIntegral F y := ⟨_, hmonic, by rwa [← aeval_def]⟩
  have hcl : IsClosed (F⟮y⟯ : Set K) := isClosed_adjoin_simple hint
  -- `k(y) ⊆ F(y)`
  have hsub : (IntermediateField.adjoin k {y} : Set K) ⊆ F⟮y⟯ := by
    have : (IntermediateField.adjoin k {y}).toSubfield ≤ (F⟮y⟯).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨c, rfl⟩ | hy')
      · obtain ⟨d, rfl⟩ := hk c
        rw [map_pow]
        exact (F⟮y⟯).algebraMap_mem ⟨_, pow_mem_frobeniusRange _⟩
      · rw [Set.mem_singleton_iff.mp hy']
        exact mem_adjoin_simple_self F y
    exact this
  have htop : F⟮y⟯ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ closure (IntermediateField.adjoin k {y} : Set K) := by
      rw [hy.closure_eq]
      trivial
    exact closure_minimal hsub hcl hx
  have hfin : Module.finrank F K = (minpoly F y).natDegree := by
    rw [← IntermediateField.finrank_top', ← htop, adjoin.finrank hint]
  refine ⟨hfin ▸ minpoly.natDegree_pos hint, ?_⟩
  rw [hfin]
  have := natDegree_le_of_dvd (minpoly.dvd F y hroot) hmonic.ne_zero
  rwa [natDegree_X_pow_sub_C] at this

/-- The Frobenius degree of a finite extension `M` of `\overline{k(y)}`: `0 < [M : M^p] ≤ p`. -/
theorem finrank_frobeniusRange_le_of_finiteDimensional_of_dense {k : Type*} [Field k]
    [Algebra k K] (hk : ∀ c : k, ∃ d : k, d ^ p = c) {y : K}
    (hy : Dense (IntermediateField.adjoin k {y} : Set K)) {M : Type*} [Field M] [CharP M p]
    [Algebra K M] [FiniteDimensional K M] :
    0 < Module.finrank (frobeniusRange M p) M ∧ Module.finrank (frobeniusRange M p) M ≤ p := by
  rw [finrank_frobeniusRange_eq_of_finiteDimensional (K := K)]
  exact finrank_frobeniusRange_le_of_dense p hk hy

end Dense

/-! ### Minimal elements of cosets with `a = 0` -/

section CritMin

variable {M : Type*} [NormedField M] [IsUltrametricDist M] (p : ℕ) [hp : Fact p.Prime]
  [CharP M p]

/-- **Cosets with `a = 0` attain their infimum**: if every `b ∈ M` has a best approximation in
`M^p`, every special coset `b + S_{0,s}(M)` has a minimal element. -/
theorem exists_isMinimalInCoset_zero_of_forall
    (hbest : ∀ b : M, ∃ c₀ : M, ∀ c : M, ‖b - c₀ ^ p‖ ≤ ‖b - c ^ p‖) {s : ℝ} {b : M}
    (h : IsSpecialCoset p 0 s b) : ∃ x, IsMinimalInCoset p 0 s b x := by
  obtain ⟨c₀, hc₀⟩ := hbest b
  refine ⟨b - c₀ ^ p, h.isMinimalInCoset_of_orthogonal ?_ fun c => ?_⟩
  · have := (memCoset_self (a := (0 : M)) (p := p) h.1.pos b).add_asMap (-c₀)
    rwa [asMap_neg, asMap_zero_left, ← sub_eq_add_neg] at this
  · have := hc₀ (c₀ - c)
    rw [sub_pow_char] at this
    calc ‖b - c₀ ^ p‖ ≤ ‖b - (c₀ ^ p - c ^ p)‖ := this
      _ = ‖b - c₀ ^ p + c ^ p‖ := by ring_nf

/-- If `M/M^p` is finite and Cartesian, every special coset `b + S_{0,s}(M)` has a minimal
element. -/
theorem exists_isMinimalInCoset_zero_of_isCartesian
    [FiniteDimensional (frobeniusRange M p) M] (hcart : IsCartesian (frobeniusRange M p) M)
    {s : ℝ} {b : M} (h : IsSpecialCoset p 0 s b) : ∃ x, IsMinimalInCoset p 0 s b x := by
  refine exists_isMinimalInCoset_zero_of_forall p (fun b => ?_) h
  obtain ⟨c, hc⟩ := hcart.exists_forall_norm_sub_le b
  obtain ⟨c₀, hc₀⟩ := mem_frobeniusRange.mp c.2
  refine ⟨c₀, fun c' => ?_⟩
  have := hc ⟨c' ^ p, pow_mem_frobeniusRange c'⟩
  have e1 : algebraMap (frobeniusRange M p) M c = c₀ ^ p := hc₀.symm
  have e2 : algebraMap (frobeniusRange M p) M ⟨c' ^ p, pow_mem_frobeniusRange c'⟩ = c' ^ p := rfl
  rwa [e1, e2] at this

end CritMin

/-! ### The Cartesian property of `M / M^p` -/

section Cartesian

variable {M : Type*} [NormedField M] [IsUltrametricDist M] (p : ℕ) [hp : Fact p.Prime]
  [CharP M p] [FiniteDimensional (frobeniusRange M p) M]

/-- If the residue `ũ` of some `u ∈ M°` is not a `p`-th power in `M̃`, then
`f_{M/M^p} ≥ p`. -/
theorem le_inertiaDegree_frobeniusRange {u : M} (hu : ‖u‖ ≤ 1)
    (hres : ∀ c : ResidueField (unitBall M),
      c ^ p ≠ residue (unitBall M) ⟨u, mem_unitBall.mpr hu⟩) :
    p ≤ inertiaDegree (frobeniusRange M p) M := by
  have : CharP (ResidueField (unitBall M)) p := charP_residueField
  set F := frobeniusRange M p
  set ũ := residue (unitBall M) ⟨u, mem_unitBall.mpr hu⟩ with hũ
  have hnot : ũ ∉ (algebraMap (ResidueField (unitBall F)) (ResidueField (unitBall M))).range := by
    rintro ⟨w, hw⟩
    obtain ⟨f, rfl⟩ := residue_surjective w
    obtain ⟨d, hd⟩ := mem_frobeniusRange.mp (f : F).2
    have hd1 : ‖d‖ ≤ 1 := by
      have : ‖d‖ ^ p ≤ 1 := by
        rw [← norm_pow, hd]
        exact norm_coe_unitBall_le_one f
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp this
    apply hres (residue (unitBall M) ⟨d, mem_unitBall.mpr hd1⟩)
    rw [← map_pow, ← hw, algebraMap_residue]
    congr 1
    apply Subtype.ext
    simp only [coe_algebraMap_unitBall, SubmonoidClass.coe_pow]
    exact hd
  have hpow : algebraMap (ResidueField (unitBall F)) (ResidueField (unitBall M))
      (residue (unitBall F) ⟨⟨u ^ p, pow_mem_frobeniusRange u⟩, by
        rw [mem_unitBall]
        change ‖u ^ p‖ ≤ 1
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hu⟩) = ũ ^ p := by
    rw [algebraMap_residue, hũ, ← map_pow]
    rfl
  have hdeg := finrank_adjoin_of_pow_char_mem p hnot hpow
  have hint : IsIntegral (ResidueField (unitBall F)) ũ := Algebra.IsIntegral.isIntegral _
  rw [adjoin.finrank hint] at hdeg
  rw [← hdeg, inertiaDegree_def]
  exact minpoly.natDegree_le _

/-- If `‖z‖` is not the `p`-th power of an absolute value of `M`, then `e_{M/M^p} ≥ p`. -/
theorem le_ramificationIndex_frobeniusRange {z : M} (hz0 : z ≠ 0)
    (hz : ∀ c : M, ‖c‖ ^ p ≠ ‖z‖) : p ≤ ramificationIndex (frobeniusRange M p) M := by
  classical
  set F := frobeniusRange M p
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set zu : Mˣ := Units.mk0 z hz0
  set g : Fin p → ValueGroupQuotient F M := fun i => valueClass F M (zu ^ (i : ℕ))
  have hginj : Function.Injective g := by
    -- the classes of `‖z‖ ^ i`, `i < p`, are distinct
    have key : ∀ i j : ℕ, i < j → j < p → valueClass F M (zu ^ i) ≠ valueClass F M (zu ^ j) := by
      intro i j hij hjp h
      obtain ⟨c, hc⟩ := valueClass_eq_valueClass_iff.mp h
      obtain ⟨d, hd⟩ := mem_frobeniusRange.mp (c : F).2
      have hzu : (zu : M) = z := rfl
      simp only [Units.val_pow_eq_pow_val, norm_pow, hzu] at hc
      -- `‖z‖ ^ (j - i) = ‖d‖ ^ p`
      have hcn : ‖(c : F)‖ = ‖d‖ ^ p := by
        change ‖((c : F) : M)‖ = _
        rw [← hd, norm_pow]
      have hn : ‖z‖ ^ (j - i) = ‖d‖ ^ p := by
        rw [← hcn]
        have : ‖z‖ ^ j = ‖z‖ ^ (j - i) * ‖z‖ ^ i := by
          rw [← pow_add, Nat.sub_add_cancel hij.le]
        rw [this] at hc
        exact mul_right_cancel₀ (pow_pos hzpos i).ne' hc
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [norm_zero, zero_pow hp.out.ne_zero] at hn
        exact (pow_pos hzpos _).ne' hn
      -- Bezout
      have hcop : Nat.Coprime (j - i) p :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
          (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      apply hz (d ^ a * z ^ b)
      rw [norm_mul, norm_zpow, norm_zpow, mul_pow, ← zpow_natCast, ← zpow_natCast (‖z‖ ^ b),
        ← zpow_mul, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, ← hn, ← zpow_natCast,
        ← zpow_mul, ← zpow_add₀ hzpos.ne']
      conv_rhs => rw [← zpow_one ‖z‖]
      congr 1
      linarith
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact key i j hlt j.2 hij
    · exact key j i hlt i.2 hij.symm
  have := Fintype.ofFinite (ValueGroupQuotient F M)
  have hcard := Fintype.card_le_of_injective g hginj
  rw [Fintype.card_fin] at hcard
  rw [ramificationIndex_eq_card, Nat.card_eq_fintype_card]
  exact hcard

/-- **`M / M^p` is Cartesian** if `[M : M^p] ≤ p` and the residue field is not perfect. -/
theorem isCartesian_frobeniusRange_of_residue (hdeg : Module.finrank (frobeniusRange M p) M ≤ p)
    {u : M} (hu : ‖u‖ ≤ 1)
    (hres : ∀ c : ResidueField (unitBall M),
      c ^ p ≠ residue (unitBall M) ⟨u, mem_unitBall.mpr hu⟩) :
    IsCartesian (frobeniusRange M p) M := by
  have h1 := le_inertiaDegree_frobeniusRange p hu hres
  have h2 := ramificationIndex_mul_inertiaDegree_le (K := frobeniusRange M p) (L := M)
  have h3 := ramificationIndex_pos (K := frobeniusRange M p) (L := M)
  unfold IsCartesian
  nlinarith

/-- **`M / M^p` is Cartesian** if `[M : M^p] ≤ p` and `|M^×|` is not `p`-divisible. -/
theorem isCartesian_frobeniusRange_of_norm (hdeg : Module.finrank (frobeniusRange M p) M ≤ p)
    {z : M} (hz0 : z ≠ 0) (hz : ∀ c : M, ‖c‖ ^ p ≠ ‖z‖) :
    IsCartesian (frobeniusRange M p) M := by
  have h1 := le_ramificationIndex_frobeniusRange p hz0 hz
  have h2 := ramificationIndex_mul_inertiaDegree_le (K := frobeniusRange M p) (L := M)
  have h3 : 0 < inertiaDegree (frobeniusRange M p) M := by
    rw [inertiaDegree_def]
    exact Module.finrank_pos
  unfold IsCartesian
  nlinarith

end Cartesian

/-! ### Consequences for immediate extensions -/

section Immediate

variable {M L : Type*} [NormedField M] [IsUltrametricDist M] [CompleteSpace M] [NormedField L]
  [IsUltrametricDist L] [NormedAlgebra M L] (p : ℕ) [hp : Fact p.Prime] [CharP M p]

/-- If every special coset `b + S_{0,s}(M)` has a minimal element, an immediate extension of
`M` contains no `γ ∉ M` with `γ ^ p ∈ M`. -/
theorem IsImmediate.not_pow_char_mem_of_critMinZero
    (hcm : ∀ (s : ℝ) (b : M), IsSpecialCoset p 0 s b → ∃ x, IsMinimalInCoset p 0 s b x)
    (h : IsImmediate M L) {γ : L} (hγ : γ ∉ Set.range (algebraMap M L)) :
    γ ^ p ∉ Set.range (algebraMap M L) := by
  rintro ⟨β, hβ⟩
  obtain ⟨h1, h2, -⟩ := h.isSpecialCoset_pow_char p hγ hβ
  exact h2 (hcm _ _ h1)

/-- If every special coset `b + S_{0,s}(M)` has a minimal element, every immediate
Artin–Schreier step `α ^ p - α ∈ M` has radius `1`; then `-(α ^ p - α) + S_{1,1}(M)` is special,
has no minimal element, and splits over `L` (`IsImmediate.isSpecialCoset_artinSchreier_one`). -/
theorem IsImmediate.radius_eq_one_of_critMinZero
    (hcm : ∀ (s : ℝ) (b : M), IsSpecialCoset p 0 s b → ∃ x, IsMinimalInCoset p 0 s b x)
    (h : IsImmediate M L) {α : L} (hα : α ∉ Set.range (algebraMap M L)) {β : M}
    (hβ : algebraMap M L β = α ^ p - α) : radius M α = 1 := by
  obtain ⟨hr1, -⟩ := one_le_radius_of_artinSchreier p hα hβ
  refine le_antisymm (not_lt.mp fun hr => ?_) hr1
  have hlt : radius M α < radius M α ^ p := lt_self_pow₀ hr (Fact.out : p.Prime).one_lt
  obtain ⟨c₀, hc₀⟩ := exists_norm_sub_lt_of_radius_lt hlt
  obtain ⟨h1, h2, -⟩ := h.isSpecialCoset_artinSchreier_zero p hα hβ hc₀
  exact h2 (hcm _ _ h1)

end Immediate

end DeJongAlterations.StableModification.Valuation.Analytic
