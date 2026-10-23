import DeJongAlterations.StableModification.Abhyankar
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Valuation rings of finite height and their coarsenings

This file formalizes the elementary height theory of valuation rings of Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.1 (`semi-stable.tex`, lines
1886–1902 and 1955–1983): the height of a valuation ring, the coarsening at a prime and the
valuation ring induced on its residue field, the additivity of heights, and the existence of the
height-one coarsening that drives the induction on height in the proof of Theorem 2.1.8
(`valunif`, lines 2205–2232). Blueprint chapter `sm-val-basic-vb.tex`.

## Main definitions

* `height O`: Temkin's height `#Spec O - 1` of a valuation subring `O` of a field `K` (a natural
  number; it is meaningful when `Spec O` is finite, which we assume as
  `[Finite (PrimeSpectrum O)]`).
* `residueSubring O P`: for a prime `P` of `O`, the image `Õ_P` of `O` in the residue field of the
  coarsening `O.ofPrime P = O_P`; it is a valuation subring of `κ(O_P)`.
* `toResidueSubring O P : O →+* residueSubring O P`, the surjection with kernel `P`.

## Main results

* `primeSpectrum_le_total`: the primes of a valuation ring form a chain.
* `krullDim_eq_of_card_eq`, `krullDim_eq_top_of_infinite`: Krull dimension of chains.
* `finite_primeSpectrum_iff_ringKrullDim_ne_top`, `ringKrullDim_eq_height`: finite height is
  finite Krull dimension, and the height is the Krull dimension.
* `height_eq_zero_iff`: height zero means `O = K`.
* `finite_primeSpectrum_of_trdeg_eq`, `height_le_of_trdeg_eq`: a valuation ring containing a
  subfield `k₀` with `trdeg (K/k₀) = d` has finite height at most `d` (from
  `ringKrullDim_le_of_trdeg_eq` of `Abhyankar.lean`).
* `mem_iff_residue_mem_residueSubring`: `O` is composed from `O_P` and `Õ_P`.
* `primeSpectrumOfPrimeOrderIso`, `primeSpectrumResidueSubringOrderIso`: the spectra of `O_P` and
  `Õ_P` are the primes below and above `P`.
* `height_ofPrime_add_height_residueSubring`: `ht O_P + ht Õ_P = ht O`.
* `exists_height_ofPrime_eq_one`: the height-one coarsening.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation

section Order

variable {α : Type*} [PartialOrder α]

/-- A totally ordered set with exactly `n + 1` elements has Krull dimension `n`. -/
theorem krullDim_eq_of_card_eq [Fintype α] (htot : ∀ a b : α, a ≤ b ∨ b ≤ a) {n : ℕ}
    (hcard : Fintype.card α = n + 1) : Order.krullDim α = n := by
  apply le_antisymm
  · rw [Order.krullDim]
    refine iSup_le fun p ↦ ?_
    have := p.length_lt_card
    exact_mod_cast (by omega : p.length ≤ n)
  · let _ : LinearOrder α :=
      { (inferInstance : PartialOrder α) with
        le_total := htot
        toDecidableLE := Classical.decRel _ }
    let e := Fintype.orderIsoFinOfCardEq α hcard
    exact Order.le_krullDim_iff.mpr ⟨LTSeries.mk n (fun i ↦ e i) fun _ _ h ↦ e.strictMono h, rfl⟩

/-- An infinite totally ordered set has infinite Krull dimension. -/
theorem krullDim_eq_top_of_infinite [Infinite α] (htot : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    Order.krullDim α = ⊤ := by
  let _ : LinearOrder α :=
    { (inferInstance : PartialOrder α) with
      le_total := htot
      toDecidableLE := Classical.decRel _ }
  have : InfiniteDimensionalOrder α := by
    refine ⟨fun n ↦ ?_⟩
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (n + 1)
    let e := s.orderIsoOfFin hs
    exact ⟨LTSeries.mk n (fun i ↦ (e i : α)) fun _ _ h ↦ e.strictMono h, rfl⟩
  exact Order.krullDim_eq_top

end Order

variable {K : Type*} [Field K] (O : ValuationSubring K)

section Height

/-- The prime ideals of a valuation ring are totally ordered (Temkin, lines 1899–1902). -/
theorem primeSpectrum_le_total (p q : PrimeSpectrum O) : p ≤ q ∨ q ≤ p :=
  (ValuationRing.le_total_ideal (A := O)).total p.asIdeal q.asIdeal

/-- The maximal ideal of a valuation subring is zero if and only if it is the whole field. -/
theorem maximalIdeal_eq_bot_iff : maximalIdeal O = ⊥ ↔ O = ⊤ := by
  constructor
  · intro h
    refine top_unique fun x _ ↦ ?_
    by_contra hx
    have hnu : x⁻¹ ∈ O.nonunits := O.inv_mem_nonunits_iff.mpr (Or.inr hx)
    obtain ⟨hmem, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnu
    rw [h, Ideal.mem_bot] at hm
    have h0 : x⁻¹ = 0 := congrArg Subtype.val hm
    rw [inv_eq_zero] at h0
    exact hx (h0 ▸ O.zero_mem)
  · rintro rfl
    refine (Submodule.eq_bot_iff _).mpr fun a ha ↦ ?_
    have h := ValuationSubring.coe_mem_nonunits_iff.mpr ha
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    rcases h with h | h
    · exact Subtype.ext h
    · exact absurd (ValuationSubring.mem_top _) h

/-- A valuation subring is a field if and only if it is the whole field. -/
theorem isField_iff_eq_top : IsField O ↔ O = ⊤ := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, maximalIdeal_eq_bot_iff]

/-- A valuation ring has finite height (finitely many primes) if and only if its Krull dimension
is finite. -/
theorem finite_primeSpectrum_iff_ringKrullDim_ne_top :
    Finite (PrimeSpectrum O) ↔ ringKrullDim O ≠ ⊤ := by
  constructor
  · intro h
    have := Fintype.ofFinite (PrimeSpectrum O)
    have hpos : 0 < Fintype.card (PrimeSpectrum O) := Fintype.card_pos
    rw [ringKrullDim, krullDim_eq_of_card_eq (primeSpectrum_le_total O)
      (n := Fintype.card (PrimeSpectrum O) - 1) (by omega)]
    exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  · intro h
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact h (krullDim_eq_top_of_infinite (primeSpectrum_le_total O))

/-- The height of a valuation ring (Temkin, line 1891): the number of its primes minus one.
It is meaningful when `Spec O` is finite (`[Finite (PrimeSpectrum O)]`); then it is the Krull
dimension (`ringKrullDim_eq_height`). -/
def height : ℕ :=
  Nat.card (PrimeSpectrum O) - 1

/-- A valuation ring of finite height `h` has `h + 1` primes. -/
theorem natCard_primeSpectrum_eq_height_add_one [Finite (PrimeSpectrum O)] :
    Nat.card (PrimeSpectrum O) = height O + 1 := by
  have : 0 < Nat.card (PrimeSpectrum O) := Nat.card_pos
  unfold height
  omega

/-- For a valuation ring of finite height, the height is the Krull dimension. -/
theorem ringKrullDim_eq_height [Finite (PrimeSpectrum O)] : ringKrullDim O = height O := by
  have := Fintype.ofFinite (PrimeSpectrum O)
  exact krullDim_eq_of_card_eq (primeSpectrum_le_total O)
    (by rw [← Nat.card_eq_fintype_card]; exact natCard_primeSpectrum_eq_height_add_one O)

/-- A valuation ring of finite height has height zero if and only if it is the whole field. -/
theorem height_eq_zero_iff [Finite (PrimeSpectrum O)] : height O = 0 ↔ O = ⊤ := by
  rw [← isField_iff_eq_top, ← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
  have h := natCard_primeSpectrum_eq_height_add_one O
  constructor
  · intro h0
    rw [h0, zero_add, Nat.card_eq_one_iff_unique] at h
    exact h.1
  · intro hs
    have : Nat.card (PrimeSpectrum O) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
    omega

/-- **Finite height over a trivially valued subfield** (relative form of Temkin,
Corollary 2.1.3(i)): a valuation ring containing a subfield `k₀` with `trdeg (K/k₀) = d` has
finitely many primes. -/
theorem finite_primeSpectrum_of_trdeg_eq {k₀ : Type*} [Field k₀] [Algebra k₀ K]
    (hO : ∀ x : k₀, algebraMap k₀ K x ∈ O) {d : ℕ} (hd : Algebra.trdeg k₀ K = d) :
    Finite (PrimeSpectrum O) := by
  rw [finite_primeSpectrum_iff_ringKrullDim_ne_top]
  have h := ringKrullDim_le_of_trdeg_eq O hO hd
  exact ne_top_of_le_ne_top (ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))) h

/-- A valuation ring containing a subfield `k₀` with `trdeg (K/k₀) = d` has height at most `d`. -/
theorem height_le_of_trdeg_eq {k₀ : Type*} [Field k₀] [Algebra k₀ K]
    (hO : ∀ x : k₀, algebraMap k₀ K x ∈ O) {d : ℕ} (hd : Algebra.trdeg k₀ K = d) :
    height O ≤ d := by
  have := finite_primeSpectrum_of_trdeg_eq O hO hd
  have h := ringKrullDim_le_of_trdeg_eq O hO hd
  rw [ringKrullDim_eq_height] at h
  exact_mod_cast h

end Height

section Coarsening

variable (P : Ideal O) [P.IsPrime]

/-- The residue map `O → κ(O_P)` of the coarsening `O_P = O.ofPrime P`. -/
def residueOfPrime : O →+* ResidueField (O.ofPrime P) :=
  (residue (O.ofPrime P)).comp (O.inclusion _ (O.le_ofPrime P))

/-- The residue map evaluated at `a ∈ O`. -/
theorem residueOfPrime_apply (a : O) :
    residueOfPrime O P a = residue (O.ofPrime P) ⟨a, O.le_ofPrime P a.2⟩ :=
  rfl

/-- **The valuation ring induced on the residue field of a coarsening** (Temkin, Lemma 2.1.4(i)):
the image `Õ_P` of `O` in the residue field `κ(O_P)` of the coarsening `O_P = O.ofPrime P` is a
valuation subring of `κ(O_P)`. -/
def residueSubring : ValuationSubring (ResidueField (O.ofPrime P)) :=
  ValuationSubring.ofSubring (residueOfPrime O P).range fun x ↦ by
    obtain ⟨y, rfl⟩ := residue_surjective x
    rcases O.mem_or_inv_mem (y : K) with hy | hy
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · by_cases hy0 : (y : K) = 0
      · left
        have : y = 0 := Subtype.ext hy0
        rw [this, map_zero]
        exact Subring.zero_mem _
      · right
        refine ⟨⟨(y : K)⁻¹, hy⟩, ?_⟩
        rw [residueOfPrime_apply]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul]
        have : (⟨(y : K)⁻¹, O.le_ofPrime P hy⟩ : O.ofPrime P) * y = 1 :=
          Subtype.ext (inv_mul_cancel₀ hy0)
        rw [this, map_one]

/-- The elements of `Õ_P` are the residues of elements of `O`. -/
theorem mem_residueSubring_iff {x : ResidueField (O.ofPrime P)} :
    x ∈ residueSubring O P ↔ ∃ a : O, residueOfPrime O P a = x :=
  Iff.rfl

/-- The surjection `O → Õ_P`, with kernel `P` (`ker_toResidueSubring`). -/
def toResidueSubring : O →+* residueSubring O P :=
  (residueOfPrime O P).codRestrict (residueSubring O P) fun a ↦ ⟨a, rfl⟩

@[simp]
theorem coe_toResidueSubring (a : O) :
    (toResidueSubring O P a : ResidueField (O.ofPrime P)) = residueOfPrime O P a :=
  rfl

/-- `O → Õ_P` is surjective. -/
theorem toResidueSubring_surjective : Function.Surjective (toResidueSubring O P) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

/-- The kernel of `O → Õ_P` is `P`: the maximal ideal of `O_P` meets `O` in `P`. -/
theorem ker_toResidueSubring : RingHom.ker (toResidueSubring O P) = P := by
  ext a
  rw [RingHom.mem_ker]
  conv_rhs => rw [← O.idealOfLE_ofPrime P]
  rw [ValuationSubring.idealOfLE, Ideal.mem_comap, ← residue_eq_zero_iff, ← Subtype.coe_inj,
    coe_toResidueSubring, residueOfPrime_apply]
  rfl

/-- The maximal ideal of an overring `A ⊇ O` is contained in `O`. -/
theorem coe_mem_of_mem_maximalIdeal {A : ValuationSubring K} (hA : O ≤ A) {y : A}
    (hy : y ∈ maximalIdeal A) : (y : K) ∈ O := by
  have h1 : (y : K) ∈ A.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hy
  exact O.nonunits_subset (ValuationSubring.nonunits_le_nonunits.mpr hA h1)

/-- **`O` is composed from `O_P` and `Õ_P`** (Temkin, Lemma 2.1.4(i)): an element of `K` lies in
`O` if and only if it lies in `O_P` and its residue lies in `Õ_P`. -/
theorem mem_iff_residue_mem_residueSubring (x : K) :
    x ∈ O ↔ ∃ h : x ∈ O.ofPrime P, residue (O.ofPrime P) ⟨x, h⟩ ∈ residueSubring O P := by
  constructor
  · intro hx
    exact ⟨O.le_ofPrime P hx, ⟨⟨x, hx⟩, rfl⟩⟩
  · rintro ⟨h, a, ha⟩
    rw [residueOfPrime_apply, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
    have hz := coe_mem_of_mem_maximalIdeal O (O.le_ofPrime P) ha
    have : x = (x - a) + a := by ring
    rw [this]
    exact O.add_mem _ _ hz a.2

/-- The primes of the coarsening `O_P` are the primes of `O` contained in `P`. -/
def primeSpectrumOfPrimeOrderIso :
    PrimeSpectrum (O.ofPrime P) ≃o Set.Iic (⟨P, ‹_›⟩ : PrimeSpectrum O) :=
  IsLocalization.AtPrime.primeSpectrumOrderIso (O.ofPrime P) P

/-- The primes of `Õ_P ≅ O/P` are the primes of `O` containing `P`. -/
def primeSpectrumResidueSubringOrderIso :
    PrimeSpectrum (residueSubring O P) ≃o PrimeSpectrum.zeroLocus (P : Set O) :=
  Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (toResidueSubring O P)
    (toResidueSubring_surjective O P) (ker_toResidueSubring O P)

/-- A coarsening of a valuation ring of finite height has finite height. -/
instance finite_primeSpectrum_ofPrime [Finite (PrimeSpectrum O)] :
    Finite (PrimeSpectrum (O.ofPrime P)) :=
  Finite.of_equiv _ (primeSpectrumOfPrimeOrderIso O P).toEquiv.symm

/-- The valuation ring induced on the residue field of a coarsening of a valuation ring of finite
height has finite height. -/
instance finite_primeSpectrum_residueSubring [Finite (PrimeSpectrum O)] :
    Finite (PrimeSpectrum (residueSubring O P)) :=
  Finite.of_equiv _ (primeSpectrumResidueSubringOrderIso O P).toEquiv.symm

/-- The primes containing `P` form the interval `[P, ∞)` of `Spec O`. -/
theorem zeroLocus_eq_Ici :
    PrimeSpectrum.zeroLocus (P : Set O) = Set.Ici (⟨P, ‹_›⟩ : PrimeSpectrum O) := by
  ext q
  rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
  rfl

/-- **Additivity of heights** (Temkin, Lemma 2.1.4): `ht O = ht O_P + ht Õ_P`. -/
theorem height_ofPrime_add_height_residueSubring [Finite (PrimeSpectrum O)] :
    height (O.ofPrime P) + height (residueSubring O P) = height O := by
  set p : PrimeSpectrum O := ⟨P, ‹_›⟩
  have h₁ : Nat.card (PrimeSpectrum (O.ofPrime P)) = (Set.Iic p).ncard := by
    rw [Nat.card_congr (primeSpectrumOfPrimeOrderIso O P).toEquiv, Nat.card_coe_set_eq]
  have h₂ : Nat.card (PrimeSpectrum (residueSubring O P)) = (Set.Ici p).ncard := by
    rw [Nat.card_congr (primeSpectrumResidueSubringOrderIso O P).toEquiv, zeroLocus_eq_Ici,
      Nat.card_coe_set_eq]
  have hunion : Set.Iic p ∪ Set.Ici p = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    exact primeSpectrum_le_total O q p
  have hinter : Set.Iic p ∩ Set.Ici p = {p} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_singleton_iff]
    exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩
  have hcard := Set.ncard_union_add_ncard_inter (Set.Iic p) (Set.Ici p)
  rw [hunion, hinter, Set.ncard_univ, Set.ncard_singleton, ← h₁, ← h₂,
    natCard_primeSpectrum_eq_height_add_one, natCard_primeSpectrum_eq_height_add_one,
    natCard_primeSpectrum_eq_height_add_one] at hcard
  omega

/-- The coarsening `O_P` is the whole field if and only if `P = 0`. -/
theorem ofPrime_eq_top_iff : O.ofPrime P = ⊤ ↔ P = ⊥ := by
  constructor
  · intro h
    have key : ∀ (S : ValuationSubring K) (hS : O ≤ S), S = ⊤ → O.idealOfLE S hS = ⊥ := by
      rintro S hS rfl
      exact O.idealOfLE_top
    rw [← O.idealOfLE_ofPrime P]
    exact key _ _ h
  · rintro rfl
    exact O.ofPrime_bot

/-- **The height-one coarsening** (Temkin, Lemma 2.1.4(ii), proof of Theorem 2.1.8, lines
2205–2232): a valuation ring of finite height `h ≥ 1` has a nonzero prime `P₁` such that the
coarsening `O_{P₁}` has height one; then `Õ_{P₁}` has height `h - 1`. -/
theorem exists_height_ofPrime_eq_one [Finite (PrimeSpectrum O)] (hO : O ≠ ⊤) :
    ∃ P₁ : PrimeSpectrum O, P₁.asIdeal ≠ ⊥ ∧ height (O.ofPrime P₁.asIdeal) = 1 ∧
      height (residueSubring O P₁.asIdeal) + 1 = height O := by
  set S : Set (PrimeSpectrum O) := {q | q.asIdeal ≠ ⊥}
  have hS : S.Nonempty := by
    refine ⟨⟨maximalIdeal O, inferInstance⟩, ?_⟩
    change maximalIdeal O ≠ ⊥
    rwa [Ne, maximalIdeal_eq_bot_iff]
  obtain ⟨p₁, hp₁⟩ := S.toFinite.exists_minimal hS
  have hp₁S : p₁.asIdeal ≠ ⊥ := hp₁.prop
  set z : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hIic : Set.Iic p₁ = {z, p₁} := by
    ext q
    simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hq
      by_cases hq0 : q.asIdeal = ⊥
      · left
        exact PrimeSpectrum.ext hq0
      · right
        exact hp₁.eq_of_le hq0 hq
    · rintro (rfl | rfl)
      · exact bot_le (a := p₁.asIdeal)
      · exact le_rfl
  have hzp : z ≠ p₁ := fun h ↦ hp₁S (congrArg PrimeSpectrum.asIdeal h).symm
  have h1 : height (O.ofPrime p₁.asIdeal) = 1 := by
    have h := natCard_primeSpectrum_eq_height_add_one (O.ofPrime p₁.asIdeal)
    rw [Nat.card_congr (primeSpectrumOfPrimeOrderIso O p₁.asIdeal).toEquiv,
      Nat.card_coe_set_eq] at h
    change (Set.Iic p₁).ncard = _ at h
    rw [hIic, Set.ncard_pair hzp] at h
    omega
  refine ⟨p₁, hp₁S, h1, ?_⟩
  have := height_ofPrime_add_height_residueSubring O p₁.asIdeal
  omega

end Coarsening

end DeJongAlterations.StableModification.Valuation
