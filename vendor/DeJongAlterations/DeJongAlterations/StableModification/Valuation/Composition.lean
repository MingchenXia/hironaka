import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import DeJongAlterations.StableModification.Valuation.Bounded

/-!
# Composition of valuations

Let `A` be a valuation subring of a field `L` and `B` a valuation subring of the residue field
`κ(A)`. The preimage of `B` under the residue map `A → κ(A)` is a valuation subring of `L`, the
valuation **composed** from `A` and `B`. Conversely every valuation subring `O ⊆ A` is composed
from `A` and its image `O/𝔪_A ⊆ κ(A)`. This is Lemma 2.1.4 (`composlem`) of M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.1
(`semi-stable.tex`, lines 1955–1983), the basis of the induction on the height in the proof of
Theorem 2.1.8.

## Main definitions

* `compose A B`: the valuation subring `{x ∈ A | x̄ ∈ B}` of `L`.
* `decompose A O h`: for `O ≤ A`, the image `O/𝔪_A` of `O` in `κ(A)`.

## Main results

* `maximalIdeal_subset_of_le` (Temkin 2.1.4(i), `𝔪_A ⊂ O`), `compose_decompose`,
  `decompose_compose`, `composeOrderIso`: valuation subrings of `L` contained in `A` correspond
  to valuation subrings of `κ(A)` (Temkin 2.1.4(i)).
* `valuation_compose_eq_one_iff`, `mem_nonunits_compose_iff`: units and nonunits of the composed
  ring.
* `exists_compose_of_lt_of_lt` (Temkin 2.1.4(ii)): a valuation subring with a prime strictly
  between `0` and its maximal ideal is composed from two valuation rings of positive height.
* `comap_compose`, `comap_decompose`: composition commutes with restriction to a subfield `K`,
  using the residue field map `κ(A ∩ K) → κ(A)`.

The gluing of spectra and the iteration in 2.1.4(iii) are not needed: the induction on the height
in Theorem 2.1.8 composes along the height-one coarsening.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation

variable {L : Type*} [Field L]

section Compose

variable (A : ValuationSubring L) (B : ValuationSubring (ResidueField A))

/-- The subring of `L` underlying the composed valuation subring. -/
def composeSubring : Subring L :=
  (B.toSubring.comap (residue A)).map A.subtype

theorem mem_composeSubring {x : L} :
    x ∈ composeSubring A B ↔ ∃ h : x ∈ A, residue A ⟨x, h⟩ ∈ B := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

/-- An element of `A` that is not a unit lies in the maximal ideal, so its residue is zero; an
element of `L` outside `A` has inverse in the maximal ideal of `A`. -/
theorem inv_mem_maximalIdeal_of_not_mem {x : L} (hx : x ∉ A) :
    ∃ h : x⁻¹ ∈ A, (⟨x⁻¹, h⟩ : A) ∈ maximalIdeal A := by
  have h := (A.mem_or_inv_mem x).resolve_left hx
  refine ⟨h, fun hu ↦ hx ?_⟩
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  have hv' : x⁻¹ * (v : L) = 1 := congrArg Subtype.val hv
  have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
  have : (v : L) = x := by
    rw [← (mul_eq_one_iff_inv_eq₀ (inv_ne_zero hx0)).mp hv', inv_inv]
  exact this ▸ v.2

/-- The valuation subring of `L` **composed** from `A` and a valuation subring `B` of the residue
field `κ(A)` (Temkin, `semi-stable.tex` l. 1955–1958): the preimage `{x ∈ A | x̄ ∈ B}` of `B`
under the residue map. -/
def compose : ValuationSubring L :=
  ValuationSubring.ofSubring (composeSubring A B) fun x ↦ by
    simp only [mem_composeSubring]
    by_cases hxA : x ∈ A
    · by_cases hB : residue A ⟨x, hxA⟩ ∈ B
      · exact .inl ⟨hxA, hB⟩
      right
      have hne : residue A ⟨x, hxA⟩ ≠ 0 := fun h ↦ hB (h ▸ B.zero_mem)
      have hu : IsUnit (⟨x, hxA⟩ : A) := (residue_ne_zero_iff_isUnit _).mp hne
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
      have hv' : x * (v : L) = 1 := congrArg Subtype.val hv
      have hx0 : x ≠ 0 := fun h ↦ by rw [h, zero_mul] at hv'; exact zero_ne_one hv'
      have hvx : (v : L) = x⁻¹ := ((mul_eq_one_iff_inv_eq₀ hx0).mp hv').symm
      refine ⟨hvx ▸ v.2, ?_⟩
      have hres : residue A ⟨x⁻¹, hvx ▸ v.2⟩ = (residue A ⟨x, hxA⟩)⁻¹ := by
        have : (⟨x⁻¹, hvx ▸ v.2⟩ : A) * ⟨x, hxA⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
        exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, this, map_one])
      rw [hres]
      exact (B.mem_or_inv_mem _).resolve_left hB
    · right
      obtain ⟨h, hm⟩ := inv_mem_maximalIdeal_of_not_mem A hxA
      refine ⟨h, ?_⟩
      rw [(residue_eq_zero_iff _).mpr hm]
      exact B.zero_mem

variable {A B}

theorem mem_compose {x : L} : x ∈ compose A B ↔ ∃ h : x ∈ A, residue A ⟨x, h⟩ ∈ B :=
  mem_composeSubring A B

theorem mem_compose_of_mem {a : A} (ha : residue A a ∈ B) : (a : L) ∈ compose A B :=
  mem_compose.mpr ⟨a.2, ha⟩

variable (A B)

theorem compose_le : compose A B ≤ A := fun _ hx ↦ (mem_compose.mp hx).1

/-- The maximal ideal of `A` is contained in the composed ring. -/
theorem mem_compose_of_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    (a : L) ∈ compose A B :=
  mem_compose_of_mem (by rw [(residue_eq_zero_iff _).mpr ha]; exact B.zero_mem)

@[simp]
theorem compose_top : compose A ⊤ = A :=
  le_antisymm (compose_le A ⊤) fun _ hx ↦ mem_compose.mpr ⟨hx, trivial⟩

/-- An element `a` of `A` is a unit of the composed ring iff it is a unit of `A` whose residue is
a unit of `B`. -/
theorem valuation_compose_eq_one_iff (a : A) :
    (compose A B).valuation (a : L) = 1 ↔ IsUnit a ∧ B.valuation (residue A a) = 1 := by
  constructor
  · intro h
    have ha : (a : L) ∈ compose A B := by
      rw [← ValuationSubring.valuation_le_one_iff, h]
    have hu : IsUnit (⟨a, ha⟩ : compose A B) := ((compose A B).valuation_eq_one_iff _).mpr h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
    have hv' : (a : L) * (v : L) = 1 := congrArg Subtype.val hv
    obtain ⟨hvA, hvB⟩ := mem_compose.mp v.2
    have haU : IsUnit a :=
      isUnit_iff_exists_inv.mpr ⟨⟨v, hvA⟩, Subtype.ext hv'⟩
    refine ⟨haU, ?_⟩
    have hres : residue A a * residue A ⟨v, hvA⟩ = 1 := by
      rw [← map_mul]
      have : a * ⟨v, hvA⟩ = 1 := Subtype.ext hv'
      rw [this, map_one]
    have hra : residue A a ∈ B := (mem_compose.mp ha).2
    have hu' : IsUnit (⟨residue A a, hra⟩ : B) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hvB⟩, Subtype.ext hres⟩
    exact (B.valuation_eq_one_iff _).mp hu'
  · rintro ⟨haU, hB⟩
    have hra : residue A a ∈ B := by
      rw [← ValuationSubring.valuation_le_one_iff, hB]
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp haU
    have hres : residue A a * residue A v = 1 := by rw [← map_mul, hv, map_one]
    have hrv : residue A v ∈ B := by
      have hu' : IsUnit (⟨residue A a, hra⟩ : B) := (B.valuation_eq_one_iff _).mpr hB
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu'
      have hw' : residue A a * (w : ResidueField A) = 1 := congrArg Subtype.val hw
      have hne : residue A a ≠ 0 := fun h ↦ by rw [h, zero_mul] at hres; exact zero_ne_one hres
      have : residue A v = (w : ResidueField A) := by
        rw [← (mul_eq_one_iff_inv_eq₀ hne).mp hres, (mul_eq_one_iff_inv_eq₀ hne).mp hw']
      exact this ▸ w.2
    have hu : IsUnit (⟨a, mem_compose_of_mem hra⟩ : compose A B) :=
      isUnit_iff_exists_inv.mpr ⟨⟨v, mem_compose_of_mem hrv⟩,
        Subtype.ext (show (a : L) * (v : L) = 1 from congrArg Subtype.val hv)⟩
    exact ((compose A B).valuation_eq_one_iff _).mp hu

/-- An element of `L` is a nonunit of the composed ring iff it lies in `A` and its residue is a
nonunit of `B`. -/
theorem valuation_compose_lt_one_iff (a : A) :
    (compose A B).valuation (a : L) < 1 ↔ B.valuation (residue A a) < 1 := by
  by_cases ha : residue A a ∈ B
  · have h1 := (compose A B).valuation_le_one ⟨a, mem_compose_of_mem ha⟩
    have h2 := B.valuation_le_one ⟨_, ha⟩
    rw [lt_iff_le_and_ne, lt_iff_le_and_ne, Ne, Ne, valuation_compose_eq_one_iff]
    simp only [h1, h2, true_and]
    constructor
    · intro h hB
      apply h ⟨(residue_ne_zero_iff_isUnit a).mp fun h0 ↦ ?_, hB⟩
      rw [h0, map_zero] at hB
      exact zero_ne_one hB
    · rintro h ⟨-, hB⟩
      exact h hB
  · constructor
    · intro h
      exact absurd ((mem_compose.mp ((compose A B).valuation_le_one_iff _ |>.mp h.le)).2) ha
    · intro h
      exact absurd ((B.valuation_le_one_iff _).mp h.le) ha

end Compose

section Decompose

variable (A : ValuationSubring L) {O : ValuationSubring L}

/-- Temkin 2.1.4(i): if `O ⊆ A`, then the maximal ideal of `A` is contained in `O`. -/
theorem mem_of_mem_maximalIdeal_of_le (h : O ≤ A) {a : A} (ha : a ∈ maximalIdeal A) :
    (a : L) ∈ O := by
  by_contra hO
  have hinv : (a : L)⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left hO
  have ha0 : (a : L) ≠ 0 := fun h0 ↦ hO (h0 ▸ O.zero_mem)
  apply ha
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, h hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/-- Temkin 2.1.4(i): if `O ⊆ A`, then the maximal ideal of `A` is contained in `O`. -/
theorem maximalIdeal_subset_of_le (h : O ≤ A) :
    ((↑) : A → L) '' (maximalIdeal A : Set A) ⊆ O := by
  rintro _ ⟨a, ha, rfl⟩
  exact mem_of_mem_maximalIdeal_of_le A h ha

/-- The subring of `κ(A)` underlying `decompose A O h`. -/
def decomposeSubring (_h : O ≤ A) : Subring (ResidueField A) :=
  (O.toSubring.comap A.subtype).map (residue A)

theorem mem_decomposeSubring (h : O ≤ A) {y : ResidueField A} :
    y ∈ decomposeSubring A h ↔ ∃ a : A, (a : L) ∈ O ∧ residue A a = y :=
  Iff.rfl

/-- For a valuation subring `O ⊆ A`, the image `O/𝔪_A` of `O` in the residue field `κ(A)`, a
valuation subring of `κ(A)` (Temkin 2.1.4(i)). -/
def decompose (h : O ≤ A) : ValuationSubring (ResidueField A) :=
  ValuationSubring.ofSubring (decomposeSubring A h) fun y ↦ by
    simp only [mem_decomposeSubring A h]
    obtain ⟨a, rfl⟩ := residue_surjective y
    by_cases haO : (a : L) ∈ O
    · exact .inl ⟨a, haO, rfl⟩
    right
    have hinv : (a : L)⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left haO
    have ha0 : (a : L) ≠ 0 := fun h0 ↦ haO (h0 ▸ O.zero_mem)
    refine ⟨⟨_, h hinv⟩, hinv, ?_⟩
    have : (⟨_, h hinv⟩ : A) * a = 1 := Subtype.ext (inv_mul_cancel₀ ha0)
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, this, map_one])

variable {A}

theorem mem_decompose {h : O ≤ A} {y : ResidueField A} :
    y ∈ decompose A h ↔ ∃ a : A, (a : L) ∈ O ∧ residue A a = y :=
  Iff.rfl

variable (A)

/-- Temkin 2.1.4(i): `O` is composed from `A` and `O/𝔪_A`. -/
@[simp]
theorem compose_decompose (h : O ≤ A) : compose A (decompose A h) = O := by
  ext x
  rw [mem_compose]
  constructor
  · rintro ⟨hxA, a, haO, ha⟩
    have hm : (⟨x, hxA⟩ : A) - a ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, ha, sub_self]
    have := mem_of_mem_maximalIdeal_of_le A h hm
    have hx : x = ((⟨x, hxA⟩ - a : A) : L) + a := by simp
    rw [hx]
    exact add_mem this haO
  · intro hx
    exact ⟨h hx, ⟨x, h hx⟩, hx, rfl⟩

@[simp]
theorem decompose_compose (B : ValuationSubring (ResidueField A)) :
    decompose A (compose_le A B) = B := by
  ext y
  rw [mem_decompose]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_compose.mp ha).2
  · intro hy
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨a, mem_compose_of_mem hy, rfl⟩

theorem compose_mono {B B' : ValuationSubring (ResidueField A)} (hB : B ≤ B') :
    compose A B ≤ compose A B' := fun _ hx ↦
  let ⟨h, hx⟩ := mem_compose.mp hx
  mem_compose.mpr ⟨h, hB hx⟩

theorem decompose_mono {O O' : ValuationSubring L} (h : O ≤ A) (h' : O' ≤ A) (hO : O ≤ O') :
    decompose A h ≤ decompose A h' := fun _ ⟨a, ha, hy⟩ ↦ ⟨a, hO ha, hy⟩

/-- Temkin 2.1.4(i): valuation subrings of `L` contained in `A` correspond to valuation subrings
of the residue field `κ(A)`. -/
def composeOrderIso : Set.Iic A ≃o ValuationSubring (ResidueField A) where
  toFun O := decompose A O.2
  invFun B := ⟨compose A B, compose_le A B⟩
  left_inv O := Subtype.ext (compose_decompose A O.2)
  right_inv B := decompose_compose A B
  map_rel_iff' {O O'} := by
    constructor
    · intro hle
      change O.1 ≤ O'.1
      rw [← compose_decompose A O.2, ← compose_decompose A O'.2]
      exact compose_mono A hle
    · intro hle
      exact decompose_mono A O.2 O'.2 hle

@[simp]
theorem decompose_eq_top_iff (h : O ≤ A) : decompose A h = ⊤ ↔ O = A := by
  constructor
  · intro htop
    rw [← compose_decompose A h, htop, compose_top]
  · rintro rfl
    exact top_unique fun y _ ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective y
      exact ⟨a, a.2, rfl⟩

/-- Temkin 2.1.4(ii): if the valuation subring `O` has a prime ideal `p` with `0 < p < 𝔪_O`, then
`O` is composed from the coarsening `A = O_p ≠ L` and a valuation subring `O/𝔪_A ≠ κ(A)`, both of
positive height. -/
theorem exists_compose_of_lt_of_lt (O : ValuationSubring L) (p : Ideal O) [p.IsPrime]
    (hbot : ⊥ < p) (htop : p < maximalIdeal O) :
    ∃ (A : ValuationSubring L) (h : O ≤ A), A ≠ ⊤ ∧ decompose A h ≠ ⊤ ∧
      compose A (decompose A h) = O := by
  refine ⟨O.ofPrime p, O.le_ofPrime p, ?_, ?_, compose_decompose _ _⟩
  · intro h
    apply hbot.ne'
    rw [← O.idealOfLE_ofPrime p]
    simp only [h, ValuationSubring.idealOfLE_top]
  · rw [Ne, decompose_eq_top_iff]
    intro h
    apply htop.ne
    rw [← O.idealOfLE_ofPrime p]
    simp only [← h, ValuationSubring.idealOfLE_self]

end Decompose

section Restriction

variable {K : Type*} [Field K] [Algebra K L]
variable (A : ValuationSubring L) (B : ValuationSubring (ResidueField A))

theorem residue_algebraMap_comap (a : A.comap (algebraMap K L)) :
    algebraMap (ResidueField (A.comap (algebraMap K L))) (ResidueField A)
        (residue (A.comap (algebraMap K L)) a) =
      residue A ⟨algebraMap K L a, a.2⟩ :=
  ResidueField.algebraMap_residue a

/-- Composition commutes with restriction to a subfield (Temkin 2.1.4, used in the proof of
Proposition 2.2.2, `semi-stable.tex` l. 2146–2175): `(A ∘ B) ∩ K` is composed from `A ∩ K` and
`B ∩ κ(A ∩ K)`. -/
theorem comap_compose :
    (compose A B).comap (algebraMap K L) =
      compose (A.comap (algebraMap K L))
        (B.comap (algebraMap (ResidueField (A.comap (algebraMap K L))) (ResidueField A))) := by
  ext c
  rw [ValuationSubring.mem_comap, mem_compose, mem_compose]
  constructor
  · rintro ⟨h, hB⟩
    refine ⟨h, ?_⟩
    rw [ValuationSubring.mem_comap, residue_algebraMap_comap]
    exact hB
  · rintro ⟨h, hB⟩
    refine ⟨h, ?_⟩
    rw [ValuationSubring.mem_comap, residue_algebraMap_comap] at hB
    exact hB

omit [Algebra K L] in
theorem comap_le_comap {O A : ValuationSubring L} (f : K →+* L) (h : O ≤ A) :
    O.comap f ≤ A.comap f :=
  fun _ hx ↦ h hx

/-- Decomposition commutes with restriction to a subfield. -/
theorem comap_decompose {O : ValuationSubring L} (h : O ≤ A) :
    decompose (A.comap (algebraMap K L)) (comap_le_comap (algebraMap K L) h) =
      (decompose A h).comap
        (algebraMap (ResidueField (A.comap (algebraMap K L))) (ResidueField A)) := by
  ext y
  rw [ValuationSubring.mem_comap]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact mem_decompose.mpr ⟨⟨algebraMap K L a, a.2⟩, ha, (residue_algebraMap_comap A a).symm⟩
  · intro hy
    obtain ⟨b, hb, hby⟩ := mem_decompose.mp hy
    obtain ⟨a, rfl⟩ := residue_surjective y
    refine mem_decompose.mpr ⟨a, ?_, rfl⟩
    rw [residue_algebraMap_comap] at hby
    have hm : (⟨algebraMap K L a, a.2⟩ : A) - b ∈ maximalIdeal A := by
      rw [← residue_eq_zero_iff, map_sub, hby, sub_self]
    have hmO := mem_of_mem_maximalIdeal_of_le A h hm
    have : algebraMap K L a = ((⟨algebraMap K L a, a.2⟩ - b : A) : L) + b := by simp
    change algebraMap K L a ∈ O
    rw [this]
    exact add_mem hmO hb

end Restriction

end DeJongAlterations.StableModification.Valuation
