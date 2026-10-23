import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Restriction of a valuation subring to a subfield; bounded extensions

Let `K → L` be a field extension and `O` a valuation subring of `L`. This file sets up the
restriction `O ∩ K = O.comap (algebraMap K L)` together with the inclusion `O ∩ K → O` as an
algebra (used throughout `StableModification/Valuation/`), and formalizes Temkin's notion of a
*bounded* extension of valued fields: M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), §2.1 (`semi-stable.tex`, lines 2050–2052).

An extension `L/K` of valued fields is **bounded** if every nonzero element of `O` divides a
nonzero element of `O ∩ K`. Temkin observes that this holds if and only if the valuation ring
`K·O`, the localization of `O` at the nonzero elements of `O ∩ K`, is all of `L`.

## Main definitions

* `comapInclusion`, `instAlgebraComap`: the inclusion `O ∩ K → O` as an algebra, with the scalar
  towers over `K` and `L`; it is a local homomorphism (`instIsLocalHomComap`), so the residue field
  of `O` is an algebra over the residue field of `O ∩ K`.
* `baseLocalization K O`: Temkin's valuation ring `K·O` of `L`, the localization of `O` at the
  nonzero elements of `O ∩ K`; `toBaseLocalization` is the inclusion `K → K·O`.
* `IsBoundedExtension K O`: every nonzero element of `O` divides a nonzero element of `O ∩ K`.

## Main results

* `le_baseLocalization`, `algebraMap_mem_baseLocalization`, `baseLocalization_le`: `K·O` is the
  smallest valuation subring of `L` containing `O` and the image of `K`.
* `isBoundedExtension_iff`: `L/K` is bounded if and only if `K·O = L` (Temkin l. 2050–2052).
* `baseLocalization_eq_self`: if the valuation is trivial on `K`, then `K·O = O`.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Restriction

variable (O : ValuationSubring L)

/-- The inclusion `O ∩ K → O`, for a valuation subring `O` of `L` and a field `K` over which
`L` is an algebra; here `O ∩ K = O.comap (algebraMap K L)`. -/
def comapInclusion : O.comap (algebraMap K L) →+* O :=
  (algebraMap K L).restrict _ O fun _ h ↦ h

/-- The algebra structure of `O` over `O ∩ K = O.comap (algebraMap K L)`. -/
instance instAlgebraComap : Algebra (O.comap (algebraMap K L)) O :=
  (comapInclusion O).toAlgebra

@[simp]
theorem coe_algebraMap_comap (a : O.comap (algebraMap K L)) :
    ((algebraMap (O.comap (algebraMap K L)) O a : O) : L) = algebraMap K L a :=
  rfl

instance instIsScalarTowerComap : IsScalarTower (O.comap (algebraMap K L)) O L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance instIsScalarTowerComapField : IsScalarTower (O.comap (algebraMap K L)) K L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem algebraMap_comap_injective :
    Function.Injective (algebraMap (O.comap (algebraMap K L)) O) := by
  intro a b h
  apply Subtype.ext
  apply (algebraMap K L).injective
  simpa using congrArg Subtype.val h

/-- The inclusion `O ∩ K → O` is a local homomorphism. -/
instance instIsLocalHomComap : IsLocalHom (algebraMap (O.comap (algebraMap K L)) O) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  have hv' : algebraMap K L a * (v : L) = 1 := congrArg Subtype.val hv
  have ha0 : (a : K) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, zero_mul] at hv'
    exact zero_ne_one hv'
  have hinv : (a : K)⁻¹ ∈ O.comap (algebraMap K L) := by
    rw [ValuationSubring.mem_comap, map_inv₀,
      (mul_eq_one_iff_inv_eq₀ ((map_ne_zero _).mpr ha0)).mp hv']
    exact v.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/-- The maximal ideal of `O ∩ K` is the trace of the maximal ideal of `O`. -/
theorem comap_maximalIdeal_comap :
    (maximalIdeal O).comap (algebraMap (O.comap (algebraMap K L)) O) =
      maximalIdeal (O.comap (algebraMap K L)) :=
  ((local_hom_TFAE (algebraMap (O.comap (algebraMap K L)) O)).out 0 4).mp
    (instIsLocalHomComap O)

end Restriction

section BaseLocalization

variable (K) (O : ValuationSubring L)

/-- The subring of `L` underlying `K·O`: the elements `x` with `a * x ∈ O` for some nonzero
`a ∈ O ∩ K`. -/
def baseLocalizationSubring : Subring L where
  carrier := {x | ∃ a : K, a ≠ 0 ∧ algebraMap K L a ∈ O ∧ algebraMap K L a * x ∈ O}
  mul_mem' := by
    rintro x y ⟨a, ha, haO, hax⟩ ⟨b, hb, hbO, hby⟩
    refine ⟨a * b, mul_ne_zero ha hb, by simpa using mul_mem haO hbO, ?_⟩
    have : algebraMap K L (a * b) * (x * y) = (algebraMap K L a * x) * (algebraMap K L b * y) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem hax hby
  one_mem' := ⟨1, one_ne_zero, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, haO, hax⟩ ⟨b, hb, hbO, hby⟩
    refine ⟨a * b, mul_ne_zero ha hb, by simpa using mul_mem haO hbO, ?_⟩
    have : algebraMap K L (a * b) * (x + y) =
        algebraMap K L b * (algebraMap K L a * x) + algebraMap K L a * (algebraMap K L b * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem hbO hax) (mul_mem haO hby)
  zero_mem' := ⟨1, one_ne_zero, by simp, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha, haO, hax⟩
    exact ⟨a, ha, haO, by simpa using neg_mem hax⟩

theorem le_baseLocalizationSubring : O.toSubring ≤ baseLocalizationSubring K O :=
  fun x hx ↦ ⟨1, one_ne_zero, by simp, by simpa using hx⟩

/-- Temkin's valuation ring `K·O` of `L` (`semi-stable.tex`, l. 2050–2052): the localization of
`O` at the nonzero elements of `O ∩ K`, i.e. the elements `x ∈ L` such that `a * x ∈ O` for some
nonzero `a ∈ O ∩ K`. -/
def baseLocalization : ValuationSubring L :=
  O.ofLE (baseLocalizationSubring K O) (le_baseLocalizationSubring K O)

variable {K O}

theorem mem_baseLocalization {x : L} :
    x ∈ baseLocalization K O ↔
      ∃ a : K, a ≠ 0 ∧ algebraMap K L a ∈ O ∧ algebraMap K L a * x ∈ O :=
  Iff.rfl

variable (K O)

theorem le_baseLocalization : O ≤ baseLocalization K O :=
  le_baseLocalizationSubring K O

theorem algebraMap_mem_baseLocalization (c : K) : algebraMap K L c ∈ baseLocalization K O := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases O.mem_or_inv_mem (algebraMap K L c) with h | h
  · exact le_baseLocalization K O h
  · refine ⟨c⁻¹, inv_ne_zero hc, by rwa [map_inv₀], ?_⟩
    rw [map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).mpr hc)]
    exact O.one_mem

/-- `K·O` is the smallest valuation subring of `L` containing `O` and the image of `K`. -/
theorem baseLocalization_le {V : ValuationSubring L} (hO : O ≤ V)
    (hK : ∀ c : K, algebraMap K L c ∈ V) : baseLocalization K O ≤ V := by
  rintro x ⟨a, ha, -, hax⟩
  have hx : x = algebraMap K L a⁻¹ * (algebraMap K L a * x) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rw [hx]
  exact mul_mem (hK _) (hO hax)

theorem comap_baseLocalization : (baseLocalization K O).comap (algebraMap K L) = ⊤ :=
  top_unique fun c _ ↦ algebraMap_mem_baseLocalization K O c

/-- The inclusion `K → K·O`. -/
def toBaseLocalization : K →+* baseLocalization K O :=
  (algebraMap K L).codRestrict _ (algebraMap_mem_baseLocalization K O)

@[simp]
theorem coe_toBaseLocalization (c : K) :
    (toBaseLocalization K O c : L) = algebraMap K L c :=
  rfl

/-- If the valuation of `O` is trivial on `K` (that is, `O ∩ K = K`), then `K·O = O`. -/
theorem baseLocalization_eq_self (h : O.comap (algebraMap K L) = ⊤) :
    baseLocalization K O = O := by
  refine le_antisymm ?_ (le_baseLocalization K O)
  rintro x ⟨a, ha, -, hax⟩
  have hainv : algebraMap K L a⁻¹ ∈ O := by
    have : a⁻¹ ∈ O.comap (algebraMap K L) := h ▸ trivial
    exact this
  have hx : x = algebraMap K L a⁻¹ * (algebraMap K L a * x) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rw [hx]
  exact mul_mem hainv hax

/-- An extension of valued fields is **bounded** (Temkin, `semi-stable.tex` l. 2050) if every
nonzero element of `O` divides, in `O`, a nonzero element of `O ∩ K`. -/
def IsBoundedExtension : Prop :=
  ∀ x ∈ O, x ≠ 0 → ∃ a : K, a ≠ 0 ∧ algebraMap K L a ∈ O ∧ ∃ y ∈ O, algebraMap K L a = x * y

/-- Temkin (`semi-stable.tex` l. 2050–2052): an extension is bounded if and only if the
valuation ring `K·O` is all of `L`. -/
theorem isBoundedExtension_iff : IsBoundedExtension K O ↔ baseLocalization K O = ⊤ := by
  constructor
  · intro h
    refine top_unique fun x _ ↦ ?_
    rcases O.mem_or_inv_mem x with hx | hx
    · exact le_baseLocalization K O hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact (baseLocalization K O).zero_mem
    obtain ⟨a, ha, haO, y, hy, hay⟩ := h x⁻¹ hx (inv_ne_zero hx0)
    refine ⟨a, ha, haO, ?_⟩
    rw [hay, mul_comm x⁻¹, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
    exact hy
  · intro h x hx hx0
    have hmem : x⁻¹ ∈ baseLocalization K O := h ▸ trivial
    obtain ⟨a, ha, haO, hax⟩ := hmem
    refine ⟨a, ha, haO, _, hax, ?_⟩
    rw [mul_comm (algebraMap K L a), ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

end BaseLocalization

end DeJongAlterations.StableModification.Valuation
