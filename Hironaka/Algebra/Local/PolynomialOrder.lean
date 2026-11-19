/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.Algebra.MvPolynomial.Degrees
import Hironaka.Algebra.Local.PowerSeries

/-!
# The order of a polynomial at a point is at most its degree

Kollár's proof of [Kol07, Lemma 61] finds, in the transform `π_*^{-1} f` of an element of order
`m`, "a monomial of degree `≤ m`", and concludes `ord ≤ m` at the origin of the chart; the points
of the fibre that are not `κ`-rational are reached in the text by a linear change of coordinates,
which only exists over an algebraically closed field.  This file replaces the linear change by
the following elementary fact, valid at every prime of a polynomial ring over any field: a
nonzero polynomial `P ∈ κ[Y]` has order at most `deg P` in the localization at every prime `𝔮`
(`ordElem_algebraMap_le_totalDegree`); not in the sources.  It is applied to the exceptional
fibre of the chart of a blow-up in `Hironaka/Algebra/Local/ChartFibre.lean`.

**Why.**  Let `L` be the residue field of `𝔮` (the fraction field of `κ[Y]/𝔮`) and `a ∈ L^σ` the
image of the coordinates — the generic point of `V(𝔮)`.  Substituting `Y_i ↦ a_i + Y_i` gives a
ring homomorphism `κ[Y] → L⟦Y⟧` whose constant term is evaluation at `a`; it sends `𝔮` into the
maximal ideal and the complement of `𝔮` to units, so it extends to a local homomorphism
`κ[Y]_𝔮 → L⟦Y⟧`.  Orders do not decrease along local homomorphisms (`ord_le_ord_map`), the order
in `L⟦Y⟧` is Mathlib's `MvPowerSeries.order` (`MvPowerSeries.ordElem_eq_order`), and the image of
`P` is the polynomial `P(a + Y)`, nonzero of degree `≤ deg P`, whose order is at most the degree
of any of its monomials.
-/

public section

namespace IsLocalRing

open IsLocalRing MvPolynomial

section Singleton

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The order of a principal ideal is the order of its generator. -/
theorem ord_span_singleton (f : R) : ord (Ideal.span {f}) = ordElem f := rfl

/-- Orders of elements do not decrease along local homomorphisms. -/
theorem ordElem_le_ordElem_map {S : Type*} [CommRing S] [IsLocalRing S] (φ : R →+* S)
    [IsLocalHom φ] (f : R) : ordElem f ≤ ordElem (φ f) := by
  rw [← ord_span_singleton, ← ord_span_singleton]
  have := ord_le_ord_map φ (Ideal.span {f})
  rwa [Ideal.map_span, Set.image_singleton] at this

end Singleton

section Polynomial

variable {K : Type*} [Field K] {σ : Type*} [Finite σ]

omit [Finite σ] in
/-- A nonzero polynomial `Q` has order at most its total degree in `L⟦Y⟧`. -/
theorem order_coe_le_totalDegree {L : Type*} [Field L] {Q : MvPolynomial σ L} (hQ : Q ≠ 0) :
    MvPowerSeries.order (Q : MvPowerSeries σ L) ≤ Q.totalDegree := by
  classical
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hQ)
  refine (MvPowerSeries.order_le (d := s) ?_).trans ?_
  · rw [coeff_coe]
    exact mem_support_iff.mp hs
  · exact_mod_cast (le_totalDegree hs)

omit [Finite σ] in
/-- The total degree of a finite product is at most the sum of the total degrees. -/
theorem totalDegree_finset_prod_le {L : Type*} [CommSemiring L] {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial σ L) : (∏ i ∈ s, g i).totalDegree ≤ ∑ i ∈ s, (g i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

omit [Finite σ] in
/-- The substitution `Y_i ↦ a_i + Y_i` does not raise the total degree. -/
theorem totalDegree_eval₂Hom_add_le {L : Type*} [Field L] (φ : K →+* L) (a : σ → L)
    (P : MvPolynomial σ K) :
    (eval₂Hom (C.comp φ) (fun i => C (a i) + X i) P).totalDegree ≤ P.totalDegree := by
  classical
  have h1 : ∀ i, (C (a i) + X i : MvPolynomial σ L).totalDegree ≤ 1 := fun i =>
    (totalDegree_add _ _).trans (max_le (by simp) (by rw [totalDegree_X]))
  rw [coe_eval₂Hom, eval₂_eq]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [RingHom.comp_apply, totalDegree_C, zero_add]
  refine (totalDegree_finset_prod_le _ _).trans ?_
  have h2 : ∑ i ∈ d.support, ((C (a i) + X i : MvPolynomial σ L) ^ d i).totalDegree ≤
      ∑ i ∈ d.support, d i :=
    Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left _ (h1 i)).trans (mul_one _).le)
  have h3 : ∑ i ∈ d.support, d i ≤ P.totalDegree := le_totalDegree hd
  exact h2.trans h3

/-- A nonzero polynomial has order at most its degree at every prime of `κ[Y]` (in place of the
linear change of coordinates in the proof of [Kol07, Lemma 61]; not in the sources). -/
theorem ordElem_algebraMap_le_totalDegree (𝔮 : Ideal (MvPolynomial σ K)) [𝔮.IsPrime]
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ordElem (algebraMap (MvPolynomial σ K) (Localization.AtPrime 𝔮) P) ≤ P.totalDegree := by
  classical
  -- the residue field of `𝔮` and the generic point `a` of `V(𝔮)`
  let A := MvPolynomial σ K ⧸ 𝔮
  let L := FractionRing A
  let ι : A →+* L := algebraMap A L
  have hι : Function.Injective ι := IsFractionRing.injective A L
  let φ : K →+* L := ι.comp ((Ideal.Quotient.mk 𝔮).comp C)
  let a : σ → L := fun i => ι (Ideal.Quotient.mk 𝔮 (X i))
  -- `Y_i ↦ a_i + Y_i`, into `L[Y] ⊆ L⟦Y⟧`
  let ψ₀ : MvPolynomial σ K →+* MvPolynomial σ L := eval₂Hom (C.comp φ) fun i => C (a i) + X i
  let ψ : MvPolynomial σ K →+* MvPowerSeries σ L :=
    (MvPolynomial.coeToMvPowerSeries.ringHom).comp ψ₀
  -- the constant term of `ψ p` is the image of `p` in `L`
  have hconst : ∀ p, MvPowerSeries.constantCoeff (ψ p) = ι (Ideal.Quotient.mk 𝔮 p) := by
    have h : (MvPowerSeries.constantCoeff (σ := σ) (R := L)).comp ψ =
        ι.comp (Ideal.Quotient.mk 𝔮) := by
      refine ringHom_ext (fun c => ?_) (fun i => ?_)
      · simp [ψ, ψ₀, φ]
      · simp [ψ, ψ₀, a]
    exact fun p => congrArg (fun g : MvPolynomial σ K →+* L => g p) h
  have hψ_unit : ∀ s : 𝔮.primeCompl, IsUnit (ψ s) := fun s => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hconst, isUnit_iff_ne_zero, ne_eq, ← map_zero ι,
      hι.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact s.2
  -- `ψ` extends to a local homomorphism from the localization at `𝔮`
  let Ψ : Localization.AtPrime 𝔮 →+* MvPowerSeries σ L := IsLocalization.lift hψ_unit
  have hΨ : ∀ p, Ψ (algebraMap _ _ p) = ψ p := fun p => IsLocalization.lift_eq hψ_unit p
  have : IsLocalHom Ψ := by
    refine ⟨fun z hz => ?_⟩
    obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    rw [IsLocalization.lift_mk' hψ_unit] at hz
    have hp : IsUnit (ψ p) := (isUnit_of_mul_isUnit_left hz)
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hconst, isUnit_iff_ne_zero, ne_eq, ← map_zero ι,
      hι.eq_iff, Ideal.Quotient.eq_zero_iff_mem] at hp
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime 𝔮) 𝔮 p s).mpr hp
  -- `ψ₀ P ≠ 0`: `ψ₀` is the (injective) coefficient map followed by a translation
  have hψ₀ : ψ₀ P ≠ 0 := by
    intro h0
    -- undo the translation with `Y_i ↦ Y_i − a_i`
    have hinv : (eval₂Hom C fun i => X i - C (a i) : MvPolynomial σ L →+* MvPolynomial σ L).comp
        ψ₀ = MvPolynomial.map φ := by
      refine ringHom_ext (fun c => ?_) (fun i => ?_)
      · simp [ψ₀]
      · simp [ψ₀]
    have h1 :=
      congrArg (eval₂Hom C fun i => X i - C (a i) : MvPolynomial σ L →+* MvPolynomial σ L) h0
    rw [map_zero, ← RingHom.comp_apply, hinv] at h1
    exact hP (map_injective φ φ.injective (h1.trans (map_zero (MvPolynomial.map φ)).symm))
  calc ordElem (algebraMap (MvPolynomial σ K) (Localization.AtPrime 𝔮) P)
      ≤ ordElem (Ψ (algebraMap (MvPolynomial σ K) (Localization.AtPrime 𝔮) P)) :=
        ordElem_le_ordElem_map Ψ _
    _ = MvPowerSeries.order (ψ₀ P : MvPowerSeries σ L) := by
        rw [hΨ, MvPowerSeries.ordElem_eq_order]
        rfl
    _ ≤ (ψ₀ P).totalDegree := order_coe_le_totalDegree hψ₀
    _ ≤ P.totalDegree := by exact_mod_cast totalDegree_eval₂Hom_add_le φ a P

end Polynomial

end IsLocalRing
