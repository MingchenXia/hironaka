/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.MarkedTripleBlowUp
public import Hironaka.Scheme.BlowUpSequence.Triple
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial split under a smooth blow-up of order at least the mark

[Kol07, 111, Step 1] observes that the birational transforms `(Π_1)^{-1}_* N(I)` and
`(Π_1)^{-1}_*(I, m)` differ only by an ideal sheaf of exceptional divisors of `Π_1`, hence only in
their monomial part, so that `N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)`. Here, for one smooth
blow-up
`π : B_Z X → X` of order `≥ m` for the marked triple `(X, I, m, E)` (conditions (1′)–(2′) of
[Kol07, Definition 65], `MarkedTriple.IsOrderGeBlowUp`) with total transform `E' = π^{-1}_{tot} E`:
`𝒪(mF) · π^{-1}_*(I, m) = π^* I = π^* M(I) · π^* N(I)` (`pow_dvd_comap_of_leOrdAlong`,
`pow_mul_markedTransform` and the split), where `𝒪(−mF)` and `π^* M(I)` are monomials of `E'`,
being invertible ideal sheaves supported on `E'` (`eq_monomialPart_of_isInvertible_of_support_le`
on the marked triple induced after the blow-up), and the nonmonomial part ignores monomials
(`nonmonomialPart_monomial_mul`). The same argument with any control `c` such that
`F^c ∣ π^* N(I)` gives the birational transform (the exceptional order, whose power always divides)
and the marked transform `π^{-1}_*(N(I), a)` for `ord_Z N(I) ≥ a`.

* `blowUpTriple`: the marked triple `(B_Z X, π^{-1}_*(I, m), m, π^{-1}_{tot} E)` induced after the
  blow-up (`MarkedTriple.induced` on the one-step sequence).
* `exists_comap_monomialPart_eq_monomial` (`π^* M(I)` is a monomial of `E'`),
  `nonmonomialPart_controlledTransform_eq` (the common core),
  `nonmonomialPart_markedTransform` (`N(π^{-1}_*(I, m)) = N(π^* N(I))`),
  `nonmonomialPart_markedTransform_eq_weakTransform` (with the birational transform of `N(I)`),
  `nonmonomialPart_markedTransform_of_le_ord` (with the marked transform `π^{-1}_*(N(I), a)`).

These identities are iterated along the rounds of Steps 1 and 2 of the proof of
[Kol07, Theorem 107]
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`,
`NonmonomialInvariant.lean`). The general facts on exceptional orders and nonvanishing used here are
in `Hironaka/Scheme/BlowUpSequence/MarkedTripleBlowUp.lean` and
`Hironaka/Resolution/Algebraic/Snc/DictionaryGenericPoints.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme Hironaka BlowUpSequence IdealSheafData

namespace Hironaka.BMO

open AlgebraicGeometry

section Auxiliary

variable {k : Type u} [Field k] (T' : Triple k)

/-- The support of the monomial part lies in the support of the family: off `E` every member's
inner product is the unit ideal. -/
theorem support_monomialPart_le (J : T'.X.left.IdealSheafData) :
    (monomialPart J T'.E).support ≤ T'.E.support := by
  have := Hironaka.BD.noetherianSpace_triple T'
  intro x hx
  by_contra hxE
  have hnot : ∀ i, x ∉ (T'.E.component i).support := fun i hi =>
    hxE ((DivisorFamily.mem_support_iff_exists _ x).mpr ⟨i, hi⟩)
  have htop : (monomialPart J T'.E).stalkIdeal x = ⊤ := by
    rw [monomialPart_eq_monomial,
      stalkIdeal_monomial T'.E (Snc.genericPoints_component_finite T'.E) _ x]
    exact (Finset.prod_eq_one fun i _ => Snc.finprod_stalk_eq_one_of_notMem T'.E (hnot i) _).trans
      Ideal.one_eq_top
  have hle := (mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp hx
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

end Auxiliary

section Transform

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k) (Z : T.X.left.IdealSheafData)
  (hZ : T.IsOrderGeBlowUp Z)

include hZ

/-- The marked triple `(B_Z X, π^{-1}_*(I, m), m, π^{-1}_{tot} E)` induced after the blow-up
(`MarkedTriple.induced` at stage `1` of the one-step sequence). -/
noncomputable def blowUpTriple : MarkedTriple k :=
  T.induced (cons T.X.left Z (nil _)) (isOrderGeSeq_single T Z hZ) (Fin.last _)

theorem blowUpTriple_X : (blowUpTriple T Z hZ).X.left = Z.blowUp := rfl

theorem blowUpTriple_I : (blowUpTriple T Z hZ).I = T.I.markedTransform Z T.m := rfl

theorem blowUpTriple_E : (blowUpTriple T Z hZ).E = T.E.totalTransform Z := rfl

/-- The identity (60.1) of [Kol07, Definition 60]: `F^m · π^{-1}_*(I, m) = π^* I` for a blow-up of
order `≥ m` (`pow_dvd_comap_of_leOrdAlong`). -/
theorem exceptionalDivisor_pow_mul_markedTransform :
    Z.exceptionalDivisor ^ T.m * T.I.markedTransform Z T.m = T.I.comap
        Z.blowUpπ := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := hZ.1
  exact pow_mul_markedTransform Z T.I T.m
    (pow_dvd_comap_of_leOrdAlong (T.X.left ↘ Spec (.of k)) n Z T.I hZ.2.2)

/-- An invertible ideal sheaf on `B_Z X` supported on the exceptional divisor or over `E` is a
monomial of the total transform `π^{-1}_{tot} E`. -/
theorem exists_eq_monomial_of_isInvertible_of_support_le
    {K : Z.blowUp.IdealSheafData}
    (hK : K.IsInvertible) (hsupp : K.support ≤ (T.E.totalTransform Z).support) :
    ∃ a : Z.blowUp → ℕ, K = (T.E.totalTransform Z).monomial a :=
  ⟨fun η => (K.ord η).toNat,
    (eq_monomialPart_of_isInvertible_of_support_le (blowUpTriple T Z hZ).toTriple hK hsupp).trans
      (monomialPart_eq_monomial _ _)⟩

/-- `π^* M(I)` is a monomial of `π^{-1}_{tot} E` ([Kol07, 111, Step 1]: the two transforms "differ
only by tensoring with an ideal sheaf of exceptional divisors"): it is invertible (the pull-back of
an invertible ideal sheaf along the blow-up) and supported on
`π^{-1}(supp E) ⊆ supp(π^{-1}_{tot} E)`, a point off the exceptional divisor lying on the strict
transform of the member through its image. -/
theorem exists_comap_monomialPart_eq_monomial :
    ∃ a : Z.blowUp → ℕ,
      (monomialPart T.I T.E).comap Z.blowUpπ = (T.E.totalTransform Z).monomial a :=
          by
  have hLN : IsLocallyNoetherian Z.blowUp :=
    ((blowUpTriple T Z hZ).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  refine exists_eq_monomial_of_isInvertible_of_support_le T Z hZ
    (blowUp.isInvertible_comap_of_isInvertible Z _ (isInvertible_monomialPart T.toTriple)) ?_
  intro b hb
  rw [support_comap] at hb
  have hbE : Z.blowUpπ b ∈ T.E.support := support_monomialPart_le T.toTriple T.I hb
  obtain ⟨i, hbi⟩ := (DivisorFamily.mem_support_iff_exists _ _).mp hbE
  by_cases hF : b ∈ Z.exceptionalDivisor.support
  · exact support_exceptionalDivisor_le T Z hF
  · refine (DivisorFamily.mem_support_iff_exists _ b).mpr ⟨toLex (Sum.inl i), ?_⟩
    have hbi' : b ∈ ((T.E.component i).comap Z.blowUpπ).support := by
      rw [support_comap]
      exact hbi
    change b ∈ (((T.E.component i).comap Z.blowUpπ).saturate
      Z.exceptionalDivisor).support
    rw [← SetLike.mem_coe, coe_support_saturate]
    exact subset_closure ⟨hbi', hF⟩

/-- The common core of the three identities below: for a control `c` with `F^c ∣ π^* J` and `J`
nonvanishing, the nonmonomial part of the controlled transform `(π^* J : F^c)` is that of `π^* J`;
they differ by the monomial `F^c`, which `N` ignores. -/
theorem nonmonomialPart_controlledTransform_eq (J : T.X.left.IdealSheafData)
    (hJ : IsNonzeroEverywhere (J.comap Z.blowUpπ)) (c : ℕ)
    (hc : Z.exceptionalDivisor ^ c ∣ J.comap Z.blowUpπ) :
    nonmonomialPart (J.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor c)
        (T.E.totalTransform Z) =
      nonmonomialPart (J.comap Z.blowUpπ) (T.E.totalTransform Z) := by
  set T₁ := blowUpTriple T Z hZ with hT₁
  have hmul : Z.exceptionalDivisor ^ c *
      J.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor c =
        J.comap Z.blowUpπ :=
    pow_mul_colon_of_dvd (I := J.comap Z.blowUpπ) _ c hc
  have hFinv : (Z.exceptionalDivisor ^ c).IsInvertible :=
    Scheme.IdealSheafData.isInvertible_pow (blowUp.isInvertible_comap_π Z) c
  have hFsupp : (Z.exceptionalDivisor ^ c).support ≤ (T.E.totalTransform Z).support := by
    cases c with
    | zero =>
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, support_top]
      exact bot_le
    | succ c =>
      rw [support_pow_succ]
      exact support_exceptionalDivisor_le T Z
  obtain ⟨aF, haF⟩ := exists_eq_monomial_of_isInvertible_of_support_le T Z hZ hFinv hFsupp
  have hC : IsNonzeroEverywhere
      (J.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor c) :=
    isNonzeroEverywhere_of_le (comap_le_controlledTransformAlong _ _ _ _) hJ
  calc nonmonomialPart (J.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor c)
        (T.E.totalTransform Z)
      = nonmonomialPart ((T.E.totalTransform Z).monomial aF *
          J.controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor c)
          (T.E.totalTransform Z) :=
        (nonmonomialPart_monomial_mul T₁.toTriple aF _ hC).symm
    _ = nonmonomialPart (J.comap Z.blowUpπ) (T.E.totalTransform Z) := by
        rw [← haF, hmul]

/-- `π^* I` is nonvanishing: it is `F^m · π^{-1}_*(I, m)`, both factors nonvanishing. -/
theorem isNonzeroEverywhere_comap_of_isOrderGeBlowUp :
    IsNonzeroEverywhere (T.I.comap Z.blowUpπ) := by
  rw [← exceptionalDivisor_pow_mul_markedTransform T Z hZ]
  exact isNonzeroEverywhere_mul (blowUpTriple T Z hZ).toTriple
    (isNonzeroEverywhere_of_isInvertible
      (Scheme.IdealSheafData.isInvertible_pow (blowUp.isInvertible_comap_π Z) T.m))
    (blowUpTriple T Z hZ).isNonzeroEverywhere

/-- `N(π^{-1}_*(I, m)) = N(π^* N(I))` ([Kol07, 111, Step 1], the identity
"`N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)`" read modulo `N` on the right). -/
theorem nonmonomialPart_markedTransform :
    nonmonomialPart (T.I.markedTransform Z T.m) (T.E.totalTransform Z) =
      nonmonomialPart ((nonmonomialPart T.I T.E).comap Z.blowUpπ)
        (T.E.totalTransform Z) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := hZ.1
  have hIπ := isNonzeroEverywhere_comap_of_isOrderGeBlowUp T Z hZ
  have h1 := nonmonomialPart_controlledTransform_eq T Z hZ T.I hIπ T.m
    (pow_dvd_comap_of_leOrdAlong (T.X.left ↘ Spec (.of k)) n Z T.I hZ.2.2)
  obtain ⟨aM, haM⟩ := exists_comap_monomialPart_eq_monomial T Z hZ
  have hNπ : IsNonzeroEverywhere ((nonmonomialPart T.I T.E).comap Z.blowUpπ) :=
    isNonzeroEverywhere_of_le (comap_mono _ (le_colon_self _ _)) hIπ
  have h2 : T.I.comap Z.blowUpπ =
      (T.E.totalTransform Z).monomial aM * (nonmonomialPart T.I T.E).comap
          Z.blowUpπ := by
    rw [← haM, ← comap_mul, monomialPart_mul_nonmonomialPart T.toTriple]
  rw [markedTransform, h1, h2]
  exact nonmonomialPart_monomial_mul (blowUpTriple T Z hZ).toTriple aM _ hNπ

/-- `N(π^{-1}_*(I, m))` is the nonmonomial part of the birational transform `π^{-1}_* N(I)` (the
weak transform, the controlled transform at the exceptional order); [Kol07, 111, Step 1] read
modulo `N`. -/
theorem nonmonomialPart_markedTransform_eq_weakTransform :
    nonmonomialPart (T.I.markedTransform Z T.m) (T.E.totalTransform Z) =
      nonmonomialPart ((nonmonomialPart T.I T.E).weakTransform Z) (T.E.totalTransform Z) := by
  rw [nonmonomialPart_markedTransform T Z hZ]
  have hNπ : IsNonzeroEverywhere ((nonmonomialPart T.I T.E).comap Z.blowUpπ) :=
    isNonzeroEverywhere_of_le (comap_mono _ (le_colon_self _ _))
      (isNonzeroEverywhere_comap_of_isOrderGeBlowUp T Z hZ)
  exact (nonmonomialPart_controlledTransform_eq T Z hZ _ hNπ _
    (pow_exceptionalOrderAlong_dvd _ _ _)).symm

/-- For `ord_Z N(I) ≥ a`, `N(π^{-1}_*(I, m)) = N(π^{-1}_*(N(I), a))`: the marked transform of
`N(I)` at any admissible mark has the same nonmonomial part. -/
theorem nonmonomialPart_markedTransform_of_le_ord (a : ℕ)
    (ha : (nonmonomialPart T.I T.E).LeOrdAlong Z.support (a : ℕ∞)) :
    nonmonomialPart (T.I.markedTransform Z T.m) (T.E.totalTransform Z) =
      nonmonomialPart ((nonmonomialPart T.I T.E).markedTransform Z a) (T.E.totalTransform Z) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := hZ.1
  rw [nonmonomialPart_markedTransform T Z hZ]
  have hNπ : IsNonzeroEverywhere ((nonmonomialPart T.I T.E).comap Z.blowUpπ) :=
    isNonzeroEverywhere_of_le (comap_mono _ (le_colon_self _ _))
      (isNonzeroEverywhere_comap_of_isOrderGeBlowUp T Z hZ)
  exact (nonmonomialPart_controlledTransform_eq T Z hZ _ hNπ a
    (pow_dvd_comap_of_leOrdAlong (T.X.left ↘ Spec (.of k)) n Z _ ha)).symm

end Transform

end Hironaka.BMO
