/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitFunctorial
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitSupport
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial split on a triple

The modules `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean`, `SplitOrder.lean`,
`SplitMain.lean`, `SplitSupport.lean` and `SplitFunctorial.lean` prove [Kol07, Definition–Lemma 110]
for a normal-crossings family on a scheme smooth over `k` (namespace `Hironaka.BMO.Snc`); this
module instantiates them on a triple `T = (X, I, E)` ([Kol07, Notation 64]: `X` smooth of finite
type over `k`, hence Noetherian; `I` nonzero on every component; `E` with normal crossings), in the
forms used by the marked order reduction. Kollár's standing characteristic-zero hypothesis is
carried as the statements carry it.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData

namespace Hironaka.BMO

variable {k : Type u} [Field k]

/-- Every monomial ideal of the triple's family is invertible (the invertibility of `M(I)` in
[Kol07, Definition–Lemma 110]). -/
theorem isInvertible_monomial (T : Triple k) (a : T.X.left → ℕ) :
    (T.E.monomial a).IsInvertible := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.isInvertible_monomial (T.X.left ↘ Spec (.of k)) T.E T.isSnc a

/-- The monomial part is invertible. -/
theorem isInvertible_monomialPart (T : Triple k) :
    (monomialPart T.I T.E).IsInvertible :=
  isInvertible_monomial T _

/-- `I = M(I) · N(I)` ([Kol07, Definition–Lemma 110]). -/
theorem monomialPart_mul_nonmonomialPart (T : Triple k) :
    monomialPart T.I T.E * nonmonomialPart T.I T.E = T.I := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.monomialPart_mul_nonmonomialPart (T.X.left ↘ Spec (.of k)) T.E T.isSnc T.I

/-- `ord_D N(I) = 0` at every component ([Kol07, Definition–Lemma 110]: "`cosupp N(I)` does not
contain any of the `E^i`", in the fine form). -/
theorem ord_nonmonomialPart_eq_zero [CharZero k] (T : Triple k) (i : T.E.ι) {η : T.X.left}
    (hη : η ∈ (T.E.component i).support.genericPoints) :
    (nonmonomialPart T.I T.E).ord η = 0 := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.ord_nonmonomialPart_eq_zero (T.X.left ↘ Spec (.of k)) T.E T.isSnc
    T.isNonzeroEverywhere hη

/-- `N(I)` is nonzero on every component. -/
theorem isNonzeroEverywhere_nonmonomialPart (T : Triple k) :
    IsNonzeroEverywhere (nonmonomialPart T.I T.E) :=
  isNonzeroEverywhere_nonmonomialPart_of T.isNonzeroEverywhere T.E

/-- The exponent of `M(I)` at `D` is `ord_D I`. -/
theorem ord_monomialPart_of_mem_genericPoints [CharZero k] (T : Triple k) (i : T.E.ι) {η : T.X.left}
    (hη : η ∈ (T.E.component i).support.genericPoints) :
    (monomialPart T.I T.E).ord η = T.I.ord η := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.ord_monomialPart_of_mem_genericPoints (T.X.left ↘ Spec (.of k)) T.E T.isSnc
    T.isNonzeroEverywhere hη

/-- The split is unique ([Kol07, Definition–Lemma 110]: "uniquely"). -/
theorem monomial_eq_monomialPart_of_mul_eq [CharZero k] (T : Triple k) {a : T.X.left → ℕ}
    {N : T.X.left.IdealSheafData}
    (h : T.E.monomial a * N = T.I)
    (hN : ∀ i : T.E.ι, ∀ η ∈ (T.E.component i).support.genericPoints, N.ord η = 0) :
    T.E.monomial a = monomialPart T.I T.E ∧ N = nonmonomialPart T.I T.E := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.monomial_eq_monomialPart_of_mul_eq (T.X.left ↘ Spec (.of k)) T.E T.isSnc T.I h hN

/-- The monomial part absorbs monomials ([Kol07, 111, Step 1]). -/
theorem monomialPart_monomial_mul [CharZero k] (T : Triple k) (a : T.X.left → ℕ)
    (J : T.X.left.IdealSheafData)
    (hJ : IsNonzeroEverywhere J) :
    monomialPart (T.E.monomial a * J) T.E = T.E.monomial a * monomialPart J T.E := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.monomialPart_monomial_mul (T.X.left ↘ Spec (.of k)) T.E T.isSnc a J hJ

/-- The nonmonomial part ignores monomials ([Kol07, 111, Step 1]). -/
theorem nonmonomialPart_monomial_mul [CharZero k] (T : Triple k) (a : T.X.left → ℕ)
    (J : T.X.left.IdealSheafData)
    (hJ : IsNonzeroEverywhere J) :
    nonmonomialPart (T.E.monomial a * J) T.E = nonmonomialPart J T.E := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.nonmonomialPart_monomial_mul (T.X.left ↘ Spec (.of k)) T.E T.isSnc a J hJ

/-- For `E = ∅`, `N(I) = I` (the last paragraph of [Kol07, 111]). -/
theorem nonmonomialPart_of_isEmpty (T : Triple k) (h : IsEmpty T.E.ι) :
    nonmonomialPart T.I T.E = T.I :=
  nonmonomialPart_of_isEmpty_of T.I T.E h

/-- An invertible ideal sheaf supported on `E` is its own monomial part ([BM08, (5.2)]: "`N(I)` is
divisible by no such prime ideal"). -/
theorem eq_monomialPart_of_isInvertible_of_support_le [CharZero k] (T : Triple k)
    {K : T.X.left.IdealSheafData} (hK : K.IsInvertible) (hsupp : K.support ≤ T.E.support) :
    K = monomialPart K T.E := by
  have := Hironaka.BD.noetherianSpace_triple T
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact Snc.eq_monomialPart_of_isInvertible_of_support_le (T.X.left ↘ Spec (.of k)) T.E
    T.isSnc hK hsupp

/-- `M(h^* I) = h^* M(I)` for a smooth `h`: the monomial part commutes with smooth pull-back. -/
theorem monomialPart_comap (T : Triple k) {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) : monomialPart T'.I T'.E = (monomialPart T.I T.E).comap h := by
  obtain ⟨-, hI, hE⟩ := hpb
  have hsnc' : (T.E.comap h).IsSnc := hE ▸ T'.isSnc
  have := Hironaka.BD.noetherianSpace_triple T'
  rw [hI, hE]
  exact monomialPart_comap_of_flat T h hsnc'

/-- `N(h^* I) = h^* N(I)` for a smooth `h`: the nonmonomial part commutes with smooth pull-back. -/
theorem nonmonomialPart_comap [CharZero k] (T : Triple k) {T' : Triple k} (h : T'.X.left ⟶ T.X.left)
    [Smooth h] (hpb : T'.IsPullbackOf T h) :
    nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap h := by
  obtain ⟨-, hI, hE⟩ := hpb
  have hsnc' : (T.E.comap h).IsSnc := hE ▸ T'.isSnc
  have := Hironaka.BD.noetherianSpace_triple T'
  have : IsLocallyNoetherian T'.X.left := (T'.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  rw [hI, hE]
  exact nonmonomialPart_comap_of_flat T (T'.X.left ↘ Spec (.of k)) h hsnc'

/-- The monomial part commutes with change of fields ([Kol07, 34.2]). -/
theorem monomialPart_baseChange (T : Triple k) {L : Type u} [Field L]
    {T' : Triple L} (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) :
    monomialPart T'.I T'.E = (monomialPart T.I T.E).comap p := by
  obtain ⟨hsq, hI, hE⟩ := hbc
  have hflat : Flat p := flat_of_isPullback_specMap hsq
  have hsnc' : (T.E.comap p).IsSnc := hE ▸ T'.isSnc
  have := Hironaka.BD.noetherianSpace_triple T'
  rw [hI, hE]
  exact monomialPart_comap_of_flat T p hsnc'

/-- The nonmonomial part commutes with change of fields ([Kol07, 34.2]). -/
theorem nonmonomialPart_baseChange [CharZero k] (T : Triple k) {L : Type u} [Field L] [CharZero L]
    {T' : Triple L} (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (hbc : T'.IsBaseChangeOf T σ p) :
    nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap p := by
  obtain ⟨hsq, hI, hE⟩ := hbc
  have hflat : Flat p := flat_of_isPullback_specMap hsq
  have hsnc' : (T.E.comap p).IsSnc := hE ▸ T'.isSnc
  have := Hironaka.BD.noetherianSpace_triple T'
  have : IsLocallyNoetherian T'.X.left := (T'.X.left ↘ Spec (.of L)).isLocallyNoetherian_of_field
  rw [hI, hE]
  exact nonmonomialPart_comap_of_flat T (T'.X.left ↘ Spec (.of L)) p hsnc'

end Hironaka.BMO
