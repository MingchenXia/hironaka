/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeq
public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.BlowUpSequence.CentersCosupport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Étale equivalent hypersurfaces give étale equivalent blow-up sequences

In [Kol07, Theorem 103, Step 2.3], for two hypersurfaces of maximal contact `H, H'` such that
`H + E` and `H' + E` are simple normal crossing divisors, Theorem 92 makes `(X, I, H + E)` and
`(X, I, H' + E)` étale equivalent, and Kollár concludes that the two blow-up sequences
`BD_{n,m,0}(X, I, H + E)` and `BD_{n,m,0}(X, I, H' + E)` "are also étale equivalent". The
introduction of [Kol07, §10] makes the same argument for an automorphism `φ` in place of the
étale pair. This file proves that conclusion for an arbitrary functor, without deleting empty
blow-ups:

Let `B` be a smooth blow-up sequence functor of order `m` (`OrderSeqFunctor`) that commutes with
smooth morphisms in the sense of [Kol07, 34.1] (`CommutesWithSmooth`), and let `Q = (U, ψ, ψ')` be
an étale equivalence of `H` and `H'` with respect to `(X, I, E)` (`EtaleEquiv`). Write
`T = (X, I, H + E)`, `T' = (X, I, H' + E)`.

* By the second clause of [Kol07, 34.1], `B(ψ^*T) = del(ψ^* B(T))` and
  `B(ψ'^*T') = del(ψ'^* B(T'))`, where `del` deletes the empty blow-ups (`eraseEmpty`). No
  deletion occurs: `B(T)` has no empty centre (the output convention of the named functors,
  [Kol07, 32], `OrderSeqAssignment.noEmptyCenters`) and every centre of the order-`m` sequence
  `B(T)` lies over `cosupp(I, m) ⊆ im ψ`, so no centre of `ψ^* B(T)` is empty
  (`noEmptyCenters_pullback_of_centersInRange`) and `eraseEmpty` is the identity on it
  (`eraseEmpty_eq_self_iff`).
* The two pulled-back triples on `U` are **equal**: `ψ^*I = ψ'^*I` is (2′), and
  `ψ^{-1}(H + E) = ψ'^{-1}(H' + E)` componentwise is (1′) with (3′)
  (`DivisorFamily.comap_append_eq`); the `k`-structure of `U` is the one of the ambient `Over`
  instance on both sides (`Triple.pullback_eq_pullback`). Hence `B(ψ^*T) = B(ψ'^*T')`
  (`OrderSeqAssignment.seq_congr`).
* Therefore `ψ^* B(T) = ψ'^* B(T')`, which is condition (3) of [Kol07, Definition 96] for the two
  outputs; conditions (1) and (2) are (2′) and (4′) of `Q`, and the covering conditions and
  `ψ ≫ f = ψ' ≫ f` are `Q`'s: `B(T)` and `B(T')` are étale equivalent through the same
  `(U, ψ, ψ')` (`etaleEquivSeq_of_functor`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme Algebra

namespace Hironaka

open Scheme

variable {k : Type u} [Field k]

/-- The value of a blow-up sequence functor depends only on the triple, not on the proof of class
membership; stated as a `HEq` because the ambient schemes of the two triples are equal only
propositionally. -/
theorem OrderSeqAssignment.seq_congr {m : ℕ} {Dom : Triple k → Prop}
    (B : OrderSeqAssignment k m Dom)
    {T₁ T₂ : Triple k} (h : T₁ = T₂) (h₁ : Dom T₁) (h₂ : Dom T₂) :
    HEq (B.seq T₁ h₁) (B.seq T₂ h₂) := by
  subst h
  rfl

/-- Two pull-backs of triples along maps from the same `Y` (with `Y`'s given `k`-structure) are
equal when the pulled-back ideals and divisor families agree. -/
theorem _root_.AlgebraicGeometry.Triple.pullback_eq_pullback [PerfectField k] (T T' : Triple k)
    {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (hY : ∃ n : ℕ, SmoothOfRelativeDimension n (Y ↘ Spec (.of k))) (ψ : Y ⟶ T.X.left)
    (ψ' : Y ⟶ T'.X.left)
    [AlgebraicGeometry.Smooth ψ] [AlgebraicGeometry.Smooth ψ']
    (hI : T.I.comap ψ = T'.I.comap ψ') (hE : T.E.comap ψ = T'.E.comap ψ') :
    T.pullback hY ψ = T'.pullback hY ψ' := by
  unfold Triple.pullback
  congr 1

/-- The conditions (1′) and (3′) of [Kol07, Definition 91] read on the family `H + E`:
`ψ^{-1}(H + E) = ψ'^{-1}(H' + E)` when `ψ^{-1}H = ψ'^{-1}H'` and `ψ^{-1}E^i = ψ'^{-1}E^i` for
every component; `H + E` is `E.append H`, with `H` the last member. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.comap_append_eq {X U : Scheme.{u}}
    (E : DivisorFamily X)
    (H H' : X.IdealSheafData) (ψ ψ' : U ⟶ X) (h1 : H.comap ψ = H'.comap ψ')
    (h3 : ∀ i, (E.component i).comap ψ = (E.component i).comap ψ') :
    (E.append H).comap ψ = (E.append H').comap ψ' := by
  unfold DivisorFamily.append DivisorFamily.comap
  congr 1
  funext i
  cases i with
  | inl j => exact h3 j
  | inr u => exact h1

end Hironaka

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k]

/-- Kollár's conclusion in [Kol07, Theorem 103, Step 2.3] that the two blow-up sequences
`BD_{n,m,0}(X, I, H + E)` and `BD_{n,m,0}(X, I, H' + E)` are étale equivalent, for an arbitrary
functor: for a
smooth blow-up sequence functor `B` of order `m` commuting with smooth morphisms
(`CommutesWithSmooth`), a triple `T = (X, I, H + E)` of its class, the triple `T' = (X, I, H' + E)`
(`H' + E` simple normal crossing, also in the class), and an étale equivalence `Q = (U, ψ, ψ')` of
`H` and `H'` with respect to `(X, I, E)` whose `U` carries the hypotheses of [Kol07, 34.1] and
whose pulled-back triples `ψ^*T`, `ψ'^*T'` lie in the class, `B(T)` and `B(T')` are étale
equivalent blow-up sequences through `(U, ψ, ψ')`: `ψ^* B(T) = B(ψ^*T) = B(ψ'^*T') = ψ'^* B(T')`,
by [Kol07, 34.1] without deletion (`OrderSeqAssignment.noEmptyCenters` and the centres lying over
the cosupport) and the equality of the pulled-back triples from (1′)–(3′). -/
theorem etaleEquivSeq_of_functor [CharZero k] {m : ℕ} {Dom : Triple k → Prop}
    (B : OrderSeqAssignment k m Dom) (hB : B.CommutesWithSmooth) (T : Triple k) (hT : Dom T)
    (E : DivisorFamily T.X.left) (H H' : T.X.left.IdealSheafData) (hE : T.E = E.append H)
    (hsnc' : (E.append H').IsSnc) (hT' : Dom { T with E := E.append H', isSnc := hsnc' })
    (Q : EtaleEquiv (T.X.left ↘ Spec (.of k)) T.I m E H H') [Q.U.Over (Spec (.of k))]
    [Q.ψ.IsOver (Spec (.of k))] [QuasiCompact (Q.U ↘ Spec (.of k))]
    [IsSeparated (Q.U ↘ Spec (.of k))]
    (hU : ∃ n : ℕ, SmoothOfRelativeDimension n (Q.U ↘ Spec (.of k)))
    (hDU : Dom (T.pullback hU Q.ψ))
    (hDU' : haveI := Q.isOver_ψ'
      Dom (Triple.pullback { T with E := E.append H', isSnc := hsnc' } hU Q.ψ')) :
    Nonempty (EtaleEquivSeq (T.X.left ↘ Spec (.of k)) T.I m (B.seq T hT)
      (B.seq { T with E := E.append H', isSnc := hsnc' } hT')) := by
  have := Q.isOver_ψ'
  have hsψ : Smooth Q.ψ := inferInstance
  have hsψ' : Smooth Q.ψ' := inferInstance
  set T' : Triple k := { T with E := E.append H', isSnc := hsnc' } with hT'def
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hne : ((B.seq T hT).pullback Q.ψ).NoEmptyCenters :=
    noEmptyCenters_pullback_of_centersInRange Q.ψ (B.noEmptyCenters T hT)
      (centersInRange_of_cosupp_le_range (T.X.left ↘ Spec (.of k)) n
        (B.isOrderSeq T hT) Q.ψ Q.covers)
  have hne' : ((B.seq T' hT').pullback Q.ψ').NoEmptyCenters :=
    noEmptyCenters_pullback_of_centersInRange Q.ψ' (B.noEmptyCenters T' hT')
      (centersInRange_of_cosupp_le_range (T.X.left ↘ Spec (.of k)) n (B.isOrderSeq T' hT') Q.ψ'
        Q.covers')
  have hcomm := hB.2
  have e1 : B.seq (T.pullback hU Q.ψ) hDU = ((B.seq T hT).pullback Q.ψ).eraseEmpty :=
    @hcomm T (T.pullback hU Q.ψ) Q.ψ hsψ (Triple.isPullbackOf_pullback T hU Q.ψ) hT hDU
  have e1' : B.seq (Triple.pullback T' hU Q.ψ') hDU' =
      ((B.seq T' hT').pullback Q.ψ').eraseEmpty :=
    @hcomm T' (T'.pullback hU Q.ψ') Q.ψ' hsψ' (Triple.isPullbackOf_pullback T' hU Q.ψ') hT' hDU'
  have hTT : T.pullback hU Q.ψ = T'.pullback hU Q.ψ' :=
    Triple.pullback_eq_pullback T T' hU Q.ψ Q.ψ' Q.h2
      (by rw [hE]; exact DivisorFamily.comap_append_eq E H H' Q.ψ Q.ψ' Q.h1 Q.h3)
  have h3 : (B.seq T hT).pullback Q.ψ = (B.seq T' hT').pullback Q.ψ' := by
    rw [← (eraseEmpty_eq_self_iff _).mpr hne, ← (eraseEmpty_eq_self_iff _).mpr hne', ← e1, ← e1']
    exact eq_of_heq (B.seq_congr hTT hDU hDU')
  exact ⟨{ Q.toEtaleImagePair with comp_eq := Q.comp_eq, h1 := Q.h2, h2 := Q.h4, h3 := h3 }⟩

end AlgebraicGeometry.Scheme.IdealSheafData
