/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.MaximalContact.GoingDown
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Corollary 85: going up and down

[Kol07, Corollary 85]: for `I` D-balanced with `m = max-ord I`, `E` simple normal crossing, `H` a
smooth hypersurface of maximal contact ([Kol07, Definition 78]) with `E + H` simple normal
crossing and no irreducible component of `H` in `cosupp(I, m)`, pushing forward from `H` to `X` is
a one-to-one correspondence between the smooth blow-up sequences of order `≥ m` starting with
`(H, I|_H, m, E|_H)` and those of order `m` starting with `(X, I, E)`. Kollár's proof says that
this follows from Theorems 84 and 80 except for the role of `E`:

* well defined: [Kol07, Theorem 84] (going up) with the divisor family carried
  (`IsDBalanced.isOrderSeq_pushforward` of `Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`);
* injective: `pushforward_injective`;
* onto: going down (`isOrderGeSeq_pullback_of_strictTransformSeq_le` of
  `Hironaka/Resolution/Algebraic/MaximalContact/GoingDown.lean`) with `j_* j^* B = B`
  (`pushforward_pullback_of_strictTransformSeq_le`), the centres of an order-`m` sequence for
  `(X, I, E)` lying in the strict transforms `H_i` by Definition 78 read on `X` itself
  (`strictTransformSeq_le_center_of_isDynamicMaximalContact`). Definition 78 is stated for the
  empty divisor family, so the sequence's family is first dropped
  (`IsOrderSeq.empty_of_isOrderSeq`): the exceptional divisors form a sub-family of the induced
  family `E_i` at every stage (`exists_isSubfamilyVia_totalTransformSeq`), and simple normal
  crossings with a family pass to its sub-families (`hasSncWith_of_isSubfamilyVia`).

The static instance (`IsDBalanced.bijOn_pushforward_of_isMaximalContact`, with `H` of maximal
contact in the sense of [Kol07, Theorem 80 (1)] and `1 ≤ m`) takes the containment of the centres
from `IsOrderSeq.strictTransformSeq_le_center_of_le_MC` instead.

**Convention.** The hypothesis `_hHc`, that no irreducible component of `H` lies in
`cosupp(I, m)`, is part of Kollár's statement of Corollary 85 (as `S ⊄ cosupp(I, m)` is of his
Theorem 84) and is kept in both theorems so that they read as printed. The proofs do not need it:
the correspondence is assembled from the library's Theorem 84
(`IsDBalanced.isOrderSeq_pushforward`), which is stated and proved without that hypothesis (the
sheaf-level Lemma 62 it iterates, `markedTransform_comap_blowUpMap_of_pow_dvd`, needs only
`F^m ∣ π^* I`), and from going down, which uses only that the centres lie in the `H_i`. The
sub-family lemmas of the first section are also used by
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Sub-families and simple normal crossings -/

/-- `F'` is a sub-family of `F` via `σ`: an injection of indices matching the components. -/
def IsSubfamilyVia (F' F : DivisorFamily X) (σ : F'.ι → F.ι) : Prop :=
  Function.Injective σ ∧ ∀ a, F.component (σ a) = F'.component a

/-- Simple normal crossings with a family pass to its sub-families: the same adapted coordinates,
the index map composed with the inclusion of indices. -/
theorem hasSncWith_of_isSubfamilyVia {F' F : DivisorFamily X} {σ : F'.ι → F.ι}
    (hσ : IsSubfamilyVia F' F σ) {Z : X.IdealSheafData} (h : F.HasSncWith Z) :
    F'.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hz, c, hcinj, hcF⟩, s, hs⟩ := h x hx
  have hmem : ∀ a : F'.ι, x ∈ (F'.component a).support → x ∈ (F.component (σ a)).support :=
    fun a ha => by rw [hσ.2 a]; exact ha
  refine ⟨n, z, ⟨hz, fun a => c ⟨σ a.1, hmem a.1 a.2⟩, fun a a' haa' => ?_, fun a => ?_⟩, s, hs⟩
  · exact Subtype.ext (hσ.1 (congrArg Subtype.val (hcinj haa')))
  · exact
      (congrArg (fun W : X.IdealSheafData => W.stalkIdeal x)
          (hσ.2 a.1)).symm.trans
      (hcF ⟨σ a.1, hmem a.1 a.2⟩)

/-- The total transform of a sub-family is a sub-family of the total transform (the exceptional
divisor is matched with itself). -/
theorem isSubfamilyVia_totalTransform {F' F : DivisorFamily X} {σ : F'.ι → F.ι}
    (hσ : IsSubfamilyVia F' F σ) (D : X.IdealSheafData) :
    IsSubfamilyVia (F'.totalTransform D) (F.totalTransform D)
      (fun a => toLex (Sum.map σ id (ofLex a))) := by
  refine ⟨fun a a' h => ?_, fun a => ?_⟩
  · exact ofLex.injective ((hσ.1.sumMap Function.injective_id) (toLex.injective h))
  · rcases ha : ofLex a with e | u
    · have : a = toLex (Sum.inl e) := congrArg toLex ha
      subst this
      change (F.component (σ e)).strictTransform D = (F'.component e).strictTransform D
      rw [hσ.2 e]
    · cases u
      have : a = toLex (Sum.inr PUnit.unit) := congrArg toLex ha
      subst this
      rfl

/-- Along a blow-up sequence, the induced family of a sub-family is a sub-family of the induced
family at every stage. -/
theorem exists_isSubfamilyVia_totalTransformSeq (S : BlowUpSequence X) {F' F : DivisorFamily X}
    (σ : F'.ι → F.ι) (hσ : IsSubfamilyVia F' F σ) (i : Fin (S.length + 1)) :
    ∃ τ : (S.totalTransformSeq F' i).ι → (S.totalTransformSeq F i).ι,
      IsSubfamilyVia (S.totalTransformSeq F' i) (S.totalTransformSeq F i) τ := by
  induction S with
  | nil _ => exact ⟨σ, hσ⟩
  | cons X D rest ih =>
    obtain ⟨j, hj⟩ := i
    cases j with
    | zero => exact ⟨σ, hσ⟩
    | succ j =>
      exact ih _ (isSubfamilyVia_totalTransform hσ D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- The empty family is a sub-family of every family. -/
theorem empty_isSubfamilyVia (E : DivisorFamily X) :
    IsSubfamilyVia (DivisorFamily.empty X) E (fun a => a.elim) :=
  ⟨fun a => a.elim, fun a => a.elim⟩

section Drop

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : DivisorFamily X)
  (m : ℕ)

/-- Dropping the divisor family: a smooth blow-up sequence of order `m` for `(X, I, E)` is one for
`(X, I)` with the empty family — its centres have simple normal crossings with the exceptional
divisors, a sub-family of the induced families `E_i`. -/
theorem IsOrderSeq.empty_of_isOrderSeq {S : BlowUpSequence X} (h : S.IsOrderSeq f I E m) :
    S.IsOrderSeq f I (DivisorFamily.empty X) m := by
  refine ⟨h.1, fun i => ⟨?_, (h.2 i).2⟩⟩
  obtain ⟨τ, hτ⟩ := exists_isSubfamilyVia_totalTransformSeq S _ (empty_isSubfamilyVia E) i.castSucc
  exact hasSncWith_of_isSubfamilyVia hτ (h.2 i).1

end Drop

/-! ### Corollary 85 -/

section Cor85

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

include n in
/-- **[Kol07, Corollary 85]** (going up and down): `X` a smooth variety, `I` D-balanced with
`m = max-ord I`, `E` simple normal crossing, `H ⊂ X` a smooth hypersurface of maximal contact
([Kol07, Definition 78]) with `E + H` simple normal crossing and no irreducible component of `H`
in `cosupp(I, m)`; pushing forward from `H` to `X` is a one-to-one correspondence between the
smooth blow-up sequences of order `≥ m` starting with `(H, I|_H, m, E|_H)` and those of order `m`
starting with `(X, I, E)`: well defined by [Kol07, Theorem 84] with `E` carried, injective by
`pushforward_injective`, onto by going down and `j_* j^* B = B`, the centres lying in the `H_i` by
Definition 78 read on `X` itself after dropping `E`. The hypothesis `_hHc` on the components of
`H` is part of Kollár's statement and is kept so that the theorem reads as printed; the proof
does not need it, because `IsDBalanced.isOrderSeq_pushforward` and
`isOrderGeSeq_pullback_of_strictTransformSeq_le` are both proved without it (module docstring,
**Convention**). -/
theorem IsDBalanced.bijOn_pushforward (H : X.IdealSheafData) (hI : I.IsDBalanced f m)
    (hmax : I.maxOrd = m) (hH : IsSmoothDivisor H) (hE : (E.append H).IsSnc)
    (hMC : IsDynamicMaximalContact f I m H)
    (_hHc : ∀ η ∈ H.support.genericPoints, I.ord η < (m : ℕ∞)) :
    Set.BijOn (fun T : BlowUpSequence H.subscheme => T.pushforward H.subschemeι)
      {T | T.IsOrderGeSeq (H.subschemeι ≫ f) (I.comap H.subschemeι) m (E.comap H.subschemeι)}
      {B | B.IsOrderSeq f I E m} := by
  refine ⟨fun T hT => ?_, fun T _ T' _ h => pushforward_injective H.subschemeι h, fun B hB => ?_⟩
  · exact IsDBalanced.isOrderSeq_pushforward f n H I E m T hI hmax hH hE hT
  · have hB : B.IsOrderSeq f I E m := hB
    have hZ : ∀ i : Fin B.length, B.strictTransformSeq H i.castSucc ≤ B.center i :=
      strictTransformSeq_le_center_of_isDynamicMaximalContact f I H m B hMC
        (IsOrderSeq.empty_of_isOrderSeq f I E m hB)
    refine ⟨B.pullback H.subschemeι, ?_, ?_⟩
    · exact isOrderGeSeq_pullback_of_strictTransformSeq_le f n I H E m B hH hE hB hZ
    · exact pushforward_pullback_of_strictTransformSeq_le B H.subschemeι
        (by rw [ker_subschemeι]; exact hZ)

include n in
/-- [Kol07, Corollary 85] with `H` of maximal contact in the static sense of
[Kol07, Theorem 80 (1)], `𝒪_X(−H) ⊆ MC(I)`, and `1 ≤ m`; the centres of an order-`m` sequence lie
in the `H_i` by `IsOrderSeq.strictTransformSeq_le_center_of_le_MC`. The hypothesis `_hHc` on the
components of `H` is part of Kollár's statement and is kept so that the theorem reads as printed;
the proof does not need it, for the reason given in the module docstring (**Convention**). -/
theorem IsDBalanced.bijOn_pushforward_of_isMaximalContact (H : X.IdealSheafData)
    (hI : I.IsDBalanced f m) (hmax : I.maxOrd = m) (hm : 1 ≤ m) (hH : IsSmoothDivisor H)
    (hE : (E.append H).IsSnc) (hMC : IsMaximalContact f I m H)
    (_hHc : ∀ η ∈ H.support.genericPoints, I.ord η < (m : ℕ∞)) :
    Set.BijOn (fun T : BlowUpSequence H.subscheme => T.pushforward H.subschemeι)
      {T | T.IsOrderGeSeq (H.subschemeι ≫ f) (I.comap H.subschemeι) m (E.comap H.subschemeι)}
      {B | B.IsOrderSeq f I E m} := by
  refine ⟨fun T hT => ?_, fun T _ T' _ h => pushforward_injective H.subschemeι h, fun B hB => ?_⟩
  · exact IsDBalanced.isOrderSeq_pushforward f n H I E m T hI hmax hH hE hT
  · have hB : B.IsOrderSeq f I E m := hB
    have hZ : ∀ i : Fin B.length, B.strictTransformSeq H i.castSucc ≤ B.center i := fun i =>
      IsOrderSeq.strictTransformSeq_le_center_of_le_MC f n hm hB hH hMC i
    refine ⟨B.pullback H.subschemeι, ?_, ?_⟩
    · exact isOrderGeSeq_pullback_of_strictTransformSeq_le f n I H E m B hH hE hB hZ
    · exact pushforward_pullback_of_strictTransformSeq_le B H.subschemeι
        (by rw [ker_subschemeι]; exact hZ)

end Cor85

end Hironaka.Sequence
