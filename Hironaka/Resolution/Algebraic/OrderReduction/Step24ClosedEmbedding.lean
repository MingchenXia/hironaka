/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Assembly
public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.4 of order reduction: the marked triple on the hypersurface

Step 2.4 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.4]) proves clause (3): for a
smooth hypersurface `τ : Y ↪ X` and an ideal sheaf `J ⊂ 𝒪_Y`, nonzero on every irreducible
component of `Y`, with `τ_*(𝒪_Y/J) = 𝒪_X/I`, the ideal `I` contains the local equations of `Y` and
so has order `1`, whence `I = W(I)`; for `E = ∅`, Step 2.1 does nothing and Step 2.2 may take
`H = Y`, so that clause (3) of Theorem 103 follows from clause (3) of [Kol07, Lemma 102].

Clause (3) of [Kol07, Lemma 102] (`Hironaka.BD.hypersurfaceTriple` and
`Hironaka.BD.eq_pushforward_of_quotient` in `Hironaka/Resolution/Algebraic/BoundaryClearing/`) forms
its marked triple on a member of the boundary of the triple to which `BD_{n,1,j}` is applied. For
Step 2.4 that triple is the Step 2.2 input `(X_r, I_r, F_r + Y_r)` (`step22Triple` at the mark `1`
with `H := Y`), whose boundary has `Y_r` at position `0`, Kollár's `E^0 := H`; its exceptional part
`F_r` is empty because `E = ∅` and Step 2.1 is the empty sequence. This module provides:

* `maxOrd_le_one_of_eq_map_smoothDivisor`, `isMaximalContact_one_of_eq_map` and
  `bOClass_one_of_eq_map`, the consequences of `I = τ_*J` that put `(X, I, ∅)` in the class of
  `BO_{n,1}` with `Y` a hypersurface of maximal contact ("`I` contains the local equations of `Y`,
  and so it has order 1"), derived from `I = τ_*J` rather than assumed;
* `zero_lt_card_step22Triple` (position `0` of the Step 2.2 boundary exists) and
  `subscheme_nth_zero_step22Triple` (for `E = ∅` the member at position `0` is `Y` as a subscheme:
  Step 2.1 is the empty sequence, `card F_r.ι = 0`, `nth_append_last`);
* **`closedEmbeddingTriple`**, the marked triple `(Y_r, J, 1, (F_r − Y_r)|_{Y_r} + ⊤)` of clause (3)
  of Lemma 102 on the Step 2.2 triple, with `J` transported along the identification `e` of `Y_r`
  with `Y`, and its dimension bound `hasDimLE_closedEmbeddingTriple` (`≤ n − 1`).

The triple is formed on the Step 2.2 triple rather than directly on `Y` because the fields of an
abstract blow-up sequence functor relate its values only across `IsPullbackOf` and
`IsBaseChangeOf`, which preserve the index type of the boundary, and because the value of
`maxContactCase` unfolds to the pushforward of clause (3) of Lemma 102 on the Step 2.2 triple;
`Hironaka/Resolution/Algebraic/OrderReduction/ClosedEmbedding.lean` proves that identity.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData
  Scheme.BlowUpSequence Hironaka.Sequence Hironaka.Local

namespace Hironaka.BO

section Derived

variable {k : Type u} [Field k]

/-- If `I = τ_*J` for a smooth hypersurface `τ : Y ↪ X`, then `max-ord I ≤ 1` ([Kol07, 104,
Step 2.4]: "`I` contains the local equations of `Y`, and so it has order 1"): `I` contains the
ideal of `Y`, of order `1` along `Y`, and is the unit ideal off `Y`. -/
theorem maxOrd_le_one_of_eq_map_smoothDivisor (T : Triple k) {Y : T.X.left.IdealSheafData}
    (hY : IsSmoothDivisor Y) {J : Y.subscheme.IdealSheafData} (hIJ : T.I = J.map Y.subschemeι) :
    T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞) := by
  rw [maxOrd_le_iff]
  intro x
  by_cases hx : x ∈ Y.support
  · have h1 : Y.subschemeι.ker ≤ J.map Y.subschemeι := by
      rw [← Scheme.IdealSheafData.map_bot]
      exact Scheme.IdealSheafData.map_mono _ bot_le
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hIJ] at h1
    calc T.I.ord x ≤ Y.ord x := Scheme.IdealSheafData.ord_anti h1 x
      _ = 1 := hY.ord_eq_one hx
  · have hxI : x ∉ T.I.support := by
      intro hxm
      rw [hIJ, Scheme.IdealSheafData.support_map] at hxm
      have hsub : closure (Y.subschemeι '' J.support) ⊆ (Y.support : Set T.X.left) := by
        refine (closure_mono (Set.image_subset_range _ _)).trans ?_
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact Y.support.isClosed.closure_subset
      exact hx (hsub hxm)
    have : ¬ (1 : ℕ∞) ≤ T.I.ord x := fun h => hxI ((one_le_ord_iff _ _).mp h)
    exact (not_le.mp this).le

/-- Under `I = τ_*J`, `Y` is a hypersurface of maximal contact for `(I, 1)`:
`MC(I, 1) = D⁰(I) = I ⊇ 𝒪_X(−Y)` ([Kol07, 104, Step 2.4] with [Kol07, Theorem 80]); neither the
smoothness of `Y` nor the nonvanishing of `J` enters. -/
theorem isMaximalContact_one_of_eq_map (T : Triple k) {Y : T.X.left.IdealSheafData}
    (J : Y.subscheme.IdealSheafData) (hIJ : T.I = J.map Y.subschemeι) :
    IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 Y := by
  change Y ≤ T.I
  have h1 : Y.subschemeι.ker ≤ J.map Y.subschemeι := by
    rw [← Scheme.IdealSheafData.map_bot]
    exact Scheme.IdealSheafData.map_mono _ bot_le
  rw [Scheme.IdealSheafData.ker_subschemeι, ← hIJ] at h1
  exact h1

/-- Under `I = τ_*J`, `(X, I, E)` lies in the class of `BO_{n,1}` when `dim X ≤ n`
([Kol07, 104, Step 2.4]). -/
theorem bOClass_one_of_eq_map {n : ℕ} (T : Triple k) (hn : T.HasDimLE n)
    {Y : T.X.left.IdealSheafData}
    (hY : IsSmoothDivisor Y) {J : Y.subscheme.IdealSheafData} (hIJ : T.I = J.map Y.subschemeι) :
    Triple.BOClass n 1 T :=
  ⟨le_rfl, hn, maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ⟩

end Derived

/-- Nonvanishing on every component is preserved by transport along an equality of schemes. -/
theorem isNonzeroEverywhere_comap_eqToHom {X Y : Scheme.{u}} (e : X = Y) (J : Y.IdealSheafData)
    (hJ : IsNonzeroEverywhere J) : IsNonzeroEverywhere (J.comap (eqToHom e)) := by
  subst e
  rw [eqToHom_refl, Scheme.IdealSheafData.comap_id]
  exact hJ

section Position

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
  {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- The Step 2.2 boundary `F_r + H_r` has a member at position `0`. -/
theorem zero_lt_card_step22Triple :
    0 < Fintype.card (step22Triple T hn hmax bd hm hH hle).E.ι :=
  lt_of_le_of_lt (Nat.zero_le _) (card_lt_card_ι_append _ _)

/-- For an empty boundary the member at position `0` of the Step 2.2 boundary `F_r + H_r` is `H`
as a subscheme ([Kol07, 104, Step 2.4]: "if `E = ∅` then Step 2.1 does nothing, and in Step 2.2 we
can choose `H = Y`"): Step 2.1 is the empty sequence, `F_r` is empty and `H_r = H`
(`nth_append_last` at `card F_r.ι = 0`). -/
theorem subscheme_nth_zero_step22Triple (hE : IsEmpty T.E.ι) :
    ((step22Triple T hn hmax bd hm hH hle).E.nth
      ⟨0, zero_lt_card_step22Triple T hn hmax bd hm hH hle⟩).subscheme = H.subscheme := by
  have key : ∀ (j : ℕ) (_ : j = 0)
      (h₀ : 0 < Fintype.card (((step21Seq T hn hmax (bd m) j).1.exceptionalFamily T.E).append
        ((step21Seq T hn hmax (bd m) j).1.strictTransformSeq H (Fin.last _))).ι),
      ((((step21Seq T hn hmax (bd m) j).1.exceptionalFamily T.E).append
        ((step21Seq T hn hmax (bd m) j).1.strictTransformSeq H (Fin.last _))).nth
          ⟨0, h₀⟩).subscheme = H.subscheme := by
    intro j hj h₀
    subst hj
    have : IsEmpty ((step21Seq T hn hmax (bd m) 0).1.exceptionalFamily T.E).ι :=
      ⟨fun a => hE.elim a.1⟩
    have hidx : (⟨0, h₀⟩ : Fin _) =
        ⟨Fintype.card ((step21Seq T hn hmax (bd m) 0).1.exceptionalFamily T.E).ι,
          card_lt_card_ι_append _ _⟩ :=
      Fin.ext Fintype.card_eq_zero.symm
    calc ((((step21Seq T hn hmax (bd m) 0).1.exceptionalFamily T.E).append
            ((step21Seq T hn hmax (bd m) 0).1.strictTransformSeq H (Fin.last _))).nth
              ⟨0, h₀⟩).subscheme
        = ((((step21Seq T hn hmax (bd m) 0).1.exceptionalFamily T.E).append
            ((step21Seq T hn hmax (bd m) 0).1.strictTransformSeq H (Fin.last _))).nth
              ⟨Fintype.card ((step21Seq T hn hmax (bd m) 0).1.exceptionalFamily T.E).ι,
                card_lt_card_ι_append _ _⟩).subscheme := by rw [hidx]
      _ = ((step21Seq T hn hmax (bd m) 0).1.strictTransformSeq H (Fin.last _)).subscheme := by
          rw [nth_append_last]
      _ = H.subscheme := rfl
  have := hE
  exact key _ Fintype.card_eq_zero _

end Position

section ClosedEmbedding

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞)) (bd : ∀ m j : ℕ, BDData.{u} n m j)
  {Y : T.X.left.IdealSheafData} (hY : IsSmoothDivisor Y)
  (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 Y) (hE : IsEmpty T.E.ι)
  (J : Y.subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J)

/-- **The marked triple of the closed-embedding case** ([Kol07, 104, Step 2.4]; clause (3) of
[Kol07, Lemma 102]): `Hironaka.BD.hypersurfaceTriple` on the Step 2.2 triple `(X_r, I_r, F_r + Y_r)`
at the mark `1` (`step22Triple` with `H := Y`), at the position `0` of `Y_r` (Kollár's
`E^0 := H`), with `J` transported along the identification of `Y_r` with `Y`
(`subscheme_nth_zero_step22Triple`; Step 2.1 is the empty sequence). Its boundary is
`(F_r − Y_r)|_{Y_r} + ⊤`, propositionally `∅ + ⊤`, the appended empty member in the convention of
`hypersurfaceTriple`. -/
noncomputable def closedEmbeddingTriple : MarkedTriple k :=
  Hironaka.BD.hypersurfaceTriple (step22Triple T hn hmax bd le_rfl hY hle)
    (zero_lt_card_step22Triple T hn hmax bd le_rfl hY hle)
    (J.comap (eqToHom (subscheme_nth_zero_step22Triple T hn hmax bd le_rfl hY hle hE)))
    (isNonzeroEverywhere_comap_eqToHom _ J hJ)

/-- The marked triple of the closed-embedding case has dimension `≤ n − 1` when `X` has dimension
`≤ n` ([Kol07, 104, Step 2.4]: the functor `BMO_{n−1,1}`), by
`Hironaka.BD.hasDimLE_hypersurfaceTriple` on the Step 2.2 triple, of dimension `≤ n` by
`bdClass_step22Triple`. -/
theorem hasDimLE_closedEmbeddingTriple :
    (closedEmbeddingTriple T hn hmax bd hY hle hE J hJ).toTriple.HasDimLE (n - 1) :=
  Hironaka.BD.hasDimLE_hypersurfaceTriple _ _ _ _
    (bdClass_step22Triple T hn hmax bd le_rfl hY hle).1

end ClosedEmbedding

end Hironaka.BO
