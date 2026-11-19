/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Basic
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The centres of an order reduction lie over the cosupport

For a marked ideal `(I, m)` and a blow-up sequence of order `≥ m` for it, the centre `Z_i` of the
`i`-th blow-up satisfies `ord_{Z_i} I_i ≥ m`, where `I_i` is the marked transform of `I` at stage
`i` [Kol07, Definition 60; Theorem 69]. Since the marked transform contains the pullback `Π_i^* I`
(it is the colon ideal `Π_i^* I : F^m` by the exceptional divisor `F`), `V(I_i) ⊆ Π_i^{-1}(V(I))`;
hence for `m ≥ 1` every centre lies over `V(I) = cosupp I`. This is the observation "by (21.2),
`π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄`" in the proof of [Kol07, Corollary 22], on which the identification of
the end result of the truncated sequence with an open subscheme of the last centre rests.

* `comap_stageMap_le_markedTransformSeq`: `Π_i^* I ≤ I_i` along any blow-up sequence.
* `stageMap_mem_support_of_mem_center`: for a blow-up sequence of order `≥ m` with `m ≥ 1`, the
  centres lie over `V(I)`.
* `stageMap_mem_support_of_mem_center_BP`: the same for the principalization sequence
  `BP(A, I, ∅)`: with an empty boundary it is the order reduction `BMO_1(A, I, 1, ∅)`
  (`BP_of_isEmpty`), a sequence of order `≥ 1` by the defining property of the functor.

The lemmas are used to place the centres of Kollár's resolution over the singular locus and, in
the form `stageMap_mem_support_of_mem_center_BP`, to identify the first centre containing the strict
transform of the embedded scheme (`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData Hironaka
  BlowUpSequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The pullback `Π_j^* I` is contained in the marked transform `I_j` of `(I, m)` along a
sequence, in the `⟨j, hj⟩` form of the indices: the colon ideal contains the ideal at every step. -/
theorem comap_stageMap_le_markedTransformSeq_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (I : X.IdealSheafData) (m j : ℕ) (hj : j < S.length + 1),
    I.comap (S.stageMap ⟨j, hj⟩) ≤ S.markedTransformSeq I m ⟨j, hj⟩
  | _, nil Y, I, m, j, hj => by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    change I.comap (𝟙 Y) ≤ I
    rw [Scheme.IdealSheafData.comap_id]
  | _, cons Y D rest, I, m, 0, hj => by
    change I.comap (𝟙 Y) ≤ I
    rw [Scheme.IdealSheafData.comap_id]
  | _, cons Y D rest, I, m, j + 1, hj => by
    change I.comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) ≤
      rest.markedTransformSeq (I.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    rw [Scheme.IdealSheafData.comap_comp]
    exact le_trans
      (Scheme.IdealSheafData.comap_mono (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
        (comap_le_controlledTransformAlong D.blowUpπ D.exceptionalDivisor
          I m))
      (comap_stageMap_le_markedTransformSeq_mk rest (I.markedTransform D m) m j _)

/-- The pullback `Π_i^* I` is contained in the marked transform `I_i` of `(I, m)` at stage `i` of
a blow-up sequence [Kol07, Definition 60]: the marked transform is a colon ideal of the pullback. -/
theorem comap_stageMap_le_markedTransformSeq (S : BlowUpSequence X) (I : X.IdealSheafData)
    (m : ℕ) (i : Fin (S.length + 1)) : I.comap (S.stageMap i) ≤ S.markedTransformSeq I m i := by
  obtain ⟨j, hj⟩ := i
  exact comap_stageMap_le_markedTransformSeq_mk S I m j hj

variable {k : Type u} [Field k] [CharZero k]

/-- In a blow-up sequence of order `≥ m` for `(I, m)` with `m ≥ 1` on an ambient `X` smooth over
`k` (the standing hypothesis under which the order is defined), every centre lies over `V(I)`
[Kol07, Definition 60; Theorem 69]: the order of the marked transform `I_i` is `≥ m ≥ 1` at every
point of the centre `Z_i` (semicontinuity), so `Z_i ⊆ V(I_i) ⊆ V(Π_i^* I) = Π_i^{-1}(V(I))`. -/
theorem stageMap_mem_support_of_mem_center (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderGeSeq f I m E) (hm : 1 ≤ m) (i : Fin S.length)
    {z : S.stage i.castSucc} (hz : z ∈ (S.center i).support) :
    S.stageMap i.castSucc z ∈ I.support := by
  have hsm : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap hS.1 i.castSucc
  have h1 : (m : ℕ∞) ≤ (S.markedTransformSeq I m i.castSucc).ord z :=
    (Scheme.IdealSheafData.leOrdAlong_iff_forall_mem _ (S.stageMap i.castSucc ≫ f) n _ _).1
      (IsOrderGeSeq.leOrdAlong hS i) z hz
  have h2 : z ∈ (S.markedTransformSeq I m i.castSucc).support :=
    (Scheme.IdealSheafData.one_le_ord_iff _ z).1 (le_trans (by exact_mod_cast hm) h1)
  have h3 : z ∈ (I.comap (S.stageMap i.castSucc)).support :=
    Scheme.IdealSheafData.support_antitone
      (comap_stageMap_le_markedTransformSeq S I m i.castSucc) h2
  exact (mem_support_comap_iff_apply I _ z).1 h3

/-- The centres of the principalization sequence `BP(A, I, ∅)` lie over `V(I)` ("by (21.2),
`π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄`" in the proof of [Kol07, Corollary 22]): with an empty boundary `BP` is
the order reduction `BMO_1(A, I, 1, ∅)` (`BP_of_isEmpty`), of order `≥ 1` for `(I, 1)`. -/
theorem stageMap_mem_support_of_mem_center_BP (TA : Triple k) (hE : IsEmpty TA.E.ι)
    (i : Fin (Hironaka.Sequence.BP TA).length) {z : (Hironaka.Sequence.BP TA).stage i.castSucc}
    (hz : z ∈ ((Hironaka.Sequence.BP TA).center i).support) :
    (Hironaka.Sequence.BP TA).stageMap i.castSucc z ∈ TA.I.support := by
  obtain ⟨n, hn⟩ := TA.smoothOfRelativeDimension
  have key : ∀ S : BlowUpSequence TA.X.left,
      S = (Hironaka.Stage.BMO_m 1 k).seq ⟨TA, 1⟩ ⟨le_rfl, rfl⟩ →
      ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ TA.I.support := by
    rintro S rfl i z hz
    exact stageMap_mem_support_of_mem_center (TA.X.left ↘ Spec (CommRingCat.of k)) n
      ((Hironaka.Stage.BMO_m 1 k).isOrderGeSeq ⟨TA, 1⟩ ⟨le_rfl, rfl⟩) le_rfl i hz
  exact key _ (Hironaka.Sequence.BP_of_isEmpty TA hE) i z hz

end Hironaka.Resolution
