/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loop's round at stage `0`

The round of the loop (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) is built from `bmoOneRun T
hm`; its isolated triple and remaining members are `isolatedAt` and `remainingAt` at the truncated
run. To compute a round at stage `0` one needs the run's constructor: for a run `cons X D rest`
(reached by `subst` from an equation `bmoOneRun T hm = cons X D rest`) the truncation at `0` is
empty, so

* `isolatedAt_cons_zero_I`: the isolated ideal is `T.I : I_Γ` with `I_Γ` the reduced ideal of the
  union of the absorbed members;
* `isolatedAt_cons_zero_E`: the boundary is unchanged; `remainingAt_cons_zero`: the remaining
  members are unchanged (the strict transform at stage `0` is the ideal itself);
* `filter_centerContains_cons_zero`: the members absorbed at stage `0` are those contained in the
  first centre `D` (`D ≤ c`, `CenterContains` at `0` on a `cons`).

These are unfoldings of the definitions, used by
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Cons

variable (T : MarkedTriple k) (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp)
  (hQ : ((BlowUpSequence.cons T.X.left D rest).take 0).IsOrderGeSeq
    (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
  (C : Finset T.X.left.IdealSheafData)

omit [CharZero k] in
/-- The stop rule at stage `0` on `cons X D rest` is containment in the first centre. -/
theorem centerContains_cons_zero_iff (c : T.X.left.IdealSheafData) :
    CenterContains (BlowUpSequence.cons T.X.left D rest) c 0 ↔ D ≤ c :=
  ⟨fun h => h.2, fun h => ⟨Nat.succ_pos _, h⟩⟩

open Classical in
omit [CharZero k] in
/-- The members absorbed at stage `0` of a run `cons X D rest` are those contained in `D`. -/
theorem filter_centerContains_cons_zero :
    C.filter (fun c => CenterContains (BlowUpSequence.cons T.X.left D rest) c 0) =
      C.filter (fun c => D ≤ c) :=
  Finset.filter_congr fun c _ => centerContains_cons_zero_iff T D rest c

open Classical in
omit [CharZero k] in
/-- The members not absorbed at stage `0` of a run `cons X D rest` are those not contained in
`D`. -/
theorem filter_not_centerContains_cons_zero :
    C.filter (fun c => ¬ CenterContains (BlowUpSequence.cons T.X.left D rest) c 0) =
      C.filter (fun c => ¬ D ≤ c) :=
  Finset.filter_congr fun c _ => not_congr (centerContains_cons_zero_iff T D rest c)

/-- At stage `0` of a run `cons X D rest`, the isolated ideal is the colon of `T.I` by the reduced
ideal of the union of the absorbed members. -/
theorem isolatedAt_cons_zero_I :
    (isolatedAt T ((BlowUpSequence.cons T.X.left D rest).take 0) hQ C).I =
      T.I.colon (IdealSheafData.vanishingIdeal (⨆ c ∈ C, c.support)) := by
  unfold isolatedAt
  dsimp only
  rfl

/-- At stage `0` of a run `cons X D rest`, the boundary of the isolated triple is `T.E`. -/
theorem isolatedAt_cons_zero_E :
    (isolatedAt T ((BlowUpSequence.cons T.X.left D rest).take 0) hQ C).E = T.E :=
  rfl

open Classical in
omit [CharZero k] in
/-- At stage `0` of a run `cons X D rest`, the remaining members are the members themselves. -/
theorem remainingAt_cons_zero : remainingAt ((BlowUpSequence.cons T.X.left D rest).take 0) C = C :=
  Finset.image_id'

end Cons

end Hironaka.Resolution
