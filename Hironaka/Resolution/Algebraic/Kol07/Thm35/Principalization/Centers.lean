/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.RefineFamily
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Sequence
import Hironaka.Scheme.BlowUpSequence.ConcatMarked
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The centers of the principalization sequence are smooth and have normal crossings with `E`

Clause (1) of [Kol07, Theorem 35]: every center of `BP(X, I, E)` is smooth and has simple normal
crossings with the running total transform of `E` [Kol07, Definition 25]. The two halves of the
definition give this for their own boundaries: `disjoinSeq_isSmooth` and `disjoinSeq_hasSncWith`
for the disjoining part against `E` itself, and the field `isOrderGeSeq` of the functor `BMO_1`
(the order condition of [Kol07, Definition 66]) for the `BMO_1` part against Kollár's ordered
family `∑ E^i`. But `∑ E^i` is the total transform of `E` at the end of the disjoining sequence
with the birational transforms of the original components collapsed into the one member `E^0`
("in (68) we allow the components of `E` to be reducible", [Kol07, 72]). Reading the clause
against the original `E` is a regrouping: the uncollapsed total transform subdivides the collapsed
one (`subdivides_collapse`; at any point at most one of the pairwise disjoint final strict
transforms passes, `meetLocus_strictTransformSeq_disjoinSeq`, so the collapsed member has the
stalk of that one member), and simple normal crossings pass to subdivisions along the whole
sequence (`isOrderGeSeq_of_subdivides`, the marked analogue of `isOrderSeq_of_subdivides`, both in
`Hironaka/Resolution/Algebraic/Kol07/RefineFamily.lean`).

The bookkeeping vehicle is `IsOrderGeSeq` at mark `0`: its order clause is vacuous
(`LeOrdAlong _ 0`), so `S.IsOrderGeSeq f ⊤ 0 E` says exactly "the centers of `S` are smooth and
have simple normal crossings with the total transforms of `E`", and the concatenation and
empty-blow-up transports for it are available (`isOrderGeSeq_concat`, `IsOrderGeSeq.eraseEmpty`).
`BP_isOrderGeSeq_zero` assembles them; `BP_center_smooth_hasSncWith` reads off clause (1).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Stage

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- "After `(k − 1)` steps we get rid of all pairwise intersections" [Kol07, 72], as the
disjointness hypothesis of `subdivides_collapse` for the collapse defining `collapsedFamily`: the
final birational transforms of two members of `E` never meet
(`meetLocus_strictTransformSeq_disjoinSeq`; the argument of `disjoinedFamily_isSnc`). -/
theorem disjoinedFamily_collapse_disjoint {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X) (hE : E.IsSnc) :
    ∀ (x : (disjoinSeq E).last) (a b : ((disjoinSeq E).totalTransformSeq E (Fin.last _)).ι),
      a ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _)) →
      b ∈ Set.range ((disjoinSeq E).originalIdx E (Fin.last _)) →
      x ∈ (((disjoinSeq E).totalTransformSeq E (Fin.last _)).component a).support →
      x ∈ (((disjoinSeq E).totalTransformSeq E (Fin.last _)).component b).support → a = b := by
  rintro x a b ⟨i, rfl⟩ ⟨j, rfl⟩ hxi hxj
  rw [component_originalIdx] at hxi hxj
  by_contra hne
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  have hx : x ∈ meetLocus
      (fun a => (disjoinSeq E).strictTransformSeq (E.component a) (Fin.last _)) 2 :=
    (mem_meetLocus_iff _ _ _).mpr ⟨{i, j}, Finset.card_pair hij, by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hxi
      · rw [Finset.mem_singleton.mp hl]
        exact hxj⟩
  rw [meetLocus_strictTransformSeq_disjoinSeq f E hE] at hx
  exact False.elim hx

variable {k : Type u} [Field k] [CharZero k]

/-- Clause (1) of [Kol07, Theorem 35] in the vehicle `IsOrderGeSeq` at mark `0`, whose order
clause is vacuous: `BP T` is a smooth blow-up sequence whose centers have simple normal crossings
with the total transforms of the original `E`. The disjoining part has this by construction, the
`BMO_1` part by the order condition of [Kol07, Definition 66] for the collapsed `∑ E^i`, regrouped
to the total transform of `E` through `subdivides_collapse` and `isOrderGeSeq_of_subdivides`; the
two are concatenated by `isOrderGeSeq_concat` and the empty blow-ups deleted by
`IsOrderGeSeq.eraseEmpty`. -/
theorem BP_isOrderGeSeq_zero (T : Triple k) :
    (BP T).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) ⊤ 0 T.E := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hS0 : (disjoinSeq T.E).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) ⊤ 0 T.E :=
    ⟨disjoinSeq_isSmooth (T.X.left ↘ Spec (.of k)) T.E T.isSnc,
      fun i => ⟨disjoinSeq_hasSncWith (T.X.left ↘ Spec (.of k)) T.E T.isSnc i, fun _ _ => zero_le⟩⟩
  have hR := (BMO_m 1 k).isOrderGeSeq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩
  have hR' : ((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩).IsOrderGeSeq
      ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k)))
      ((disjoinSeq T.E).markedTransformSeq ⊤ 0 (Fin.last _)) 0 (collapsedFamily _ T.E) :=
    ⟨hR.1, fun j => ⟨(hR.2 j).1, fun _ _ => zero_le⟩⟩
  have hsub : ((disjoinSeq T.E).totalTransformSeq T.E (Fin.last _)).Subdivides
      (collapsedFamily (disjoinSeq T.E) T.E) := by
    unfold collapsedFamily
    exact subdivides_collapse _ _
      (disjoinedFamily_collapse_disjoint (T.X.left ↘ Spec (.of k)) T.E T.isSnc)
  have hR0 := isOrderGeSeq_of_subdivides _ hsub hR'
  have hcat := isOrderGeSeq_concat (T.X.left ↘ Spec (.of k)) (disjoinSeq T.E) _ hS0 hR0
  exact IsOrderGeSeq.eraseEmpty (T.X.left ↘ Spec (.of k)) n hcat

/-- Clause (1) of [Kol07, Theorem 35]: every center of `BP T` is smooth over `k` and has simple
normal crossings with the total transform of `E` at its stage; read off `BP_isOrderGeSeq_zero`. -/
theorem BP_center_smooth_hasSncWith (T : Triple k) :
    ∀ i : Fin (BP T).length,
      Smooth (((BP T).center i).subschemeι ≫ (BP T).stageMap i.castSucc ≫
          (T.X.left ↘ Spec (CommRingCat.of k))) ∧
        ((BP T).totalTransformSeq T.E i.castSucc).HasSncWith ((BP T).center i) :=
  fun i => ⟨(BP_isOrderGeSeq_zero T).1 i, ((BP_isOrderGeSeq_zero T).2 i).1⟩

end Hironaka.Sequence
