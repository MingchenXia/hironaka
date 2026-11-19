/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional

/-!
# Two general lemmas for Definition 66

Two facts used to check the clauses of [Kol07, Definition 66] for a blow-up sequence, first on
the model of Kollár's Warning 63 (`HironakaExamples/Sequence/Remark33Warning63.lean`) and later
in the library:

* `hasSncWith_empty_of_smooth`: the empty family has simple normal crossings with every smooth
  center (adapted parameters, `exists_adaptedParameters_of_smooth`; [Kol07, Definition 24] for
  `E = ∅`);
* `leOrdAlong_one_of_le`: `ord_Z I ≥ 1` whenever `I ≤ Z` (the order along `Z` of
  [Kol07, Definition 47] is the order at its generic points).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence CoordinateSubspace
  affineBlowUpAlgebra Remark33 Algebra AlgebraicGeometry.Scheme.IdealSheafData MvPolynomial

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-! ### Two general lemmas for Definition 66 -/

section General

variable {k : Type u} [Field k]

/-- The empty family has simple normal crossings with every smooth center: at a point of the
center, adapted parameters (`exists_adaptedParameters_of_smooth`) are a regular system of
parameters an initial segment of which generates the center ([Kol07, Definition 24] for
`E = ∅`). -/
theorem hasSncWith_empty_of_smooth (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.Smooth f]
    (Z : X.IdealSheafData)
    [AlgebraicGeometry.Smooth (Z.subschemeι ≫ f)] : (DivisorFamily.empty X).HasSncWith Z := by
  intro x hx
  obtain ⟨m, c, y, -, hdim, hmax, hZ⟩ := exists_adaptedParameters_of_smooth f Z hx
  refine ⟨m, y, ⟨⟨hmax.symm, hdim⟩, fun i => i.1.elim, fun i => i.1.elim, fun i => i.1.elim⟩,
    Finset.univ.filter (fun j : Fin m => j.val < c), ?_⟩
  rw [hZ]
  congr 2
  ext j
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]

/-- `ord_Z I ≥ 1` when `I ≤ Z` (the order along `Z` of [Kol07, Definition 47] is the order at
its generic points): every generic point of `Z` lies in the support of `I`. -/
theorem leOrdAlong_one_of_le {I Z : X.IdealSheafData} (h : I ≤ Z) :
    I.LeOrdAlong Z.support ((1 : ℕ) : ℕ∞) := by
  intro η hη
  rw [Nat.cast_one, one_le_ord_iff]
  exact support_antitone h hη.1

end General

end Hironaka.Sequence
