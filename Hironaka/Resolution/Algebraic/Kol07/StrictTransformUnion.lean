/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Transform.Reduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Strict transforms of finite unions, monotonicity, reducedness

Three general facts about the strict transform of a closed subscheme along a blow-up sequence
([Kol07, Definition 30, 30.2]; the saturation of the pulled-back ideal by the exceptional ideal):

* the support of the strict transform of a finite union is the union of the strict transforms'
  supports (`coe_support_strictTransformSeq_biUnion`; one blow-up: `coe_support_strictTransform`
  describes the support as the closure of the preimage of `V(J)` minus the preimage of the centre,
  and closure commutes with finite unions);
* the strict transform is monotone in the ideal (`strictTransformSeq_mono`);
* the strict transform of a reduced closed subscheme is reduced
  (`isReduced_strictTransformSeq_subscheme`).

They are used by the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools`) and by the resolution functor on
reduced schemes with several irreducible components
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex`), where the centre containing the
strict transform of the whole scheme is compared with the centres containing the strict transforms
of its components.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

/-! ### Strict transforms of finite unions; monotonicity; reduced ideals of closed sets -/

section StrictTransform

variable {X : Scheme.{u}}

/-- One blow-up (`coe_support_strictTransform`): if `V(J)` is the finite union of the `V(c i)`,
the strict transform of `V(J)` is the union of the strict transforms of the `V(c i)`. -/
theorem coe_support_strictTransform_biUnion [IsLocallyNoetherian X] (D : X.IdealSheafData)
    {ι : Type*} (s : Set ι) (hs : s.Finite) (c : ι → X.IdealSheafData) (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = ⋃ i ∈ s, ((c i).support : Set X)) :
    ((J.strictTransform D).support : Set D.blowUp) =
      ⋃ i ∈ s, (((c i).strictTransform D).support : Set D.blowUp) := by
  simp only [coe_support_strictTransform]
  rw [hJ, Set.preimage_iUnion₂, ← hs.closure_biUnion]
  congr 1
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, hxD⟩
    exact ⟨i, hi, hx, hxD⟩
  · rintro ⟨i, hi, hx, hxD⟩
    exact ⟨⟨i, hi, hx⟩, hxD⟩

/-- Along a sequence (`⟨j, hj⟩` form): the strict transform of a finite union is the union of the
strict transforms. -/
theorem coe_support_strictTransformSeq_biUnion_mk (hX : IsLocallyNoetherian X)
    (S : BlowUpSequence X) {ι : Type*} (s : Set ι) (hs : s.Finite) (c : ι → X.IdealSheafData)
    (J : X.IdealSheafData) (hJ : (J.support : Set X) = ⋃ i ∈ s, ((c i).support : Set X)) (j : ℕ)
    (hj : j < S.length + 1) :
    ((S.strictTransformSeq J ⟨j, hj⟩).support : Set (S.stage ⟨j, hj⟩)) =
      ⋃ i ∈ s, ((S.strictTransformSeq (c i) ⟨j, hj⟩).support : Set (S.stage ⟨j, hj⟩)) := by
  induction S generalizing j with
  | nil X => exact hJ
  | cons X D rest ih =>
    cases j with
    | zero => exact hJ
    | succ j =>
      have hLN : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
      exact ih hLN (fun i => (c i).strictTransform D) (J.strictTransform D)
        (coe_support_strictTransform_biUnion D s hs c J hJ) j (Nat.lt_of_succ_lt_succ hj)

/-- Along a sequence: the strict transform of a finite union is the union of the strict
transforms. -/
theorem coe_support_strictTransformSeq_biUnion [hX : IsLocallyNoetherian X] (S : BlowUpSequence X)
    {ι : Type*} (s : Set ι) (hs : s.Finite) (c : ι → X.IdealSheafData) (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = ⋃ i ∈ s, ((c i).support : Set X)) (i : Fin (S.length + 1)) :
    ((S.strictTransformSeq J i).support : Set (S.stage i)) =
      ⋃ l ∈ s, ((S.strictTransformSeq (c l) i).support : Set (S.stage i)) := by
  obtain ⟨j, hj⟩ := i
  exact coe_support_strictTransformSeq_biUnion_mk hX S s hs c J hJ j hj

/-- The strict transform is monotone in the ideal (the saturation of a pull-back is). -/
theorem strictTransform_mono (D : X.IdealSheafData) {J K : X.IdealSheafData} (h : J ≤ K) :
    J.strictTransform D ≤ K.strictTransform D :=
  saturate_mono_left _ _ _ (comap_mono _ h)

/-- The strict transform along a sequence is monotone in the ideal (`⟨j, hj⟩` form). -/
theorem strictTransformSeq_mono_mk (S : BlowUpSequence X) {J K : X.IdealSheafData} (h : J ≤ K)
    (j : ℕ) (hj : j < S.length + 1) :
    S.strictTransformSeq J ⟨j, hj⟩ ≤ S.strictTransformSeq K ⟨j, hj⟩ := by
  induction S generalizing j with
  | nil X => exact h
  | cons X D rest ih =>
    cases j with
    | zero => exact h
    | succ j => exact ih (strictTransform_mono D h) j (Nat.lt_of_succ_lt_succ hj)

/-- The strict transform along a sequence is monotone in the ideal. -/
theorem strictTransformSeq_mono (S : BlowUpSequence X) {J K : X.IdealSheafData} (h : J ≤ K)
    (i : Fin (S.length + 1)) : S.strictTransformSeq J i ≤ S.strictTransformSeq K i := by
  obtain ⟨j, hj⟩ := i
  exact strictTransformSeq_mono_mk S h j hj

/-- The strict transform of a reduced closed subscheme along a sequence is reduced (`⟨j, hj⟩`
form; `isReduced_strictTransform_subscheme` at each step). -/
theorem isReduced_strictTransformSeq_subscheme_mk (S : BlowUpSequence X) (J : X.IdealSheafData)
    (hJ : IsReduced J.subscheme) (j : ℕ) (hj : j < S.length + 1) :
    IsReduced (S.strictTransformSeq J ⟨j, hj⟩).subscheme := by
  induction S generalizing j with
  | nil X => exact hJ
  | cons X D rest ih =>
    cases j with
    | zero => exact hJ
    | succ j =>
      exact ih (J.strictTransform D) (@isReduced_strictTransform_subscheme _ D J hJ)
        j (Nat.lt_of_succ_lt_succ hj)

/-- The strict transform of a reduced closed subscheme along a sequence is reduced. -/
theorem isReduced_strictTransformSeq_subscheme (S : BlowUpSequence X) (J : X.IdealSheafData)
    [hJ : IsReduced J.subscheme] (i : Fin (S.length + 1)) :
    IsReduced (S.strictTransformSeq J i).subscheme := by
  obtain ⟨j, hj⟩ := i
  exact isReduced_strictTransformSeq_subscheme_mk S J hJ j hj

end StrictTransform

end Hironaka.Resolution
