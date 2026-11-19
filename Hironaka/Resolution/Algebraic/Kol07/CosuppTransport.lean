/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The cosupport under a blow-up whose center lies in it

The boundary-clearing step of the proof of Theorem 103 [Kol07, 104, Step 2.1] keeps the
birational transforms of the already cleared members `E^i` (`i < j`) disjoint from the cosupport
while `BD_{n,m,j}` blows up centers inside `cosupp(I, m)`. The fact behind it: under one blow-up
with center `Z ⊆ cosupp(I, m)`, a point of `cosupp(π_*^{-1} I, m)` maps to a point of
`cosupp(I, m)`. Over `Z` this holds because `Z ⊆ cosupp(I, m)`; off the exceptional divisor because
the weak transform is the pull-back there (the exceptional factor is the unit ideal,
`stalkIdeal_weakTransform_of_notMem`), `π` is a local isomorphism
(`isIso_stalkMap_π_of_notMem_support`), and the order is a stalk invariant (`ord_map_ringEquiv`);
this is `le_ord_of_le_ord_weakTransform`. Hence a divisor disjoint from the cosupport has
birational transform disjoint from the cosupport of the weak transform
(`disjoint_cosupp_strictTransform_of_disjoint`, with `coe_support_strictTransform`), and along a
smooth blow-up sequence of order `m`, whose centers lie in the cosupport by condition (4) of
[Kol07, Definition 66] and upper semicontinuity (`le_ord_of_mem_center`), the disjointness persists
to the end (`disjoint_cosupp_strictTransformSeq_last_of_disjoint`).

The weak transform is the birational transform `π_*^{-1} I` of [Kol07, 58].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Off the exceptional divisor the weak transform (the birational transform of [Kol07, 58]) has
the stalk of the pull-back: the exceptional factor is the unit ideal there, and a colon by the unit
ideal is the ideal itself. -/
theorem stalkIdeal_weakTransform_of_notMem (Z I : X.IdealSheafData) {x' : Z.blowUp}
    (hx' : x' ∉ Z.exceptionalDivisor.support) :
    (I.weakTransform Z).stalkIdeal x' = (I.comap Z.blowUpπ).stalkIdeal x' := by
  have htop : Z.exceptionalDivisor.stalkIdeal x' = ⊤ := by
    by_contra h
    exact hx' ((mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mpr (IsLocalRing.le_maximalIdeal h))
  refine le_antisymm ?_
    (stalkIdeal_mono
      (comap_le_controlledTransformAlong Z.blowUpπ Z.exceptionalDivisor I _) x')
  refine (stalkIdeal_colon_le _ _ x').trans ?_
  rw [stalkIdeal_pow, htop, Ideal.top_pow]
  intro r hr
  have := Submodule.mem_colon.mp hr 1 (Submodule.mem_top)
  simpa using this

/-- Off the exceptional divisor the order of the weak transform is the order of the ideal at the
image point (`π` is a local isomorphism there, and the order is a stalk invariant). -/
theorem ord_weakTransform_of_notMem (Z I : X.IdealSheafData) {x' : Z.blowUp}
    (hx' : x' ∉ Z.exceptionalDivisor.support) :
    (I.weakTransform Z).ord x' = I.ord (Z.blowUpπ x') := by
  rw [ord_eq_ord_stalkIdeal, stalkIdeal_weakTransform_of_notMem Z I hx', stalkIdeal_comap,
    ord_eq_ord_stalkIdeal]
  have : IsIso (Z.blowUpπ.stalkMap x') := isIso_stalkMap_π_of_notMem_support Z hx'
  exact ord_map_ringEquiv
    (asIso (Z.blowUpπ.stalkMap x')).commRingCatIsoToRingEquiv _

/-- If the center `Z` lies in `cosupp(I, m)`, a point of `cosupp(π_*^{-1} I, m)` on the blow-up
maps to a point of `cosupp(I, m)`. -/
theorem le_ord_of_le_ord_weakTransform (Z I : X.IdealSheafData) {m : ℕ}
    (hZ : ∀ x ∈ Z.support, (m : ℕ∞) ≤ I.ord x) (x' : Z.blowUp)
    (h : (m : ℕ∞) ≤ (I.weakTransform Z).ord x') : (m : ℕ∞) ≤ I.ord (Z.blowUpπ x') := by
  by_cases hx' : x' ∈ Z.exceptionalDivisor.support
  · exact hZ _ ((mem_support_comap_iff_apply Z Z.blowUpπ x').mp hx')
  · rwa [ord_weakTransform_of_notMem Z I hx'] at h

/-- A divisor disjoint from `cosupp(I, m)` has birational transform disjoint from
`cosupp(π_*^{-1} I, m)` when the center lies in `cosupp(I, m)`. -/
theorem disjoint_cosupp_strictTransform_of_disjoint [IsLocallyNoetherian X]
    (Z I D : X.IdealSheafData) {m : ℕ} (hZ : ∀ x ∈ Z.support, (m : ℕ∞) ≤ I.ord x)
    (hD : Disjoint {x | (m : ℕ∞) ≤ I.ord x} (D.support : Set X)) :
    Disjoint {x' | (m : ℕ∞) ≤ (I.weakTransform Z).ord x'}
      ((D.strictTransform Z).support : Set Z.blowUp) := by
  rw [Set.disjoint_left]
  intro x' hx' hxD
  have h1 : (m : ℕ∞) ≤ I.ord (Z.blowUpπ x') := le_ord_of_le_ord_weakTransform Z I hZ x'
      hx'
  have hsub : ((D.strictTransform Z).support : Set Z.blowUp) ⊆
      Z.blowUpπ ⁻¹' (D.support : Set X) := by
    rw [coe_support_strictTransform]
    exact (closure_mono Set.sdiff_subset).trans
      (D.support.isClosed.preimage Z.blowUpπ.continuous).closure_subset
  exact Set.disjoint_left.mp hD h1 (hsub hxD)

variable {k : Type u} [Field k] [CharZero k] {m : ℕ}

/-- Along a smooth blow-up sequence of order `m`, whose centers lie in the cosupport (condition
(4) of [Kol07, Definition 66]), a divisor disjoint from `cosupp(I, m)` keeps its birational
transform disjoint from the cosupport of the final ideal; this is what keeps the cleared members
cleared in [Kol07, 104, Step 2.1]. -/
theorem disjoint_cosupp_strictTransformSeq_last_of_disjoint (n : ℕ) : ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X)
    {J : X.IdealSheafData} {E : DivisorFamily X}, S.IsOrderSeq f J E m → ∀ (D : X.IdealSheafData),
    Disjoint {x | (m : ℕ∞) ≤ J.ord x} (D.support : Set X) →
    Disjoint {x | (m : ℕ∞) ≤ (S.weakTransformSeq J (Fin.last _)).ord x}
      ((S.strictTransformSeq D (Fin.last _)).support : Set _)
  | _, _, _, nil _, _, _, _, _, hD => hD
  | X, f, _, cons _ D₀ rest, J, E, h, D, hD => by
    obtain ⟨hhead, ht⟩ := (isOrderSeq_cons_iff f J E m D₀ rest).1 h
    have : Smooth (D₀.subschemeι ≫ f) := hhead.1
    have : SmoothOfRelativeDimension n (D₀.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D₀
    have : Smooth f := SmoothOfRelativeDimension.smooth n f
    have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    have hZ : ∀ x ∈ D₀.support, (m : ℕ∞) ≤ J.ord x := fun x hx =>
      IsOrderSeq.le_ord_of_mem_center f n h ⟨0, Nat.succ_pos _⟩ hx
    exact disjoint_cosupp_strictTransformSeq_last_of_disjoint n (D₀.blowUpπ ≫ f) rest ht
      (D.strictTransform D₀) (disjoint_cosupp_strictTransform_of_disjoint D₀ J D hZ hD)

end Hironaka.Sequence
