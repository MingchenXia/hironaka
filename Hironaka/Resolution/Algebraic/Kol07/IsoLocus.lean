/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.TransformOrder
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isomorphism locus of a blow-up sequence

In the proof of Theorem 107, Kollár runs the order reduction of the monomial part `M(I)` on
`X ∖ cosupp N(I)`, where `I = M(I)` [Kol07, 111, Step 3]. This library runs it on `X` itself for
`(M(I), m)` and reads the result for `(I, m)`. Over `cosupp N(I)` nothing happens: every center
lies in `cosupp(M_i, m)`, which misses the preimage of `cosupp N(I)` because there
`ord M_i = ord M(I) ≤ ord I < m` after the second step; and a blow-up sequence whose centers avoid
the preimages of a set `C` is an isomorphism over `C`, with the marked transform there the
pullback of the starting ideal.

This module proves the two halves of that statement for any scheme (identities of stalks off the
centers; no field, no smoothness) and the propagation of the disjointness along a smooth sequence:

* `stalkIdeal_markedTransform_congr`, `stalkIdeal_markedTransformSeq_congr`: the stalk of a
  marked transform at `x` depends only on the stalk of the starting ideal at the image of `x`
  (the marked transform is `(π^* I) : (π^* Z)^m` with `π^* Z` invertible, and colons by
  invertible ideals are read stalkwise); so ideals with equal stalks over an open have equal
  marked transforms over its preimage, Kollár's "`I = M(I)` off `cosupp N(I)`" transported along
  the sequence;
* `ord_markedTransform_of_notMem`: off the exceptional divisor the order of the marked transform
  is the order at the image (the marked analogue of `ord_weakTransform_of_notMem`);
* `isIso_over_of_centers_disjoint`, `ord_markedTransformSeq_eq_of_disjoint`: along a sequence
  whose centers avoid the preimages of `C`, at every point over `C` the stage map is an
  isomorphism of stalks (a blow-up is an isomorphism off its center,
  `isIso_stalkMap_π_of_notMem_support`, composed along the stages) and the marked transform's
  stalk is the stalk of the pulled-back ideal (the exceptional stalk is the unit ideal there,
  `stalkIdeal_markedTransform_of_notMem`); hence the order there is the order at the image;
* `center_disjoint_of_isOrderGeSeq_of_lt`: a smooth blow-up sequence of order `≥ m` for
  `(M, m, E)` on a smooth scheme over a field of characteristic zero has every center disjoint
  from the preimage of any set on which `ord M < m`. By induction along the sequence: the center
  lies in `cosupp(M_i, m)` (condition (4′) of [Kol07, Definition 66] at the generic points, at
  every point by upper semicontinuity), and over the set the order is unchanged (the earlier
  blow-ups are isomorphisms there).

The restriction-level form of the isomorphism statement, `IsIso (S.composite ∣_ U)`, is in
`Hironaka/Resolution/Algebraic/Kol07/IsoRestrict.lean`. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
  Scheme.IdealSheafData Scheme BlowUpSequence IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

section AnyScheme

variable {X : Scheme.{u}}

/-- The stalk of a marked transform `(π^* I) : (π^* Z)^m` [Kol07, Definition 60] at `y` is
determined by the stalk of the ideal at `π y`: two ideals with the same stalk at `π y` have marked
transforms with the same stalk at `y` (the colon by the invertible `(π^* Z)^m` is read
stalkwise). -/
theorem stalkIdeal_markedTransform_congr (D : X.IdealSheafData) {I J : X.IdealSheafData} (m : ℕ)
    {y : D.blowUp} (h : I.stalkIdeal (D.blowUpπ y) = J.stalkIdeal
        (D.blowUpπ y)) :
    (I.markedTransform D m).stalkIdeal y = (J.markedTransform D m).stalkIdeal y := by
  change ((I.comap D.blowUpπ).colon (D.comap D.blowUpπ ^ m)).stalkIdeal y
      =
    ((J.comap D.blowUpπ).colon (D.comap D.blowUpπ ^ m)).stalkIdeal y
  rw [stalkIdeal_colon_of_isInvertible _ (isInvertible_pow (blowUp.isInvertible_comap_π D) m),
    stalkIdeal_colon_of_isInvertible _ (isInvertible_pow (blowUp.isInvertible_comap_π D) m),
    stalkIdeal_comap, stalkIdeal_comap, h]

/-- The stalk of the marked transform `(I_i, m)` at `x` is determined by the stalk of `I` at
`Π_i x`: two starting ideals with the same stalk at `Π_i x` have marked transforms with the same
stalk at `x` (Kollár's "`I = M(I)`" off `cosupp N(I)`, [Kol07, 111, Step 2], transported along a
sequence). -/
theorem stalkIdeal_markedTransformSeq_congr (S : BlowUpSequence X) {I J : X.IdealSheafData}
    (m : ℕ) (i : Fin (S.length + 1)) (x : S.stage i)
    (h : I.stalkIdeal (S.stageMap i x) = J.stalkIdeal (S.stageMap i x)) :
    (S.markedTransformSeq I m i).stalkIdeal x = (S.markedTransformSeq J m i).stalkIdeal x := by
  induction S with
  | nil Y => exact h
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hj⟩
    · exact h
    · exact ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x (stalkIdeal_markedTransform_congr D m h)

/-- Off the exceptional divisor the order of the marked transform is the order of the ideal at the
image point: the blow-up is a local isomorphism there and the order is read in isomorphic local
rings (`ord_map_ringEquiv`). The marked analogue of `ord_weakTransform_of_notMem`. -/
theorem ord_markedTransform_of_notMem (Z K : X.IdealSheafData) (c : ℕ) {q : Z.blowUp}
    (hq : q ∉ (Z.comap Z.blowUpπ).support) :
    (K.markedTransform Z c).ord q = K.ord (Z.blowUpπ q) := by
  rw [ord_eq_ord_stalkIdeal, stalkIdeal_markedTransform_of_notMem Z K c hq, ord_eq_ord_stalkIdeal]
  have : IsIso (Z.blowUpπ.stalkMap q) := isIso_stalkMap_π_of_notMem_support Z hq
  exact ord_map_ringEquiv
    (asIso (Z.blowUpπ.stalkMap q)).commRingCatIsoToRingEquiv _

/-- Along a blow-up sequence whose centers avoid the preimages of a set `C`, **the sequence is an
isomorphism over `C` and the marked transform there is the pullback**: at every point over `C`
the stage map is an isomorphism of stalks (a blow-up is an isomorphism off its center,
`isIso_stalkMap_π_of_notMem_support`, composed along the stages) and the marked transform's stalk
is the stalk of the pulled-back ideal (the exceptional stalk is the unit ideal there,
`stalkIdeal_markedTransform_of_notMem`). Not in the sources; holds on any scheme. -/
theorem isIso_over_of_centers_disjoint (S : BlowUpSequence X) {I : X.IdealSheafData} {m : ℕ}
    {C : Set X}
    (hZ : ∀ i : Fin S.length,
      Disjoint (((S.center i).support : Set (S.stage i.castSucc))) (S.stageMap i.castSucc ⁻¹' C))
    (i : Fin (S.length + 1)) (x : S.stage i) (hx : S.stageMap i x ∈ C) :
    IsIso ((S.stageMap i).stalkMap x) ∧
      (S.markedTransformSeq I m i).stalkIdeal x = (I.comap (S.stageMap i)).stalkIdeal x := by
  induction S with
  | nil Y =>
    revert x hx
    change ∀ (x : Y), (𝟙 Y : Y ⟶ Y) x ∈ C → IsIso ((𝟙 Y : Y ⟶ Y).stalkMap x) ∧
      I.stalkIdeal x = (I.comap (𝟙 Y)).stalkIdeal x
    intro x _
    exact ⟨isIso_stalkMap_id Y x, (stalkIdeal_comap_id I x).symm⟩
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hj⟩
    · revert x hx
      change ∀ (x : Y), (𝟙 Y : Y ⟶ Y) x ∈ C → IsIso ((𝟙 Y : Y ⟶ Y).stalkMap x) ∧
        I.stalkIdeal x = (I.comap (𝟙 Y)).stalkIdeal x
      intro x _
      exact ⟨isIso_stalkMap_id Y x, (stalkIdeal_comap_id I x).symm⟩
    · revert x hx
      change ∀ (x : rest.stage ⟨j, Nat.lt_of_succ_lt_succ hj⟩),
        (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) x ∈ C →
        IsIso ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ).stalkMap x) ∧
          (rest.markedTransformSeq (I.markedTransform D m) m
            ⟨j, Nat.lt_of_succ_lt_succ hj⟩).stalkIdeal x =
          (I.comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ)).stalkIdeal x
      intro x hx
      have hZ' : ∀ i' : Fin rest.length,
          Disjoint (((rest.center i').support : Set (rest.stage i'.castSucc)))
            (rest.stageMap i'.castSucc ⁻¹' (D.blowUpπ ⁻¹' C)) := fun i' => by
        rw [Set.disjoint_left]
        intro y hy hy'
        exact Set.disjoint_left.1 (hZ ⟨i'.1 + 1, Nat.succ_lt_succ i'.2⟩) hy hy'
      have hxC : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x ∈ D.blowUpπ ⁻¹' C := hx
      obtain ⟨h1, h2⟩ :=
        ih (I := I.markedTransform D m) hZ' ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x hxC
      have hy : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x ∉
          (D.comap D.blowUpπ).support := by
        rw [mem_support_comap_iff_apply]
        intro hmem
        exact Set.disjoint_left.1 (hZ ⟨0, Nat.succ_pos _⟩) hmem hxC
      have hiso : IsIso (D.blowUpπ.stalkMap (rest.stageMap ⟨j,
          Nat.lt_of_succ_lt_succ hj⟩ x)) :=
        isIso_stalkMap_π_of_notMem_support D hy
      have e : ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ).stalkMap
          x).hom =
          ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩).stalkMap x).hom.comp
            (D.blowUpπ.stalkMap (rest.stageMap ⟨j,
                Nat.lt_of_succ_lt_succ hj⟩ x)).hom := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
      refine ⟨?_, ?_⟩
      · rw [Scheme.Hom.stalkMap_comp]
        exact IsIso.comp_isIso' hiso h1
      · rw [h2, stalkIdeal_comap, stalkIdeal_comap, stalkIdeal_markedTransform_of_notMem D I m hy,
          Ideal.map_map, e]
        rfl

/-- The order form of `isIso_over_of_centers_disjoint`: at a point over `C` the marked transform
has the order of the ideal at the image (the order is read in isomorphic local rings,
`ord_map_ringEquiv`). Holds on any scheme. -/
theorem ord_markedTransformSeq_eq_of_disjoint (S : BlowUpSequence X) {I : X.IdealSheafData}
    {m : ℕ} {C : Set X}
    (hZ : ∀ i : Fin S.length,
      Disjoint (((S.center i).support : Set (S.stage i.castSucc))) (S.stageMap i.castSucc ⁻¹' C))
    (i : Fin (S.length + 1)) (x : S.stage i) (hx : S.stageMap i x ∈ C) :
    (S.markedTransformSeq I m i).ord x = I.ord (S.stageMap i x) := by
  obtain ⟨h1, h2⟩ := isIso_over_of_centers_disjoint S (I := I) (m := m) hZ i x hx
  rw [ord_eq_ord_stalkIdeal, h2, stalkIdeal_comap, ord_eq_ord_stalkIdeal]
  exact ord_map_ringEquiv
    (asIso ((S.stageMap i).stalkMap x)).commRingCatIsoToRingEquiv _

end AnyScheme

section Smooth

variable {k : Type u} [Field k] [CharZero k]

/-- Along a smooth blow-up sequence of order `≥ m` for `(M, m, E)`, every center avoids the
preimage of a set `C` on which `ord M < m`. By induction along the sequence: the center `Z_i` lies
in `cosupp(M_i, m)` (at its generic points by condition (4′) of [Kol07, Definition 66], at every
point by upper semicontinuity), while over `C` the order of `M_i` is the order of `M` at the image
(`ord_markedTransform_of_notMem`, the earlier blow-ups being isomorphisms there), hence `< m`. -/
theorem center_disjoint_of_isOrderGeSeq_of_lt : ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) {M : X.IdealSheafData} {m : ℕ}
    {E : DivisorFamily X}, S.IsOrderGeSeq f M m E → ∀ {C : Set X}, (∀ x ∈ C, M.ord x < m) →
    ∀ i : Fin S.length,
      Disjoint (((S.center i).support : Set (S.stage i.castSucc))) (S.stageMap i.castSucc ⁻¹' C)
  | _, _, _, _, nil _, _, _, _, _, _, _, i => i.elim0
  | X, f, n, _, cons _ D rest, M, m, E, hS, C, hC, i => by
    obtain ⟨hhead, ht⟩ := (isOrderGeSeq_cons_iff (f := f) (I := M) (m := m) (E := E) D rest).1 hS
    have : Smooth (D.subschemeι ≫ f) := hhead.1
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hD : Disjoint (D.support : Set X) C := by
      rw [Set.disjoint_left]
      intro x hx hxC
      exact absurd ((leOrdAlong_iff_forall_mem (I := M) (f := f) (n := n) D.support (m : ℕ∞)).1
        hhead.2.2 x hx) (not_le.2 (hC x hxC))
    rcases i with ⟨_ | j, hj⟩
    · exact hD
    · have hC' : ∀ y ∈ D.blowUpπ ⁻¹' C, (M.markedTransform D m).ord y < m := fun y hy =>
        by
        have hy' : y ∉ (D.comap D.blowUpπ).support := by
          rw [mem_support_comap_iff_apply]
          exact fun hmem => Set.disjoint_left.1 hD hmem hy
        rw [ord_markedTransform_of_notMem D M m hy']
        exact hC _ hy
      exact center_disjoint_of_isOrderGeSeq_of_lt (D.blowUpπ ≫ f) n rest ht hC'
        ⟨j, Nat.lt_of_succ_lt_succ hj⟩

end Smooth

end Hironaka.Sequence
