/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The centers of an order-`m` blow-up sequence lie over the cosupport

For a smooth blow-up sequence `S = (X_r → ⋯ → X_0 = X)` of order `m` starting with `(X, I)`
([Kol07, Definition 66], `IsOrderSeq`), `cosupp(I_{i+1}, m) ⊆ π_i^{-1}(cosupp(I_i, m))`, hence
`Π_i(Z_i) ⊆ cosupp(I, m)` for every center `Z_i`. Consequently, for a flat `ψ : U ⟶ X` whose image
contains `cosupp(I, m)`, every center lies in the image of the corresponding stage lift of `ψ`
(`CentersInRange`), no center of `ψ^*S` is empty when none of `S` is, and `ψ^*S` determines `S`
(`pullback_injective`). This is what allows étale equivalence [Kol07, Definition 96] and the
equality of étale equivalent blow-up sequences [Kol07, Theorem 97] to be used with étale maps
whose image contains the cosupport in place of étale surjections: the lifts of `ψ` still cover the
centers, so no empty
blow-up has to be deleted.

**The one-blow-up step** (`le_ord_blowUpπ_of_le_ord_weakTransform`). Let `π : B_Z X → X` be the
blow-up of a center `Z` along which `ord I = m` (condition (4) of Definition 66 at one stage), and
let `y ∈ B_Z X` with `ord_y I' ≥ m` for the weak transform `I' = π_*^{-1} I`. If `π(y) ∈ Z` then
`ord_{π(y)} I ≥ m` because `ord_Z I = m` means `ord = m` at the generic points of `Z`, and the
order is upper semicontinuous (`leOrdAlong_iff_forall_mem`, on the smooth `X` in characteristic
zero). If `π(y) ∉ Z` then `π` is an isomorphism near `y` and `I'` contains `π^* I`, so
`ord_y I' ≤ ord_{π(y)} I` (`ord_controlledTransform_le_of_notMem`; this is the part of
[Kol07, Lemma 61] concerning points off the exceptional divisor). The stage step and
`Π_i(Z_i) ⊆ cosupp(I, m)` follow by induction along the sequence, the stages being smooth of the
same relative dimension (`smoothOfRelativeDimension_blowUpπ_comp_of_smooth`).
-/

public section

namespace AlgebraicGeometry

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- One blow-up: if `ord_Z I = m` along the center `Z` and `y ∈ B_Z X` has `ord_y π_*^{-1} I ≥ m`,
then `ord_{π(y)} I ≥ m`; over the center by upper semicontinuity of the order, off it because `π`
is an isomorphism there and `π_*^{-1} I ⊇ π^* I` (`ord_controlledTransform_le_of_notMem`; compare
[Kol07, Lemma 61]). -/
theorem le_ord_blowUpπ_of_le_ord_weakTransform (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {D I : X.IdealSheafData} {m : ℕ}
    (hord : I.OrdAlongEq D.support (m : ℕ∞)) (y : D.blowUp)
    (hy : (m : ℕ∞) ≤ (I.weakTransform D).ord y) : (m : ℕ∞) ≤ I.ord
        (D.blowUpπ y) := by
  by_cases hz : D.blowUpπ y ∈ D.support
  · exact (leOrdAlong_iff_forall_mem I f n D.support (m : ℕ∞)).mp
      (fun η hη => (hord η hη).ge) _ hz
  · exact hy.trans (ord_controlledTransform_le_of_notMem D I _ y hz)

/-- The stage step: for a smooth blow-up sequence `S` of order `m` starting with `(X, I)`,
`cosupp(I_{i+1}, m) ⊆ π_i^{-1}(cosupp(I_i, m))`; induction along the sequence with
`le_ord_blowUpπ_of_le_ord_weakTransform` at the first step (on the `cons` shape the first step is
`D.blowUpπ` once the tail's constructor is known, `step_cons_nil_zero`, `step_cons_cons_zero`). -/
theorem le_ord_step_of_le_ord_weakTransformSeq (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) (i : Fin S.length)
    {y : S.stage i.succ} (hy : (m : ℕ∞) ≤ (S.weakTransformSeq I i.succ).ord y) :
    (m : ℕ∞) ≤ (S.weakTransformSeq I i.castSucc).ord (S.step i y) := by
  induction S with
  | nil _ => exact i.elim0
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, hrest⟩ :=
      (isOrderSeq_cons_iff (f := f) (I := I) (E := E) (m := m) D rest).1 hS
    rcases i with ⟨_ | j, hi⟩
    · cases rest with
      | nil _ =>
        rw [step_cons_nil_zero]
        exact le_ord_blowUpπ_of_le_ord_weakTransform f n hord y hy
      | cons _ D' rest' =>
        rw [step_cons_cons_zero]
        exact le_ord_blowUpπ_of_le_ord_weakTransform f n hord y hy
    · have : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
        have := hD
        exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      exact ih (D.blowUpπ ≫ f) hrest ⟨j, Nat.lt_of_succ_lt_succ hi⟩ hy

/-- Every center of a smooth blow-up sequence of order `m` starting with `(X, I)` lies over the
cosupport, `Π_i(Z_i) ⊆ cosupp(I, m)`: by induction along the sequence, a point of `Z_i` has
`ord I_i ≥ m` (condition (4) of [Kol07, Definition 66] with upper semicontinuity), and
`le_ord_blowUpπ_of_le_ord_weakTransform` carries `ord ≥ m` down each blow-up. -/
theorem le_ord_stageMap_of_mem_center (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) (i : Fin S.length)
    {z : S.stage i.castSucc} (hz : z ∈ (S.center i).support) :
    (m : ℕ∞) ≤ I.ord (S.stageMap i.castSucc z) := by
  induction S with
  | nil _ => exact i.elim0
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, hrest⟩ :=
      (isOrderSeq_cons_iff (f := f) (I := I) (E := E) (m := m) D rest).1 hS
    rcases i with ⟨_ | j, hi⟩
    · exact (leOrdAlong_iff_forall_mem I f n D.support (m : ℕ∞)).mp
        (fun η hη => (hord η hη).ge) z hz
    · have : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
        have := hD
        exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have h1 := ih (D.blowUpπ ≫ f) hrest ⟨j, Nat.lt_of_succ_lt_succ hi⟩ hz
      exact le_ord_blowUpπ_of_le_ord_weakTransform f n hord _ h1

/-- For a flat `ψ : U ⟶ X` whose image contains `cosupp(I, m)`, the centers of a smooth blow-up
sequence of order `m` starting with `(X, I)` lie in the images of the stage lifts of `ψ`
(`CentersInRange`): `Z_i ⊆ Π_i^{-1}(cosupp(I, m)) ⊆ Π_i^{-1}(im ψ) = im ψ_i`
(`range_pullbackStageHom`). -/
theorem centersInRange_of_cosupp_le_range (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) {U : Scheme.{u}} (ψ : U ⟶ X)
    [Flat ψ] (h : {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range ψ.base) : S.CentersInRange ψ := by
  intro i
  rw [range_pullbackStageHom]
  intro z hz
  exact h (le_ord_stageMap_of_mem_center f n hS i hz)

/-- If no center of `S` is empty and every center lies in the image of the corresponding stage
lift of `ψ`, then no center of `ψ^*S` is empty: by induction along the sequence; at each stage the
pulled-back center is `ψ_i^{-1}(Z_i)`, whose support is the preimage of the nonempty
`|Z_i| ⊆ im ψ_i` (`support_comap`, `support_eq_bot_iff`). -/
theorem noEmptyCenters_pullback_of_centersInRange {S : BlowUpSequence X} {U : Scheme.{u}}
    (ψ : U ⟶ X) (hne : S.NoEmptyCenters) (hr : S.CentersInRange ψ) :
    (S.pullback ψ).NoEmptyCenters := by
  induction S generalizing U with
  | nil _ => exact fun i => i.elim0
  | cons Y D rest ih =>
    rw [pullback_cons, noEmptyCenters_cons_iff]
    obtain ⟨hD, hrest⟩ := (noEmptyCenters_cons_iff D rest).1 hne
    refine ⟨fun htop => hD ?_,
      ih (Scheme.Hom.blowUpMap ψ D) hrest fun i => hr ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩
    have h0 : (D.support : Set Y) ⊆ Set.range ψ := hr ⟨0, Nat.succ_pos _⟩
    rw [← Scheme.IdealSheafData.support_eq_bot_iff] at htop ⊢
    rw [Scheme.IdealSheafData.support_comap] at htop
    ext z
    refine ⟨fun hz => ?_, fun hz => hz.elim⟩
    obtain ⟨u, rfl⟩ := h0 hz
    have hu : u ∈ (D.support.preimage ψ.continuous : Set U) := hz
    rw [htop] at hu
    exact hu.elim

/-- `ψ^*B` determines `B` when the image of `ψ` contains the cosupport (a closed subscheme
contained in the image of an étale map is determined by its preimage): two smooth blow-up
sequences of order `m` starting with `(X, I)` with equal pullbacks along a flat `ψ` whose image
contains `cosupp(I, m)` are equal (`pullback_injective` with `centersInRange_of_cosupp_le_range`;
compare the uniqueness for surjective `h` in [Kol07, 30.1]). -/
theorem eq_of_pullback_eq_of_cosupp_le_range (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {S S' : BlowUpSequence X} {I : X.IdealSheafData}
    {E E' : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m) (hS' : S'.IsOrderSeq f I E' m)
    {U : Scheme.{u}} (ψ : U ⟶ X) [Flat ψ] (h : {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range ψ.base)
    (heq : S.pullback ψ = S'.pullback ψ) : S = S' :=
  pullback_injective ψ (centersInRange_of_cosupp_le_range f n hS ψ h)
    (centersInRange_of_cosupp_le_range f n hS' ψ h) heq

end AlgebraicGeometry
