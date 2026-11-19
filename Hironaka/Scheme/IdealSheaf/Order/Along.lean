/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs

/-!
# The order along a closed subset and the maximal order

[Kol07, Definition 47]: for an irreducible subvariety `Z ⊂ X` the order of `I` along `Z` is
`ord_Z I := ord_η I`, `η` the generic point of `Z`; for `Z` not irreducible, the notation
`ord_Z I = m` (resp. `ord_Z I ≥ m`) means that the order of `I` at every generic point of `Z` is `m`
(resp. `≥ m`); and the maximal order of `I` along `Z` is `max-ord_Z I := max {ord_z I : z ∈ Z}`.

* `IrreducibleCloseds.genericPoint Z` is the generic point of an irreducible closed subset of a
  quasi-sober space (Mathlib's `IsIrreducible.genericPoint`); schemes are quasi-sober and `T₀`, so
  it is the unique point with `closure {η} = Z`.
* `Closeds.genericPoints Z` are the generic points of a closed subset `Z`, the generic points of
  its irreducible components, taken as the points of `Z` maximal for specialization; the
  characterization `mem_genericPoints_iff` identifies them with the points `η` whose closure
  `closure {η}` is a maximal irreducible subset of `Z` (an irreducible component of `Z`).
* `ordAlong I Z := ord I (generic point of Z)` for `Z` irreducible closed; `OrdAlongEq I Z m` and
  `LeOrdAlong I Z m` are Kollár's conventions `ord_Z I = m`, `ord_Z I ≥ m` for a closed `Z` that
  need not be irreducible (the condition at every generic point), consistent with `ordAlong` on
  irreducible closed sets (`ordAlongEq_iff`, `leOrdAlong_iff`);
  `maxOrdAlong I Z := ⨆ z ∈ Z, ord I z` is `max-ord_Z I` (attained and finite under Noetherian
  hypotheses, `Hironaka/Scheme/IdealSheaf/Order/Constructible.lean`). [Hau03, Appendix A] defines
  `ord_Z` through the localization `𝒪_{W,Z}` and notes `ord_Z = min_{a ∈ Z} ord_a I`; that minimum
  is `Hironaka/Scheme/IdealSheaf/Order/Specialization.lean`.

The two lemmas at the end, on membership in a finite union of closed sets and on affine
neighbourhoods missing it, are general tools used by the monomial part of the argument
(`Hironaka/Resolution/Algebraic/Monomial/Geometric`).

Used for the cosupport of marked ideals and the centres of blow-ups
(`Hironaka/Scheme/Snc/Dictionary.lean`, `HironakaExamples/Sequence/CosuppForcing.lean`,
`Hironaka/Resolution/Algebraic/Balanced/GoingUpChain.lean`,
`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`, `Hironaka.BD.Zminus1`).
-/

@[expose] public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **The generic points of a closed subset** `Z` ("every generic point of `Z`",
[Kol07, Definition 47]): the points of `Z` that are maximal for specialization, that is, the
generic points of the irreducible components of `Z` (`Closeds.mem_genericPoints_iff`). -/
def Closeds.genericPoints (Z : Closeds X) : Set X :=
  {η | η ∈ Z ∧ ∀ ⦃η'⦄, η' ∈ Z → η' ⤳ η → η' = η}

/-- The empty closed set has no generic points. -/
theorem Closeds.genericPoints_bot : (⊥ : Closeds X).genericPoints = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun η hη => ?_
  have h : η ∈ ((⊥ : Closeds X) : Set X) := hη.1
  rw [Closeds.coe_bot] at h
  exact Set.notMem_empty η h

/-- **The generic point of an irreducible closed subset** of a quasi-sober space (Mathlib's
`IsIrreducible.genericPoint`). -/
noncomputable def IrreducibleCloseds.genericPoint [QuasiSober X] (Z : IrreducibleCloseds X) : X :=
  Z.isIrreducible.genericPoint

/-- The generic point of `Z` is a generic point of `Z`: `closure {η} = Z`. -/
theorem IrreducibleCloseds.isGenericPoint_genericPoint [QuasiSober X] (Z : IrreducibleCloseds X) :
    IsGenericPoint Z.genericPoint (Z : Set X) :=
  Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed

/-- The generic points of a closed `Z` in a sober `T₀` space are the points `η ∈ Z`
whose closure is a maximal irreducible subset of `Z` — an irreducible component of `Z`.  (A
specialization-maximal `η` has `closure {η}` maximal: an irreducible `T ⊆ Z` containing `η` has a
generic point `η'` of its closure, which specializes to `η`, so `η' = η` and `T ⊆ closure {η}`;
conversely maximality of `closure {η}` forces any `η' ∈ Z` with `η' ⤳ η` to satisfy `η ⤳ η'` as
well, hence `η' = η`.) -/
theorem Closeds.mem_genericPoints_iff [T0Space X] [QuasiSober X] (Z : Closeds X) (η : X) :
    η ∈ Z.genericPoints ↔ Maximal (fun T : Set X => T ⊆ Z ∧ IsIrreducible T) (closure {η}) := by
  constructor
  · rintro ⟨hηZ, hmax⟩
    refine ⟨⟨Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηZ),
      isIrreducible_singleton.closure⟩, ?_⟩
    rintro T ⟨hTZ, hT⟩ hle
    have hη' : IsGenericPoint hT.genericPoint (closure T) := hT.isGenericPoint_genericPoint_closure
    have hη'Z : hT.genericPoint ∈ Z :=
      Z.isClosed.closure_subset_iff.mpr hTZ hη'.mem
    have hηT : η ∈ closure T := subset_closure (hle (subset_closure rfl))
    have heq : hT.genericPoint = η := hmax hη'Z (hη'.specializes hηT)
    calc T ⊆ closure T := subset_closure
      _ = closure {hT.genericPoint} := hη'.def.symm
      _ = closure {η} := by rw [heq]
  · rintro ⟨⟨hsub, -⟩, hmax⟩
    refine ⟨hsub (subset_closure rfl), fun η' hη'Z hspec => ?_⟩
    have h1 : closure ({η} : Set X) ⊆ closure {η'} := specializes_iff_closure_subset.mp hspec
    have h2 : closure ({η'} : Set X) ⊆ closure {η} :=
      hmax ⟨Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη'Z),
        isIrreducible_singleton.closure⟩ h1
    exact (hspec.antisymm (specializes_iff_closure_subset.mpr h2)).eq

/-- The only generic point of an irreducible closed `Z` is its generic point. -/
theorem IrreducibleCloseds.genericPoints_eq [T0Space X] [QuasiSober X] (Z : IrreducibleCloseds X) :
    (⟨Z, Z.isClosed⟩ : Closeds X).genericPoints = {Z.genericPoint} := by
  ext η
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hηZ, hmax⟩
    exact (hmax Z.isGenericPoint_genericPoint.mem
      (Z.isGenericPoint_genericPoint.specializes hηZ)).symm
  · rintro rfl
    exact ⟨Z.isGenericPoint_genericPoint.mem, fun η' hη' hspec =>
      (hspec.antisymm (Z.isGenericPoint_genericPoint.specializes hη')).eq⟩

end TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TopologicalSpace

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- [Kol07, Definition 47]: **the order of `I` along an irreducible closed subset `Z`**,
`ord_Z I := ord_η I` for `η` the generic point of `Z`. -/
noncomputable def ordAlong (Z : IrreducibleCloseds X) : ℕ∞ :=
  I.ord Z.genericPoint

/-- Kollár's notation `ord_Z I = m` for a closed `Z` that need not be irreducible
([Kol07, Definition 47]): the order of `I` at every generic point of `Z` is `m`. -/
def OrdAlongEq (Z : Closeds X) (m : ℕ∞) : Prop :=
  ∀ η ∈ Z.genericPoints, I.ord η = m

/-- Kollár's notation `ord_Z I ≥ m` for a closed `Z` that need not be irreducible
([Kol07, Definition 47]): the order of `I` at every generic point of `Z` is at least `m`. -/
def LeOrdAlong (Z : Closeds X) (m : ℕ∞) : Prop :=
  ∀ η ∈ Z.genericPoints, m ≤ I.ord η

/-- [Kol07, Definition 47]: **the maximal order of `I` along `Z`**,
`max-ord_Z I := max {ord_z I : z ∈ Z}`, as a supremum in `ℕ∞` (attained and finite under the
hypotheses of `Hironaka/Scheme/IdealSheaf/Order/Constructible.lean`). -/
noncomputable def maxOrdAlong (Z : Set X) : ℕ∞ :=
  ⨆ z ∈ Z, I.ord z

/-- `ord_Z I = ord_η I` for any generic point `η` of the irreducible closed `Z` (there is exactly
one, schemes being `T₀`). -/
theorem ordAlong_eq_of_isGenericPoint {Z : IrreducibleCloseds X} {η : X}
    (hη : IsGenericPoint η (Z : Set X)) : I.ordAlong Z = I.ord η := by
  rw [ordAlong, Z.isGenericPoint_genericPoint.eq hη]

/-- For an irreducible closed `Z` the convention `ord_Z I = m` is `ordAlong I Z = m`. -/
theorem ordAlongEq_iff (Z : IrreducibleCloseds X) (m : ℕ∞) :
    I.OrdAlongEq ⟨Z, Z.isClosed⟩ m ↔ I.ordAlong Z = m := by
  rw [OrdAlongEq, IrreducibleCloseds.genericPoints_eq]
  simp only [Set.mem_singleton_iff, forall_eq]
  rfl

/-- For an irreducible closed `Z` the convention `ord_Z I ≥ m` is `m ≤ ordAlong I Z`. -/
theorem leOrdAlong_iff (Z : IrreducibleCloseds X) (m : ℕ∞) :
    I.LeOrdAlong ⟨Z, Z.isClosed⟩ m ↔ m ≤ I.ordAlong Z := by
  rw [LeOrdAlong, IrreducibleCloseds.genericPoints_eq]
  simp only [Set.mem_singleton_iff, forall_eq]
  rfl

/-- `ord_z I ≤ max-ord_Z I` for `z ∈ Z`. -/
theorem le_maxOrdAlong {Z : Set X} {z : X} (hz : z ∈ Z) : I.ord z ≤ I.maxOrdAlong Z :=
  le_iSup₂ (f := fun z (_ : z ∈ Z) => I.ord z) z hz

/-- `max-ord_Z I ≤ m` iff `ord_z I ≤ m` for every `z ∈ Z`. -/
theorem maxOrdAlong_le_iff {Z : Set X} {m : ℕ∞} : I.maxOrdAlong Z ≤ m ↔ ∀ z ∈ Z, I.ord z ≤ m :=
  iSup₂_le_iff

/-- Membership in a finite supremum of closed sets (a general tool, in the namespace of the
monomial part that uses it, `Hironaka/Resolution/Algebraic/Monomial/Geometric`). -/
theorem _root_.Hironaka.Monomial.PieceFamily.mem_finset_sup_iff {ι : Type*} (s : Finset ι)
    (g : ι → Closeds X) (x : X) :
    x ∈ s.sup g ↔ ∃ i ∈ s, x ∈ g i := by
  rw [← SetLike.mem_coe, Closeds.coe_finset_sup, Finset.sup_eq_iSup]
  simp

/-- A point outside a finite union of closed sets has an affine neighbourhood outside it (used
by `Hironaka/Resolution/Algebraic/Monomial/Geometric/Local.lean`). -/
theorem _root_.AlgebraicGeometry.exists_affineOpens_of_not_mem_sup {ι : Type*} (s : Finset ι)
    (C : ι → Closeds X) {x : X}
    (hx : x ∉ s.sup C) : ∃ U : X.affineOpens, x ∈ U.1 ∧ ∀ y ∈ U.1, y ∉ s.sup C := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((s.sup C).compl : Opens X) from hx) (s.sup C).compl.isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy => hUV hy⟩

end AlgebraicGeometry.Scheme.IdealSheafData
