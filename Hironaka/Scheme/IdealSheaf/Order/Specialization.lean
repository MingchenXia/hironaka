/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Semicontinuity.Defs
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Monotonicity of the order along specialization

[Hau03, Appendix A]: `ord_Z = min_{a ∈ Z} ord_a I`, "where it suffices to take the minimum over the
closed points `a` of `Z`", and the order "does not increase under localization" (Hauser refers to
Zariski and Nagata for this). Here: if `x ∈ closure {η}` then `ord_η I ≤ ord_x I`, which is the
content of the upper semicontinuity of `Hironaka/Scheme/IdealSheaf/Order/Semicontinuity.lean`; in
characteristic zero it replaces the Zariski–Nagata argument.

* The general form: for an ideal sheaf `I` whose order function is upper semicontinuous, a closed
  set `{x : ord_x I ≥ y}` containing `η` contains every specialization of `η`
  (`ord_le_ord_of_specializes_of_upperSemicontinuous`); hence the generic point of an irreducible
  closed `Z` has the smallest order on `Z` (`ordAlong_le_ord_of_upperSemicontinuous`,
  `ordAlong_eq_iInf_of_upperSemicontinuous`), the minimum may be taken over the closed points of `Z`
  when the closed points are dense in every locally closed subset (a Jacobson space,
  `ordAlong_eq_iInf_closedPoints_of_upperSemicontinuous`), and Kollár's convention `ord_Z I ≥ m`
  for a reducible closed `Z` (`Hironaka/Scheme/IdealSheaf/Order/Along.lean`) is the pointwise bound
  on `Z` (`leOrdAlong_iff_forall_mem_of_upperSemicontinuous`), since every point of a closed set is
  a specialization of one of its generic points (`Closeds.exists_mem_genericPoints_specializes`, by
  Zorn's lemma inside `Z` as in Mathlib's `exists_preirreducible`).
* The same for `f : X ⟶ Spec k` smooth of relative dimension `n` over a field `k` of
  characteristic zero (`upperSemicontinuous_ord`; the closed points are dense in every locally
  closed subset by Mathlib's `LocallyOfFiniteType.jacobsonSpace`).

Used throughout for the orders at the generic points of centres and along specialization
(`Hironaka/Scheme/BlowUpSequence/OrderAlongCenter.lean`,
`Hironaka/Scheme/BlowUpSequence/CentersCosupport.lean`, `Hironaka/Scheme/Snc/DictionaryOrder.lean`,
`Hironaka/Resolution/Algebraic/Balanced/Order.lean`,
`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SkippedRound.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedClaimTools.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`, among others).
-/

public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- The topological input for a reducible closed `Z` (Kollár's convention, [Kol07, Definition 47]):
in a sober `T₀` space every point `z` of a closed set `Z` is a specialization of a generic point of
`Z` — a maximal irreducible closed subset of `Z` through `z` exists (Zorn, as in Mathlib's
`exists_preirreducible`), and its generic point is a generic point of `Z`
(`Closeds.mem_genericPoints_iff`). -/
theorem Closeds.exists_mem_genericPoints_specializes [T0Space X] [QuasiSober X] (Z : Closeds X)
    {z : X} (hz : z ∈ Z) : ∃ η ∈ Z.genericPoints, η ⤳ z := by
  obtain ⟨T, -, hT⟩ := zorn_subset_nonempty {T : Set X | T ⊆ Z ∧ IsIrreducible T ∧ z ∈ T}
    (fun c hc hcc hne => by
      obtain ⟨T₀, hT₀⟩ := hne
      refine ⟨⋃₀ c, ⟨Set.sUnion_subset fun T hT => (hc hT).1,
        ⟨⟨z, Set.mem_sUnion_of_mem (hc hT₀).2.2 hT₀⟩, ?_⟩,
        Set.mem_sUnion_of_mem (hc hT₀).2.2 hT₀⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      intro u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩
      obtain ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
      obtain ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
      rcases hcc.total hpc hqc with hpq | hqp
      · obtain ⟨w, hwq, hwuv⟩ := (hc hqc).2.1.2 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
        exact ⟨w, Set.mem_sUnion_of_mem hwq hqc, hwuv⟩
      · obtain ⟨w, hwp, hwuv⟩ := (hc hpc).2.1.2 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
        exact ⟨w, Set.mem_sUnion_of_mem hwp hpc, hwuv⟩)
    (closure {z}) ⟨Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz),
      isIrreducible_singleton.closure, subset_closure rfl⟩
  obtain ⟨hTZ, hTirr, hzT⟩ := hT.prop
  have hTc : closure T = T :=
    (hT.eq_of_subset ⟨Z.isClosed.closure_subset_iff.mpr hTZ, hTirr.closure, subset_closure hzT⟩
      subset_closure).symm
  have hη : IsGenericPoint hTirr.genericPoint T :=
    hTirr.isGenericPoint_genericPoint (isClosed_of_closure_subset hTc.le)
  refine ⟨hTirr.genericPoint, ?_, hη.specializes hzT⟩
  rw [Closeds.mem_genericPoints_iff, hη.def]
  exact ⟨⟨hTZ, hTirr⟩, fun T' hT' hle => (hT.eq_of_subset ⟨hT'.1, hT'.2, hle hzT⟩ hle).symm.le⟩

end TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TopologicalSpace

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

section General

variable (hI : UpperSemicontinuous fun x => I.ord x)

include hI

/-- General form of "does not increase under localization" ([Hau03, Appendix A]): when
`x ↦ ord_x I` is upper semicontinuous,
`ord_η I ≤ ord_x I` for `η ⤳ x` — the closed set `{ord ≥ ord_η I}` contains `η`, hence `x`. -/
theorem ord_le_ord_of_specializes_of_upperSemicontinuous {η x : X} (h : η ⤳ x) :
    I.ord η ≤ I.ord x :=
  h.mem_closed (upperSemicontinuous_iff_isClosed_preimage.mp hI (I.ord η))
    (show I.ord η ≤ I.ord η from le_rfl)

/-- General form: the generic point of an irreducible closed `Z` has the smallest order on `Z`. -/
theorem ordAlong_le_ord_of_upperSemicontinuous (Z : IrreducibleCloseds X) {z : X} (hz : z ∈ Z) :
    I.ordAlong Z ≤ I.ord z :=
  ord_le_ord_of_specializes_of_upperSemicontinuous I hI
    (Z.isGenericPoint_genericPoint.specializes hz)

/-- [Hau03, Appendix A], general form: `ord_Z I = min_{z ∈ Z} ord_z I` for an irreducible closed
`Z` (attained at the generic point). -/
theorem ordAlong_eq_iInf_of_upperSemicontinuous (Z : IrreducibleCloseds X) :
    I.ordAlong Z = ⨅ z ∈ (Z : Set X), I.ord z :=
  le_antisymm (le_iInf₂ fun _ hz => ordAlong_le_ord_of_upperSemicontinuous I hI Z hz)
    (iInf₂_le Z.genericPoint Z.isGenericPoint_genericPoint.mem)

/-- [Hau03, Appendix A], "it suffices to take the minimum over the closed points", general form:
in a Jacobson space (closed points dense in every locally closed subset), `ord_Z I` is the minimum
of `ord_a I` over the closed points `a ∈ Z`: when `ord_Z I = m < ∞`, the locally closed set
`Z ∖ {ord ≥ m + 1}` contains the generic point, hence a closed point `a`, and `ord_a I ≤ m`. -/
theorem ordAlong_eq_iInf_closedPoints_of_upperSemicontinuous [JacobsonSpace X]
    (Z : IrreducibleCloseds X) :
    I.ordAlong Z = ⨅ z ∈ (Z : Set X) ∩ closedPoints X, I.ord z := by
  refine le_antisymm
    (le_iInf₂ fun _ hz => ordAlong_le_ord_of_upperSemicontinuous I hI Z hz.1) ?_
  rcases eq_or_ne (I.ordAlong Z) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  have hclosed : IsClosed {x | I.ordAlong Z + 1 ≤ I.ord x} :=
    upperSemicontinuous_iff_isClosed_preimage.mp hI (I.ordAlong Z + 1)
  have hne' : ((Z : Set X) ∩ {x | I.ordAlong Z + 1 ≤ I.ord x}ᶜ).Nonempty :=
    ⟨Z.genericPoint, Z.isGenericPoint_genericPoint.mem, fun h =>
      (not_le.mpr ((ENat.lt_add_one_iff hne).mpr le_rfl)) h⟩
  obtain ⟨a, ⟨haZ, ha⟩, hac⟩ := nonempty_inter_closedPoints hne'
    (Z.isClosed.isLocallyClosed.inter hclosed.isOpen_compl.isLocallyClosed)
  exact (iInf₂_le a ⟨haZ, hac⟩).trans ((ENat.lt_add_one_iff hne).mp (not_le.mp ha))

/-- Kollár's convention `ord_Z I ≥ m` for a closed `Z` that need not be irreducible
(`Hironaka/Scheme/IdealSheaf/Order/Along.lean`), general form: it holds exactly when `ord_z I ≥ m`
at every point of `Z`. -/
theorem leOrdAlong_iff_forall_mem_of_upperSemicontinuous (Z : Closeds X) (m : ℕ∞) :
    I.LeOrdAlong Z m ↔ ∀ z ∈ Z, m ≤ I.ord z := by
  constructor
  · intro h z hz
    obtain ⟨η, hη, hspec⟩ := Z.exists_mem_genericPoints_specializes hz
    exact (h η hη).trans (ord_le_ord_of_specializes_of_upperSemicontinuous I hI hspec)
  · intro h η hη
    exact h η hη.1

end General

section Smooth

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n

/-- The order "does not increase under localization" ([Hau03, Appendix A]; the content of the upper
semicontinuity): on a scheme smooth over a field of characteristic zero, `ord_η I ≤ ord_x I` when
`η` specializes to `x`. -/
theorem ord_le_ord_of_specializes {η x : X} (h : η ⤳ x) : I.ord η ≤ I.ord x :=
  ord_le_ord_of_specializes_of_upperSemicontinuous I (upperSemicontinuous_ord f n I) h

/-- In terms of closures: if `x ∈ closure {η}` then `ord_η I ≤ ord_x I`. -/
theorem ord_le_ord_of_mem_closure {η x : X} (h : x ∈ closure {η}) : I.ord η ≤ I.ord x :=
  ord_le_ord_of_specializes I f n (specializes_iff_mem_closure.mpr h)

/-- The generic point of `Z` has the smallest order on `Z`. -/
theorem ordAlong_le_ord (Z : IrreducibleCloseds X) {z : X} (hz : z ∈ Z) :
    I.ordAlong Z ≤ I.ord z :=
  ordAlong_le_ord_of_upperSemicontinuous I (upperSemicontinuous_ord f n I) Z hz

/-- [Hau03, Appendix A]: `ord_Z I = min_{z ∈ Z} ord_z I` for an irreducible closed `Z`. -/
theorem ordAlong_eq_iInf (Z : IrreducibleCloseds X) :
    I.ordAlong Z = ⨅ z ∈ (Z : Set X), I.ord z :=
  ordAlong_eq_iInf_of_upperSemicontinuous I (upperSemicontinuous_ord f n I) Z

/-- [Hau03, Appendix A], "where it suffices to take the minimum over the closed points `a` of `Z`":
a scheme locally of finite type over a field is a Jacobson space (Mathlib's
`LocallyOfFiniteType.jacobsonSpace`). -/
theorem ordAlong_eq_iInf_closedPoints (Z : IrreducibleCloseds X) :
    I.ordAlong Z = ⨅ z ∈ (Z : Set X) ∩ closedPoints X, I.ord z := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact ordAlong_eq_iInf_closedPoints_of_upperSemicontinuous I (upperSemicontinuous_ord f n I) Z

/-- Kollár's convention `ord_Z I ≥ m` for a closed `Z` that need not be irreducible holds exactly
when `ord_z I ≥ m` at every point `z` of `Z`. -/
theorem leOrdAlong_iff_forall_mem (Z : Closeds X) (m : ℕ∞) :
    I.LeOrdAlong Z m ↔ ∀ z ∈ Z, m ≤ I.ord z :=
  leOrdAlong_iff_forall_mem_of_upperSemicontinuous I (upperSemicontinuous_ord f n I) Z m

end Smooth

end AlgebraicGeometry.Scheme.IdealSheafData
