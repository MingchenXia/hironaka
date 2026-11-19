/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Snc.Dictionary
import Hironaka.Algebra.Local.PrimeProducts
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The dictionary, part II: total transforms and boundaries, and simple normal crossings as only
normal crossings

The second part of the translation between Kollár's divisor families and Hironaka's boundaries
(definitions in `Hironaka/Scheme/Snc/Dictionary.lean`):

* **Total transforms.** The members of Kollár's total transform
  `π⁻¹_tot(F) = (π_*^{-1} F^j)_j + F_exc` [Kol07, Definition 25] cover exactly
  `π⁻¹(V(F)) ∪ π⁻¹(V(D))`: the support of a strict transform is the closure of the part off the
  exceptional divisor (`coe_support_saturate`, on a locally Noetherian scheme), so it lies in
  `π⁻¹(V(F^j))`, and the part of `π⁻¹(V(F^j))` over the center is inside the exceptional divisor
  `π⁻¹(V(D))`, the last member. Hence the reduced union of the total transform is Hironaka's
  `red(f⁻¹(E) ∪ f⁻¹(D))` (`reducedTransform`) of the reduced union, and along a sequence
  Hironaka's boundaries `E_i` of [Hir64, Main Theorem II (iii)] are the reduced unions of Kollár's
  `E_i`; for a reduced `E`, of the total transforms of the component family of `E`.
* **Kollár's simple normal crossings give Hironaka's only normal crossings, for any family.** At a
  point `x` of `Z` with Kollár's coordinates `z` [Kol07, Definition 24], the members through `x`
  are `(z_{c(i)} = 0)` with `c` injective; the reduced union of the family is the radical of the
  product of the members (`vanishingIdeal_support`), its stalk at `x` has the minimal primes of
  `(∏ z_{c(i)})` (stalks commute with products, `stalkIdeal_mul`; radicals do not change minimal
  primes, `Ideal.radical_minimalPrimes`, and the stalk of a radical is sandwiched between the stalk
  and its radical), and these are the `(z_{c(i)})` (`IsLocalRing.minimalPrimes_span_prod`, each
  `z_{c(i)}` prime since `𝒪_{X,x}/(z_{c(i)})` is a regular local ring). This is
  [Hir64, Definition 2] at `x`; with `D = X` (`⊥`) it is "only normal crossings".
* **Clause (iii) of Main Theorem II.** Condition (3) of [Kol07, Definition 66] for the total
  transform of the component family of `E` at stage `i` gives Hironaka's clause (iii) for the
  boundary `E_i`: the stage is smooth over `k` (`IsSmooth.stageMap_smoothOfRelativeDimension`) and
  the boundary is the reduced union.

The converse direction, for the family of irreducible components, is in
`Hironaka/Resolution/Algebraic/Snc/DictionaryComponents.lean`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Scheme
  IdealSheafData DivisorFamily BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open Scheme AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The support of a family, as a set, is the finite union of the supports of its members. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.coe_support_eq_iUnion (F : DivisorFamily X) :
    (F.support : Set X) = ⋃ i, ((F.component i).support : Set X) := by
  change ((⨆ i, (F.component i).support : Closeds X) : Set X) = _
  rw [← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
  ext x
  simp

/-- The support of the strict transform of `J` under the blow-up with center `D` is the closure of
`π⁻¹(V(J)) ∖ π⁻¹(V(D))`, on a locally Noetherian scheme (`coe_support_saturate`); this is the
strict transform of [Hau14, Definition 6.2]. -/
theorem coe_support_strictTransform [IsLocallyNoetherian X] (D J : X.IdealSheafData) :
    ((J.strictTransform D).support : Set D.blowUp) =
      closure (D.blowUpπ ⁻¹' (J.support : Set X) \ D.blowUpπ ⁻¹'
          (D.support : Set X)) := by
  have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
  change (((J.comap D.blowUpπ).saturate (D.comap D.blowUpπ)).support :
    Set D.blowUp) = _
  rw [coe_support_saturate, support_comap, support_comap]
  rfl

/-- The members of the total transform [Kol07, Definition 25] of a family under the blow-up with
center `D` cover exactly `π⁻¹(V(F)) ∪ π⁻¹(V(D))`: each strict transform lies in `π⁻¹(V(F^j))`, and
the part of `π⁻¹(V(F^j))` over the center lies in the exceptional divisor, the last member. -/
theorem support_totalTransform_eq [IsLocallyNoetherian X] (F : DivisorFamily X)
    (D : X.IdealSheafData) :
    (F.totalTransform D).support =
      F.support.preimage D.blowUpπ.continuous ⊔
        D.support.preimage D.blowUpπ.continuous := by
  apply Closeds.ext
  rw [DivisorFamily.coe_support_eq_iUnion, Closeds.coe_sup]
  change (⋃ i : (F.totalTransform D).ι, (((F.totalTransform D).component i).support :
      Set D.blowUp)) =
    D.blowUpπ ⁻¹' (F.support : Set X) ∪ D.blowUpπ ⁻¹' (D.support : Set X)
  ext x'
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_preimage]
  constructor
  · rintro ⟨i, hi⟩
    rcases i with j | _
    · left
      change x' ∈ (((F.component j).strictTransform D).support : Set D.blowUp) at hi
      rw [coe_support_strictTransform] at hi
      have hcl : IsClosed (D.blowUpπ ⁻¹' ((F.component j).support : Set X)) :=
        (F.component j).support.isClosed.preimage D.blowUpπ.continuous
      have hx' := (hcl.closure_subset_iff.mpr Set.sdiff_subset) hi
      rw [DivisorFamily.coe_support_eq_iUnion]
      exact Set.mem_iUnion.mpr ⟨j, hx'⟩
    · right
      change x' ∈ ((D.comap D.blowUpπ).support : Set D.blowUp) at hi
      rw [support_comap] at hi
      exact hi
  · intro h
    by_cases hD : D.blowUpπ x' ∈ (D.support : Set X)
    · refine ⟨toLex (Sum.inr PUnit.unit), ?_⟩
      change x' ∈ ((D.comap D.blowUpπ).support : Set D.blowUp)
      rw [support_comap]
      exact hD
    · rcases h with hF | hD'
      · rw [DivisorFamily.coe_support_eq_iUnion] at hF
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hF
        refine ⟨toLex (Sum.inl j), ?_⟩
        change x' ∈ (((F.component j).strictTransform D).support : Set D.blowUp)
        rw [coe_support_strictTransform]
        exact subset_closure ⟨hj, hD⟩
      · exact absurd hD' hD

/-- The reduced union of the total transform of a family [Kol07, Definition 25] is Hironaka's
reduced total transform `red(f⁻¹(E) ∪ f⁻¹(D))` [Hir64, Main Theorem II (iii)] of its reduced union
(`reducedTransform`). -/
theorem unionIdeal_totalTransform [IsLocallyNoetherian X] (F : DivisorFamily X)
    (D : X.IdealSheafData) :
    (F.totalTransform D).unionIdeal = F.unionIdeal.reducedTransform D := by
  conv_lhs => unfold DivisorFamily.unionIdeal
  rw [support_totalTransform_eq]
  unfold reducedTransform
  rw [support_unionIdeal]

/-- `boundarySeq_eq_unionIdeal_totalTransformSeq`, the induction, with the locally Noetherian
hypothesis as an explicit argument so that it is carried to the blow-ups. -/
theorem boundarySeq_eq_unionIdeal_totalTransformSeq_aux {X : Scheme.{u}} (S : BlowUpSequence X)
    (hX : IsLocallyNoetherian X) (F : DivisorFamily X) (i : Fin (S.length + 1)) :
    S.boundarySeq F.unionIdeal i = (S.totalTransformSeq F i).unionIdeal := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · have hY : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
      change rest.boundarySeq (F.unionIdeal.reducedTransform D) ⟨j, Nat.lt_of_succ_lt_succ hi⟩ =
        (rest.totalTransformSeq (F.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ hi⟩).unionIdeal
      rw [← unionIdeal_totalTransform]
      exact ih hY (F.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- Hironaka's boundaries `E_i` [Hir64, Main Theorem II (iii)], started at the reduced union of a
family, are the reduced unions of Kollár's total transforms [Kol07, Definition 66 (1)] at every
stage of a sequence. -/
theorem boundarySeq_eq_unionIdeal_totalTransformSeq [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (F : DivisorFamily X) (i : Fin (S.length + 1)) :
    S.boundarySeq F.unionIdeal i = (S.totalTransformSeq F i).unionIdeal :=
  boundarySeq_eq_unionIdeal_totalTransformSeq_aux S inferInstance F i

/-- For a reduced `E`, the boundaries `E_i` of [Hir64, Main Theorem II] are the reduced unions of
Kollár's total transforms of the component family of `E`.
-/
theorem boundarySeq_eq_unionIdeal_totalTransformSeq_componentFamily [IsNoetherian X]
    (S : BlowUpSequence X) (E : X.IdealSheafData) [IsReduced E.subscheme]
    (i : Fin (S.length + 1)) :
    S.boundarySeq E i = (S.totalTransformSeq E.componentFamily i).unionIdeal := by
  conv_lhs => rw [← unionIdeal_componentFamily_of_isReduced E]
  exact boundarySeq_eq_unionIdeal_totalTransformSeq S E.componentFamily i

/-! ### Kollár's simple normal crossings give Hironaka's only normal crossings (any family) -/

/-- The support of a finite product of ideal sheaves is the union of the supports (`support_mul`
iterated). -/
theorem support_finset_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) :
    (∏ j ∈ s, I j).support = ⨆ j ∈ s, (I j).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih => rw [Finset.prod_insert has, support_mul, ih, Finset.iSup_insert]

/-- The reduced union of a family is the radical of the product of its members: both are the
vanishing ideal sheaf of `⋃ᵢ V(E^i)` (`vanishingIdeal_support`). -/
theorem unionIdeal_eq_radical_prod (F : DivisorFamily X) :
    F.unionIdeal = (∏ j, F.component j).radical := by
  unfold DivisorFamily.unionIdeal
  rw [← vanishingIdeal_support, support_finset_prod]
  congr 1
  change (⨆ j, (F.component j).support) = ⨆ j ∈ Finset.univ, (F.component j).support
  simp

/-- The stalk of an ideal sheaf lies in the stalk of its radical. -/
theorem stalkIdeal_le_stalkIdeal_radical (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x ≤ I.radical.stalkIdeal x :=
  stalkIdeal_mono I.le_radical x

/-- The stalk of the radical lies in the radical of the stalk (`Ideal.map_radical_le` on an affine
open computing the stalk). -/
theorem stalkIdeal_radical_le (I : X.IdealSheafData) (x : X) :
    I.radical.stalkIdeal x ≤ (I.stalkIdeal x).radical := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ I.radical U hx, stalkIdeal_eq_map_germ I U hx]
  change Ideal.map _ (I.ideal U).radical ≤ _
  exact Ideal.map_radical_le _

/-- The stalk of the radical of an ideal sheaf has the same minimal primes as the stalk of the
ideal sheaf (both stalks have the same radical). -/
theorem minimalPrimes_stalkIdeal_radical (I : X.IdealSheafData) (x : X) :
    (I.radical.stalkIdeal x).minimalPrimes = (I.stalkIdeal x).minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, ← Ideal.radical_minimalPrimes (I := I.stalkIdeal x)]
  congr 1
  apply le_antisymm
  · exact Ideal.radical_le_radical_iff.mpr (stalkIdeal_radical_le I x)
  · exact Ideal.radical_mono (stalkIdeal_le_stalkIdeal_radical I x)

/-- A coordinate of a regular system of parameters that generates the stalk of an ideal sheaf is a
prime element: the quotient by it is a regular local ring, hence a domain, and the coordinate is
nonzero (it is not in `𝔪²`). -/
theorem prime_of_stalkIdeal_eq_span {x : X} [IsRegularLocalRing (X.presheaf.stalk x)] {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} (hrs : IsRegularSystemOfParameters z) {Z : X.IdealSheafData}
    {j : Fin n} (hZ : Z.stalkIdeal x = Ideal.span {z j}) : Prime (z j) := by
  have hZ' : Z.stalkIdeal x = Ideal.span (z '' ↑({j} : Finset (Fin n))) := by
    rw [hZ]; simp
  have hreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ Z.stalkIdeal x) :=
    isRegularLocalRing_quotient_stalkIdeal_of_eq_span hrs hZ'
  have hdom : IsDomain (X.presheaf.stalk x ⧸ Z.stalkIdeal x) := inferInstance
  rw [hZ] at hdom
  have hprime : (Ideal.span {z j}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hne : z j ≠ 0 := by
    intro h0
    have := (mem_maximalIdeal_and_notMem_sq_of_span_eq hrs j).2
    rw [h0] at this
    exact this (Ideal.zero_mem _)
  exact (Ideal.span_singleton_prime hne).mp hprime

/-- From Kollár's simple normal crossings [Kol07, Definition 24 (4)] to Hironaka's only normal
crossings [Hir64, Definition 2], for an arbitrary family: if `Z` has simple normal crossings with
`F` then the reduced union of `F` has only normal crossings with `Z`. At `x ∈ Z` Kollár's
coordinates make the members through `x` the hyperplanes `(z_{c(i)} = 0)`, whose union has the
minimal primes `(z_{c(i)})` (`prod_stalkIdeal_eq_span` with `minimalPrimes_span_prod`). -/
theorem HasSncWith.isSncBoundaryWith_unionIdeal (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} {Z : X.IdealSheafData} (h : F.HasSncWith Z) :
    IsSncBoundaryWith F.unionIdeal Z := by
  classical
  intro x hx
  obtain ⟨n, z, ⟨hrs, c, hcinj, hc⟩, s, hs⟩ := h x hx
  refine ⟨n, z, hrs, ?_, s, hs⟩
  intro P hP
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  change P ∈ (F.unionIdeal.stalkIdeal x).minimalPrimes at hP
  rw [unionIdeal_eq_radical_prod, minimalPrimes_stalkIdeal_radical,
    Scheme.IdealSheafData.stalkIdeal_finset_prod, prod_stalkIdeal_eq_span c hc] at hP
  obtain ⟨i, -, hPi⟩ := minimalPrimes_span_prod
    (fun i _ => prime_of_stalkIdeal_eq_span hrs (hc i)) hP
  exact ⟨c i, hPi⟩

/-- The reduced union of a simple normal crossing family [Kol07, Definition 24 (1)–(3)] has only
normal crossings [Hir64, Definition 2 with `D = X`]. -/
theorem IsSnc.isSncBoundary_unionIdeal (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (h : F.IsSnc) : IsSncBoundary F.unionIdeal := by
  have hZ : F.HasSncWith ⊥ := by
    intro x _
    obtain ⟨n, z, hz⟩ := h.2 x
    refine ⟨n, z, hz, ∅, ?_⟩
    rw [Scheme.IdealSheafData.stalkIdeal_bot]
    simp
  exact HasSncWith.isSncBoundaryWith_unionIdeal f hZ

section Boundaries

variable [IsNoetherian X] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} (E : X.IdealSheafData)
  [IsReduced E.subscheme]

include f n

/-- From condition (3) of [Kol07, Definition 66] to clause (iii) of [Hir64, Main Theorem II]:
along a smooth blow-up sequence, if the center `Z_i` has simple normal crossings with Kollár's
total transform `E_i` of the component family of `E`, then Hironaka's boundary `E_i` has only
normal crossings with `Z_i`; the one-directional dictionary at the stage `X_i` (smooth over `k`)
with the boundary identified as the reduced union of the total transform. -/
theorem HasSncWith.isSncBoundaryWith_boundarySeq (hS : S.IsSmooth f) (i : Fin S.length)
    (h : (S.totalTransformSeq E.componentFamily i.castSucc).HasSncWith (S.center i)) :
    IsSncBoundaryWith (S.boundarySeq E i.castSucc) (S.center i) := by
  rw [boundarySeq_eq_unionIdeal_totalTransformSeq_componentFamily]
  have : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.stageMap_smoothOfRelativeDimension hS i.castSucc
  have : Smooth (S.stageMap i.castSucc ≫ f) := SmoothOfRelativeDimension.smooth n _
  exact HasSncWith.isSncBoundaryWith_unionIdeal (S.stageMap i.castSucc ≫ f) h

/-- Along a smooth blow-up sequence of order `d` starting with `(X, J, E.componentFamily)`, every
boundary `E_i` has only normal crossings with the center `D_i`: clause (iii) of
[Hir64, Main Theorem II] in the form used by its proof. -/
theorem IsOrderSeq.isSncBoundaryWith_boundarySeq {J : X.IdealSheafData} {d : ℕ}
    (h : S.IsOrderSeq f J E.componentFamily d) (i : Fin S.length) :
    IsSncBoundaryWith (S.boundarySeq E i.castSucc) (S.center i) :=
  HasSncWith.isSncBoundaryWith_boundarySeq f n E h.1 i (h.2 i).1

end Boundaries

end Hironaka.Sequence
