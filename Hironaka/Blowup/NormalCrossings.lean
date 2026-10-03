/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Simple normal crossings divisors and normal crossings with a submanifold

Sources: Włodarczyk 2005 §2.1 (the ordered collection `E` of a marked ideal, whose components "have simultaneously
simple normal crossings"; a centre `C` "has simple normal crossings with `E`"), Bierstone--Milman 2008, Definitions
2.1 (`E = ∑ Hᵢ` an ordered simple normal crossings divisor, `Hᵢ` smooth hypersurfaces, not necessarily irreducible,
transverse to `N`) and 2.2 (`C`, `E` have only normal crossings).

All three notions are instances of one local picture: holomorphic coordinates at `x` in which each
member of a finite family passing through `x` is a coordinate subspace `{z | ∀ j ∈ S, z j = 0}`
(`IsCoordinateFamilyAt`).  The coordinates are a `LocalHolomorphicEquivAt` composed with the preferred
chart, exactly as in `RegularAtDim`.

## Main declarations

* `coordSubspace S`, `IsCoordinateFamilyAt n A S x`;
* `IsSNCDivisor n E` -- `E : List (Set M)` (the list order is the order of `E`; the newest exceptional
  divisor is appended last): closed, and at each point the members through it are DISTINCT coordinate
  hyperplanes of one coordinate system;
* `HasNormalCrossings n C E` -- at each point of `C`, one coordinate system makes `C` a coordinate
  subspace and every member of `E` through the point a coordinate hyperplane;
* `IsTransverse n N E` -- as `HasNormalCrossings`, and moreover no hyperplane of `E` through the point
  contains `N` there (its coordinate is not one of those cutting out `N`);
* sanity checks: `isSNCDivisor_nil`, `coordSubspace_eq_complexCoordinatePlane`,
  `hasNormalCrossings_nil_of_isClosedSubmanifold`, `isTransverse_nil_of_isClosedSubmanifold`.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.NormalCrossings

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The coordinate subspace `{z | z j = 0 for j ∈ S}` of `ℂⁿ`. -/
def coordSubspace (S : Finset (Fin n)) : Set (ComplexModel n) :=
  {z | ∀ j ∈ S, z j = 0}

/-- `ℂᵏ × 0` is the coordinate subspace cut out by the last `n - k` coordinates. -/
theorem coordSubspace_eq_complexCoordinatePlane (k : ℕ) :
    coordSubspace (Finset.univ.filter fun j : Fin n => k ≤ j.1) = complexCoordinatePlane n k := by
  ext z
  simp [coordSubspace, complexCoordinatePlane]

variable (n) in
/-- **Adapted coordinates for a family at a point.** There are holomorphic coordinates at `x`
(a local biholomorphism `Φ` of `ℂⁿ` after the preferred chart, centred at `0`) in which every member
`A i` passing through `x` is, near `x`, the coordinate subspace cut out by `S i`. -/
def IsCoordinateFamilyAt {ι : Type*} (A : ι → Set M) (S : ι → Finset (Fin n)) (x : M) : Prop :=
  ∃ Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x),
    Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
    Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
    ∀ i, x ∈ A i → ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ A i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))

variable [IsComplexManifold n M]

/-- Centred holomorphic coordinates exist at every point (from `regularAtDim_univ`). -/
theorem exists_centred_coordinates (x : M) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 := by
  obtain ⟨-, -, Φ, hsrc, h0, -⟩ := AnalyticIrreducibleComponents.regularAtDim_univ (n := n) x
  exact ⟨Φ, hsrc, h0⟩

/-- The empty family is adapted at every point. -/
theorem isCoordinateFamilyAt_of_isEmpty {ι : Type*} [IsEmpty ι] (A : ι → Set M)
    (S : ι → Finset (Fin n)) (x : M) : IsCoordinateFamilyAt n A S x := by
  obtain ⟨Φ, hsrc, h0⟩ := exists_centred_coordinates (n := n) x
  exact ⟨Φ, hsrc, h0, fun i => isEmptyElim i⟩

variable (n) in
/-- **An ordered simple normal crossings divisor**, as the list `E = [H₁, …, H_s]` of its members
(smooth hypersurfaces, not necessarily connected; the list order is the order of `E`).  The members
are closed, and at every point the members through it are distinct coordinate hyperplanes of one
holomorphic coordinate system. -/
def IsSNCDivisor (E : List (Set M)) : Prop :=
  (∀ H ∈ E, IsClosed H) ∧
    ∀ x : M, ∃ S : Fin E.length → Finset (Fin n),
      IsCoordinateFamilyAt n (fun i => E.get i) S x ∧
        (∀ i, x ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | x ∈ E.get i}

/-- The empty divisor has simple normal crossings. -/
theorem isSNCDivisor_nil : IsSNCDivisor n ([] : List (Set M)) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun x =>
    ⟨fun i => i.elim0,
      @isCoordinateFamilyAt_of_isEmpty _ _ _ _ _ _ (inferInstanceAs (IsEmpty (Fin 0))) _ _ x,
      fun i => i.elim0,
      fun i _ => i.elim0⟩⟩

variable (n) in
/-- **`C` has only normal crossings with `E`**: at every point of `C` one holomorphic coordinate system
makes `C` a coordinate subspace (cut out by `S₀`) and every member of `E` through the point a coordinate
hyperplane. -/
def HasNormalCrossings (C : Set M) (E : List (Set M)) : Prop :=
  ∀ x ∈ C, ∃ (S₀ : Finset (Fin n)) (S : Fin E.length → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim C fun i => E.get i)
      (fun o => o.elim S₀ S) x ∧
      ∀ i, x ∈ E.get i → (S i).card = 1

variable (n) in
/-- **`E` is transverse to `N`**: normal crossings at the points of `N`, and no member of `E` through
a point of `N` contains `N` near that point (its coordinate is not among those cutting out `N`). -/
def IsTransverse (N : Set M) (E : List (Set M)) : Prop :=
  ∀ x ∈ N, ∃ (S₀ : Finset (Fin n)) (S : Fin E.length → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim N fun i => E.get i)
      (fun o => o.elim S₀ S) x ∧
      ∀ i, x ∈ E.get i → (S i).card = 1 ∧ Disjoint (S i) S₀

/-- Transversality implies normal crossings. -/
theorem IsTransverse.hasNormalCrossings {N : Set M} {E : List (Set M)} (h : IsTransverse n N E) :
    HasNormalCrossings n N E := fun x hx => by
  obtain ⟨S₀, S, hcoord, hS⟩ := h x hx
  exact ⟨S₀, S, hcoord, fun i hi => (hS i hi).1⟩

/-- A regular point of `C` of dimension `k` is a point where `C` alone is a coordinate subspace. -/
theorem isCoordinateFamilyAt_of_regularAtDim {C : Set M} {x : M} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) (E : List (Set M)) (S : Fin E.length → Finset (Fin n))
    (hE : ∀ i, x ∉ E.get i) :
    IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim C fun i => E.get i)
      (fun o => o.elim (Finset.univ.filter fun j : Fin n => k ≤ j.1) S) x := by
  obtain ⟨-, -, Φ, hsrc, h0, hflat⟩ := hC
  refine ⟨Φ, hsrc, h0, ?_⟩
  rintro (_ | i) hxi y hy hyΦ
  · simpa [coordSubspace_eq_complexCoordinatePlane] using hflat hy hyΦ
  · exact absurd hxi (hE i)

/-- **A closed submanifold has normal crossings with the empty divisor.** -/
theorem hasNormalCrossings_nil_of_isClosedSubmanifold {C : Set M}
    (hC : IsClosedSubmanifold n C) : HasNormalCrossings n C ([] : List (Set M)) := by
  intro x hx
  obtain ⟨k, hk⟩ := hC.2 x hx
  exact ⟨_, fun i => i.elim0, isCoordinateFamilyAt_of_regularAtDim hk [] _ fun i => i.elim0,
    fun i => i.elim0⟩

/-- **The empty divisor is transverse to every closed submanifold.** -/
theorem isTransverse_nil_of_isClosedSubmanifold {N : Set M} (hN : IsClosedSubmanifold n N) :
    IsTransverse n N ([] : List (Set M)) := by
  intro x hx
  obtain ⟨k, hk⟩ := hN.2 x hx
  exact ⟨_, fun i => i.elim0, isCoordinateFamilyAt_of_regularAtDim hk [] _ fun i => i.elim0,
    fun i => i.elim0⟩

end

end Hironaka.NormalCrossings
