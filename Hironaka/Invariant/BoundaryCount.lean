/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberPullback
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intersections of members of a normal crossings divisor and the boundary count

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), proof of Proposition `pr:resol`, Step 1a ("reduction to the
nonboundary case": `s(x)` is the number of divisors in `E` through `x`, the intersections `H^s_α` of `s` members,
and "if `s ≥ 2` then by blowing up `C = H^s_α` we separate divisors contributing to `H^s_α`, thus creating new
points all with `s(x) < s`"); Bierstone--Milman 2008, §5.

Let `E` be a simple normal crossings divisor on `X` and `S` a set of indices of members.

* `memberInter E S = ⋂_{i ∈ S} E.get i`: `hasNormalCrossings_memberInter` (it has normal crossings with `E`),
  `isClosedSubmanifold_memberInter` (it is a closed submanifold, `0 < n`).
* `boundaryCount E x = #{i | x ∈ E.get i}`: `eventually_boundaryCount_le` (upper semicontinuous),
  `boundaryCount_map` (re-indexing along `E.map f`), `boundaryCount_map_geoStrictTransform_le`
  (along a blowup the strict transforms of the members through `z` come from members through `π z`).
* Proof: in adapted coordinates and a monomial chart `j` around `z`, all members of `S` through `z` would give `W_{s
  i}(z) = 0`, `s i ≠ j`; then the points `σ_j(W z + ε e_j)` lie on every member of `S`, hence in `C`, although their
  `j`-th coordinate is `ε ≠ 0`.
* The same curve, now taken close to `π z`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BoundaryCount

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupStrictSubmanifold BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings MarkedIdeals

noncomputable section

variable {n : ℕ}

section Members

variable {X : Type*} [TopologicalSpace X]

/-- The intersection of the members of `E` with indices in `S`. -/
def memberInter (E : List (Set X)) (S : Finset (Fin E.length)) : Set X :=
  {x | ∀ i ∈ S, x ∈ E.get i}

open Classical in
/-- **The boundary count** `s(x)`: the number of members of `E` through `x`. -/
def boundaryCount (E : List (Set X)) (x : X) : ℕ :=
  (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).card

/-- An intersection of closed members is closed. -/
theorem isClosed_memberInter {E : List (Set X)} (hE : ∀ H ∈ E, IsClosed H)
    (S : Finset (Fin E.length)) : IsClosed (memberInter E S) := by
  have : memberInter E S = ⋂ i ∈ S, E.get i := by
    ext x
    simp [memberInter]
  rw [this]
  exact isClosed_biInter fun i _ => hE _ (List.get_mem _ _)

/-- `x` lies on the coordinate subspace of a union iff on each. -/
theorem mem_coordSubspace_biUnion {ι : Type*} (S : Finset ι) (T : ι → Finset (Fin n))
    (w : ComplexModel n) : w ∈ coordSubspace (S.biUnion T) ↔ ∀ i ∈ S, w ∈ coordSubspace (T i) := by
  simp only [coordSubspace, mem_ofPred_eq, Finset.mem_biUnion]
  constructor
  · intro h i hi t ht
    exact h t ⟨i, hi, ht⟩
  · rintro h t ⟨i, hi, ht⟩
    exact h i hi t ht

open Classical in
/-- **Upper semicontinuity of the boundary count**: near `x`, only members through `x` pass. -/
theorem eventually_boundaryCount_le {E : List (Set X)} (hE : ∀ H ∈ E, IsClosed H) (x : X) :
    ∀ᶠ y in 𝓝 x, boundaryCount E y ≤ boundaryCount E x := by
  have h : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i :=
    eventually_all.mpr fun i => by
      by_cases hi : x ∈ E.get i
      · exact Eventually.of_forall fun _ h => absurd hi h
      · filter_upwards [(hE _ (List.get_mem _ _)).isOpen_compl.mem_nhds hi] with y hy _
        exact hy
  filter_upwards [h] with y hy
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  by_contra hx
  exact hy i hx hi

open Classical in
/-- **Re-indexing along a map of the members.** -/
theorem boundaryCount_map {Y : Type*} (f : Set X → Set Y) (E : List (Set X)) (z : Y) :
    boundaryCount (E.map f) z =
      (Finset.univ.filter fun i : Fin E.length => z ∈ f (E.get i)).card := by
  unfold boundaryCount
  refine Finset.card_equiv (finCongr (List.length_map f)) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, finCongr_apply, List.get_eq_getElem,
    List.getElem_map, Fin.val_cast]

end Members

section Manifold

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Truncating the dimension at `n` does not change the coordinate plane. -/
theorem complexCoordinatePlane_min (k : ℕ) :
    complexCoordinatePlane n (min k n) = complexCoordinatePlane n k := by
  ext w
  simp only [complexCoordinatePlane, mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  have hi := i.2
  have : min k n ≤ i.1 ↔ k ≤ i.1 := by omega
  rw [this]

/-- **An intersection of members has normal crossings with `E`.** -/
theorem hasNormalCrossings_memberInter {E : List (Set X)} (hE : IsSNCDivisor n E)
    (S : Finset (Fin E.length)) : HasNormalCrossings n (memberInter E S) E := by
  intro x hx
  obtain ⟨T, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, -⟩ := hE.2 x
  refine ⟨S.biUnion T, T, ⟨Φ, hΦt, hΦ0, ?_⟩, hcard⟩
  rintro (_ | i) hxi y hy hyΦ
  · change (∀ i ∈ S, y ∈ E.get i) ↔
      Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S.biUnion T)
    rw [mem_coordSubspace_biUnion]
    exact forall₂_congr fun i hi => hΦA i (hx i hi) hy hyΦ
  · exact hΦA i hxi hy hyΦ

/-- **An intersection of members is a closed submanifold** (`0 < n`). -/
theorem isClosedSubmanifold_memberInter (hn : 0 < n) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (S : Finset (Fin E.length)) : IsClosedSubmanifold n (memberInter E S) := by
  refine ⟨isClosed_memberInter hE.1 S, fun x hx => ?_⟩
  obtain ⟨kC, kN, Φ, s, -, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ _) hE
    (isTransverse_univ_of_isSNCDivisor hE) (hasNormalCrossings_memberInter hE S) hx
  refine ⟨min kC n, RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
    (fun {y} hy hyΦ => ?_) hx (mem_chart_source _ x) Φ.center_mem_source⟩
  have h := (hflat hy hyΦ).1
  rw [← complexCoordinatePlane_min] at h
  exact h

section Blowup

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **The boundary count does not increase**: the strict transforms of the members through `z` come
from members through `π z`. -/
theorem boundaryCount_map_geoStrictTransform_le (hπc : Continuous π) {E : List (Set X)}
    (hE : ∀ H ∈ E, IsClosed H) (z : Y) :
    boundaryCount (E.map (geoStrictTransform π C)) z ≤ boundaryCount E (π z) := by
  rw [boundaryCount_map]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact geoStrictTransform_subset_preimage hπc (hE _ (List.get_mem _ _)) hi

end Blowup

end Manifold

section Tower

open BlowupTowers

variable {X Y : CMfd.{u} n}

theorem isClosed_of_mem_take_E_geoTransformAlong (𝔪 : MarkedIdeal n X)
    (hE : ∀ H ∈ 𝔪.E, IsClosed H) (T : BlowupTower X Y) :
    ∀ H ∈ (𝔪.geoTransformAlong T).E.take 𝔪.E.length, IsClosed H := by
  cases T with
  | refl => simpa using hE
  | step T C π hπ =>
    intro H hH
    have hlen :
        𝔪.E.length ≤ ((𝔪.geoTransformAlong T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
    rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E,
      List.take_append_of_le_length hlen] at hH
    obtain ⟨H₀, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hH)
    exact isClosed_closure

end Tower

end

end Hironaka.BoundaryCount
