import Hironaka.Invariant.BoundaryCount

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Intersections of members with a submanifold transverse to the divisor

Hironaka phase H2 (TN3), an input of the monomial case along a submanifold `N`
(`hir:monomial-case`, `hir:monomial-invariant-geometry` (5) for `N ≠ M`,
`blueprint/src/hironaka.tex`):
claimed on I-0977 C-0071.  Blueprint `bcalc:member-intersection-along` (chapter
`blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of the proof of
`pr:resol` (the monomial case: the centre is the maximal locus of the monomial invariant, an
intersection of components of the divisor restricted to `N`); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §5.

Let `E` be a simple normal crossings divisor transverse to `N` (`NormalCrossings.IsTransverse`:
at each point of `N` one coordinate system makes `N` a coordinate subspace `L_{S₀}` and each member
through the point a coordinate hyperplane `{w_{t_i} = 0}` with `t_i ∉ S₀`), and `S` a set of
members.

* `hasNormalCrossings_inter_memberInter`: `N ∩ ⋂_{i ∈ S} E_i` has only normal crossings with `E`
  (in the transversality coordinates it is `L_{S₀ ∪ {t_i : i ∈ S}}`);
* `isClosedSubmanifold_inter_memberInter` (`N` closed, `0 < n`): it is a closed submanifold;
* `isAdmissibleCentre_inter_memberInter`: if it lies in the cosupport of `(M, N, E, 𝔞, d)`, it is an
  admissible centre; `_of_isWellFormed` for a well-formed marked ideal.

These are the along-`N` versions of `BoundaryCount.hasNormalCrossings_memberInter`,
`isClosedSubmanifold_memberInter`, `isAdmissibleCentre_memberInter` (`N = M`), with the same proofs:
the flattening of the centre comes from
`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberInterAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings MarkedIdeals BoundaryCount

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The trace on `N` of an intersection of members has normal crossings with `E`**, for `E`
transverse to `N`: in the transversality coordinates at a point, `N = L_{S₀}` and the members
through it are the hyperplanes `{w_{t_i} = 0}`, so `N ∩ ⋂_{i ∈ S} E_i = L_{S₀ ∪ ⋃_{i ∈ S} T_i}`. -/
theorem hasNormalCrossings_inter_memberInter {N : Set X} {E : List (Set X)}
    (hT : IsTransverse n N E) (S : Finset (Fin E.length)) :
    HasNormalCrossings n (N ∩ memberInter E S) E := by
  intro x hx
  obtain ⟨S₀, T, ⟨Φ, hΦt, hΦ0, hΦA⟩, hT1⟩ := hT x hx.1
  refine ⟨S₀ ∪ S.biUnion T, T, ⟨Φ, hΦt, hΦ0, ?_⟩, fun i hi => (hT1 i hi).1⟩
  rintro (_ | i) hxi y hy hyΦ
  · change (y ∈ N ∧ ∀ i ∈ S, y ∈ E.get i) ↔
      Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S₀ ∪ S.biUnion T)
    have hunion : ∀ w : ComplexModel n, w ∈ coordSubspace (S₀ ∪ S.biUnion T) ↔
        w ∈ coordSubspace S₀ ∧ w ∈ coordSubspace (S.biUnion T) := fun w => by
      simp only [coordSubspace, Finset.mem_union, mem_ofPred_eq]
      exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩,
        fun h j hj => hj.elim (h.1 j) (h.2 j)⟩
    rw [hunion, mem_coordSubspace_biUnion]
    exact and_congr (hΦA none hx.1 hy hyΦ)
      (forall₂_congr fun i hi => hΦA (some i) (hx.2 i hi) hy hyΦ)
  · exact hΦA (some i) hxi hy hyΦ

/-- **The trace on `N` of an intersection of members is a closed submanifold** (`N` closed, `E`
simple normal crossings and transverse to `N`, `0 < n`). -/
theorem isClosedSubmanifold_inter_memberInter (hn : 0 < n) {N : Set X} (hNc : IsClosed N)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (S : Finset (Fin E.length)) : IsClosedSubmanifold n (N ∩ memberInter E S) := by
  refine ⟨hNc.inter (isClosed_memberInter hE.1 S), fun x hx => ?_⟩
  obtain ⟨kC, kN, Φ, s, -, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ _) hE
    (isTransverse_univ_of_isSNCDivisor hE) (hasNormalCrossings_inter_memberInter hT S) hx
  refine ⟨min kC n, RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
    (fun {y} hy hyΦ => ?_) hx (mem_chart_source _ x) Φ.center_mem_source⟩
  have h := (hflat hy hyΦ).1
  rw [← complexCoordinatePlane_min] at h
  exact h

/-- **The trace on `N` of an intersection of members inside the cosupport is an admissible
centre** of `(M, N, E, 𝔞, d)` (`N` closed, `E` simple normal crossings and transverse to `N`). -/
theorem isAdmissibleCentre_inter_memberInter (hn : 0 < n) (𝔪 : MarkedIdeal n X)
    (hNc : IsClosed 𝔪.N) (hE : IsSNCDivisor n 𝔪.E) (hT : IsTransverse n 𝔪.N 𝔪.E)
    (S : Finset (Fin 𝔪.E.length)) (hsub : 𝔪.N ∩ memberInter 𝔪.E S ⊆ 𝔪.cosupp) :
    𝔪.IsAdmissibleCentre (𝔪.N ∩ memberInter 𝔪.E S) :=
  ⟨isClosedSubmanifold_inter_memberInter hn hNc hE hT S, hsub,
    hasNormalCrossings_inter_memberInter hT S⟩

/-- **The same for a well-formed marked ideal.** -/
theorem isAdmissibleCentre_inter_memberInter_of_isWellFormed (hn : 0 < n) {𝔪 : MarkedIdeal n X}
    (h𝔪 : 𝔪.IsWellFormed) (S : Finset (Fin 𝔪.E.length))
    (hsub : 𝔪.N ∩ memberInter 𝔪.E S ⊆ 𝔪.cosupp) :
    𝔪.IsAdmissibleCentre (𝔪.N ∩ memberInter 𝔪.E S) :=
  isAdmissibleCentre_inter_memberInter hn 𝔪 h𝔪.isClosedSubmanifold_N.1 h𝔪.isSNCDivisor
    h𝔪.isTransverse S hsub

end

end Hironaka.MemberInterAlong
