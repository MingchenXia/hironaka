/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaBoundaryCountAnalyticSuperlevels

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

import Hironaka.Invariant.InvariantClosedSuperlevels

set_option autoImplicit false

/-!
# Actual analytic monomial-invariant superlevels

Genuine nearby exponent freezing and actual feasible-subset maxima produce
local analytic equations, then global analyticity. Actual canonical monomial
thresholds are connected directly to these producers. Companion/history
thresholds and the global auxiliary-chain resolution engine remain open.
Blueprint: `hironaka-monomial-superlevels-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaMonomialAnalyticSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings MonomialInvariant MonomialCase MonomialCaseAlong
  ResolutionInvariantSpec CanonicalCentres GeneralValue GermIdealOrder DivisorExponentAlong
  HironakaOrderTupleAnalyticSuperlevels

noncomputable section

variable {n : ℕ}

/-- A genuine nonbottom lower bound on the actual feasible maximum is witnessed
by one of the actual feasible subsets; no top-set certificate is input. -/
theorem le_inv_iff_exists_feasible (S : Finset ℕ) (a : ℕ → ℕ) (d : ℕ) (v : Val) :
    (v : WithBot Val) ≤ inv n S a d ↔ ∃ K ∈ feasible S a d, v ≤ key n a K := by
  classical
  constructor
  · intro hv
    have hne : (feasible S a d).Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp [inv, he] at hv
    obtain ⟨K, hK, hmax, -⟩ := exists_top (n := n) (feasible_nonempty_iff.mp hne)
    rw [hmax] at hv
    exact ⟨K, hK, WithBot.coe_le_coe.mp hv⟩
  · rintro ⟨K, hK, hv⟩
    exact (WithBot.coe_le_coe.mpr hv).trans (Finset.le_max (Finset.mem_image_of_mem _ hK))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

private theorem analytic_of_closed_locally_analytic {A : Set M} (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∃ B : Set M, IsComplexAnalyticSubset (n := n) B ∧
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ B ∩ U = A ∩ U) :
    IsComplexAnalyticSubset (n := n) A := by
  intro x
  by_cases hx : x ∈ A
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hA Subset.rfl hx
  obtain ⟨B, hB, U, hU, hxU, heq⟩ := hlocal x hx
  obtain ⟨P⟩ := hB x
  let e := (complexChartAt (n := n) x).val
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨{ generatorCount := P.generatorCount
            generator := P.generator
            coordinateNeighborhood := P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' U)
            isOpen_coordinateNeighborhood :=
              P.isOpen_coordinateNeighborhood.inter (e.isOpen_inter_preimage_symm hU)
            center_mem_coordinateNeighborhood := ⟨P.center_mem_coordinateNeighborhood,
              e.map_source hxs, by
                change e.symm (e x) ∈ U
                rw [e.left_inv hxs]
                exact hxU⟩
            coordinateNeighborhood_subset_target := fun _ hz => hz.2.1
            generator_holomorphic := fun i =>
              (P.generator_holomorphic i).mono inter_subset_left
            zeroLocus := ?_ }⟩
  intro y hy hyO
  have hyU : y ∈ U := by
    have ht : e.symm (e y) ∈ U := hyO.2.2
    rwa [e.left_inv hy] at ht
  rw [← P.zeroLocus hy hyO.1]
  constructor
  · intro hyA
    have hyB : y ∈ B ∩ U := by rw [heq]; exact ⟨hyA, hyU⟩
    exact hyB.1
  · intro hyB
    have hyA : y ∈ A ∩ U := by rw [← heq]; exact ⟨hyB, hyU⟩
    exact hyA.1

/-- Actual original coefficients and actual feasible subsets internally produce
an analytic finite union agreeing with the complete monomial superlevel nearby. -/
theorem exists_analytic_near_gammaAlong_superlevel (hn : 0 < n) (N : Set M)
    (hN : IsClosedSubmanifold n N) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (htrans : IsTransverse n N E) (I : GermIdeal n M) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) (d : ℕ) (v : Val) {x : M} (hx : x ∈ N) :
    ∃ B : Set M, IsComplexAnalyticSubset (n := n) B ∧
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        B ∩ U = {y | y ∈ N ∧ (v : WithBot Val) ≤ gammaAlong n N I E d y} ∩ U := by
  classical
  let a := expDataAlong n N I E x
  let F := (feasible (memberIdx E x) a d).filter (fun K => v ≤ key n a K)
  let B := ⋃ K ∈ F, N ∩ BoundaryCount.memberInter E (topIdx E (key n a K))
  have hB : IsComplexAnalyticSubset (n := n) B := by
    let L := F.toList.map (fun K => (N ∩ BoundaryCount.memberInter E (topIdx E (key n a K)), K))
    have hL := HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_biUnion_list L (by
      intro p hp
      obtain ⟨K, -, rfl⟩ := List.mem_map.mp hp
      exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hE htrans _))
    have heq : (⋃ p ∈ L, p.1) = B := by
      ext y
      simp [L, B]
    rwa [heq] at hL
  have hev := (eventually_memberIdx_subset E hE.1 x).and
    (eventually_expDataAlong_eq hn hN hE htrans hI hne hx)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hev
  refine ⟨B, hB, U, hU, hxU, ?_⟩
  ext y
  constructor
  · rintro ⟨hyB, hyU⟩
    obtain ⟨K, hK, hyN, hyK⟩ := mem_iUnion₂.mp hyB
    obtain ⟨hKfeas, hKv⟩ := Finset.mem_filter.mp hK
    have hKsub := (mem_feasible.mp hKfeas).1
    have hlt : ∀ i ∈ topSet (key n a K), i < E.length := fun i hi =>
      (mem_memberIdx E).mp (hKsub hi) |>.choose
    have hKy : K ⊆ memberIdx E y := (mem_memberInter_topIdx_iff hlt).mp hyK
    have hKg : K ∈ feasible (memberIdx E y) a d :=
      mem_feasible.mpr ⟨hKy, (mem_feasible.mp hKfeas).2⟩
    have hg : (v : WithBot Val) ≤ inv n (memberIdx E y) a d :=
      (le_inv_iff_exists_feasible _ _ _ _).mpr ⟨K, hKg, hKv⟩
    have he : gammaAlong n N I E d y = inv n (memberIdx E y) a d :=
      inv_congr ((hUsub hyU).2 hyN)
    exact ⟨⟨hyN, he.symm ▸ hg⟩, hyU⟩
  · rintro ⟨⟨hyN, hgv⟩, hyU⟩
    have he : gammaAlong n N I E d y = inv n (memberIdx E y) a d :=
      inv_congr ((hUsub hyU).2 hyN)
    rw [he] at hgv
    obtain ⟨K, hKg, hKv⟩ := (le_inv_iff_exists_feasible _ _ _ _).mp hgv
    have hKsub := (mem_feasible.mp hKg).1
    have hKx : K ⊆ memberIdx E x := hKsub.trans (hUsub hyU).1
    have hKfeas : K ∈ feasible (memberIdx E x) a d :=
      mem_feasible.mpr ⟨hKx, (mem_feasible.mp hKg).2⟩
    have hlt : ∀ i ∈ topSet (key n a K), i < E.length := fun i hi =>
      (mem_memberIdx E).mp (hKx hi) |>.choose
    exact ⟨mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKfeas, hKv⟩,
      hyN, (mem_memberInter_topIdx_iff hlt).mpr hKsub⟩, hyU⟩

/-- Genuine exponent freezing and actual local equations make every monomial
superlevel globally analytic; USC is used only for its closedness. -/
theorem isComplexAnalyticSubset_gammaAlong_superlevel (hn : 0 < n) (N : Set M)
    (hN : IsClosedSubmanifold n N) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (htrans : IsTransverse n N E) (I : GermIdeal n M) (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) (d : ℕ) (v : WithBot Val) :
    IsComplexAnalyticSubset (n := n) {y | y ∈ N ∧ v ≤ gammaAlong n N I E d y} := by
  cases v with
  | bot => simpa using AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN
  | coe v =>
    have husc : ResolutionInvariantOrder.IsInvUSCOn (gammaAlong n N I E d) N :=
      fun _ hx => eventually_gammaAlong_le hn hN hE htrans hI hne d hx
    apply analytic_of_closed_locally_analytic (husc.isClosed_superlevel hN.1 v)
    intro x hx
    exact exists_analytic_near_gammaAlong_superlevel hn N hN E hE htrans I hI hne d v hx.1

section Canonical

universe u
variable {k : ℕ} {X Y : CMfd.{u} n}

/-- The actual canonical superlevel at a monomial threshold is exactly the
union of its positive first-entry locus and its actual monomial superlevel. -/
theorem canonical_monomial_superlevel_eq_union (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (T : BlowupTower X Y) (v : WithBot Val) :
    {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
      (toLex (0, toLex (Sum.inl v)) : ValTy (k + 1)) ≤
        (invFamily hn (k + 1)).inv 𝔪 T y} =
      {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
        1 ≤ (ofLex ((invFamily hn (k + 1)).inv 𝔪 T y)).1} ∪
      {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
        v ≤ gammaAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
          (geoTransformAlong 𝔪 T).E (geoTransformAlong 𝔪 T).d y} := by
  ext y
  let lower := fun {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) =>
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) 𝔍 S z
  have he : (invFamily hn (k + 1)).inv 𝔪 T y = genInv lower 𝔪 T y := rfl
  simp only [mem_ofPred_eq, mem_union, he]
  by_cases ho : NonmonomialOrderLocal.nmOrd (geoTransformAlong 𝔪 T) y = 0
  · rw [genInv_of_nmOrd_eq_zero lower 𝔪 T ho]
    simp [Prod.Lex.toLex_le_toLex]
  · have hp : 0 < NonmonomialOrderLocal.nmOrd (geoTransformAlong 𝔪 T) y :=
      Nat.pos_of_ne_zero ho
    have hfirst : 1 ≤ (ofLex (genInv lower 𝔪 T y)).1 := hp
    have hvalue : (toLex (0, toLex (Sum.inl v)) : ValTy (k + 1)) ≤
        genInv lower 𝔪 T y := by
      rw [genInv, Prod.Lex.toLex_le_toLex]
      exact Or.inl hp
    constructor
    · exact fun h => Or.inl ⟨h.1, hfirst⟩
    · rintro (h | h)
      · exact ⟨h.1, hvalue⟩
      · exact ⟨h.1, hvalue⟩

/-- Genuine canonical monomial-threshold superlevels are globally analytic
along actual test towers, using actual transformed ideal/boundary geometry. -/
theorem isComplexAnalyticSubset_canonical_monomial_superlevel (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : IsInvDomain (n := n) (k + 1) 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (v : WithBot Val) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
        (toLex (0, toLex (Sum.inl v)) : ValTy (k + 1)) ≤
          (invFamily hn (k + 1)).inv 𝔪 T y} := by
  rw [canonical_monomial_superlevel_eq_union hn 𝔪 T v]
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
    (isComplexAnalyticSubset_canonical_first_superlevel hn 𝔪 h T hT 1)
    (isComplexAnalyticSubset_gammaAlong_superlevel hn _ hd.isWellFormed.isClosedSubmanifold_N
      _ hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse
      _ hd.isWellFormed.isCoherent hd.isNonzeroAlongAt _ v)

end Canonical

end
end Hironaka.HironakaMonomialAnalyticSuperlevels
