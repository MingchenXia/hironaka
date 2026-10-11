/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaAnalyticCentreExtension
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Invariant.CanonicalCentres
import Mathlib.Data.List.Lex

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual analytic superlevels of coherent ideal-order tuples

Finite recursion constructs the analytic locus and identifies it with the
actual extended-natural lexicographic order tuple. This does not assert that
an arbitrary enhanced resolution invariant has a global tuple presentation.
Blueprint: `hironaka-order-tuple-superlevels-extension.tex`.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaOrderTupleAnalyticSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealOrder HironakaEmbeddedDimensionParts HironakaDimensionGlobalComponents
  HironakaAnalyticCentreExtension AnalyticDimensionBasics GlobalComponents RegularLocusComponent
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal MonomialPartAlong CanonicalCentres

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite construction from actual ideal-order cosupports. -/
def orderTupleSuperlevel (N : Set M) : List (GermIdeal n M × ℕ) → Set M
  | [] => N
  | p :: L => cosupport n N p.1 (p.2 + 1) ∪
      (cosupport n N p.1 p.2 ∩ orderTupleSuperlevel N L)

private theorem cons_le_cons_iff (a b : ℕ∞) (s t : List ℕ∞) :
    a :: s ≤ b :: t ↔ a < b ∨ (a ≤ b ∧ s ≤ t) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · change List.Lex (· < ·) (a :: s) (b :: t) at h
      cases h with
      | rel h => exact Or.inl h
      | cons h => exact Or.inr ⟨le_rfl, le_of_lt h⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact Or.inr ⟨le_rfl, le_rfl⟩
  · rintro (h | ⟨hab, hst⟩)
    · exact le_of_lt (show List.Lex (· < ·) (a :: s) (b :: t) from .rel h)
    · by_cases hlt : a < b
      · exact le_of_lt (show List.Lex (· < ·) (a :: s) (b :: t) from .rel hlt)
      · obtain rfl := le_antisymm hab (not_lt.mp hlt)
        exact List.cons_le_cons _ hst

omit [IsComplexManifold n M] in
/-- The constructed locus is exactly the actual extended-natural order-tuple
lexicographic superlevel, including infinite orders and zero thresholds. -/
theorem mem_orderTupleSuperlevel_iff (N : Set M) (L : List (GermIdeal n M × ℕ))
    (hL : ∀ p ∈ L, p.1.IsCoherent) (x : M) :
    x ∈ orderTupleSuperlevel N L ↔ x ∈ N ∧
      L.map (fun p => (p.2 : ℕ∞)) ≤ L.map (fun p => order n N p.1 x) := by
  induction L with
  | nil => simp [orderTupleSuperlevel]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht : ∀ q ∈ L, q.1.IsCoherent := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hhol : ∀ g, p.1.mem x g → HolomorphicAt n g x :=
      fun _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hp hg
    have hstrict : (p.2 : ℕ∞) < order n N p.1 x ↔ OrderGE n N p.1 x (p.2 + 1) := by
      rw [← ENat.natCast_add_one_le_iff]
      simpa only [Nat.cast_add, Nat.cast_one] using (le_order_iff hhol (q := p.2 + 1))
    simp only [orderTupleSuperlevel, mem_union, mem_inter_iff, ih ht,
      List.map_cons, cons_le_cons_iff, cosupport, mem_ofPred_eq]
    rw [← hstrict, ← le_order_iff hhol]
    tauto

/-- Actual coherent derivative ideals, rather than a superlevel certificate,
make the constructed lexicographic locus globally analytic. -/
theorem isComplexAnalyticSubset_orderTupleSuperlevel (N : Set M)
    (hN : IsClosedSubmanifold n N) (L : List (GermIdeal n M × ℕ))
    (hL : ∀ p ∈ L, p.1.IsCoherent) :
    IsComplexAnalyticSubset (n := n) (orderTupleSuperlevel N L) := by
  have hNa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN
  induction L with
  | nil => exact hNa
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht : ∀ q ∈ L, q.1.IsCoherent := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hfirst := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hp hN
      (Nat.succ_pos p.2)
    have hweak : IsComplexAnalyticSubset (n := n) (cosupport n N p.1 p.2) := by
      by_cases hz : p.2 = 0
      · rw [hz, cosupport_zero (fun _ _ hg =>
          RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hp hg)]
        exact hNa
      · exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hp hN
          (Nat.pos_of_ne_zero hz)
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hfirst
      (hweak.inter (ih ht))

/-- Genuine global dimensional components extend the actual regular local
trace of a coherent ideal-order tuple superlevel. -/
theorem exists_pure_global_extension_of_regular_tuple_superlevel
    (N : Set M) (hN : IsClosedSubmanifold n N) (L : List (GermIdeal n M × ℕ))
    (hL : ∀ p ∈ L, p.1.IsCoherent) (q : ℕ) (U : Set M) (_hU : IsOpen U)
    (hreg : ∀ x ∈ orderTupleSuperlevel N L, x ∈ U →
      RegularAtDim (n := n) (orderTupleSuperlevel N L) x q) :
    ∃ T : Set M, IsComplexAnalyticSubset (n := n) T ∧
      IsPureDim (n := n) T q ∧ T ⊆ orderTupleSuperlevel N L ∧
      T ∩ U = orderTupleSuperlevel N L ∩ U ∧
      (∀ x ∈ T, x ∈ U → RegularAtDim (n := n) T x q) ∧
      T = ⋃₀ {B | B ∈ globalComponents (n := n) (orderTupleSuperlevel N L) ∧
        IsPureDim (n := n) B q} := by
  have hA := isComplexAnalyticSubset_orderTupleSuperlevel N hN L hL
  refine ⟨dimensionPart (n := n) (orderTupleSuperlevel N L) q,
    isComplexAnalyticSubset_dimensionPart hA q,
    HironakaDimensionGlobalComponents.isPureDim_dimensionPart hA q,
    dimensionPart_subset hA.isClosed q,
    dimensionPart_inter_eq_of_regularOn hA.isClosed q hreg, ?_,
    dimensionPart_eq_sUnion_globalComponents hA q⟩
  intro x hxT hxU
  exact regularAtDim_dimensionPart_of_regularAtDim hA.isClosed
    (hreg x (dimensionPart_subset hA.isClosed q hxT) hxU)

section Canonical

universe u
variable {k : ℕ} {X Y : CMfd.{u} n}

private theorem natCast_nmOrd_eq_order (𝔪 : MarkedIdeal n Y)
    (h : IsInvDomain (n := n) (k + 1) 𝔪) (hn : 0 < n) {y : Y} (hy : y ∈ 𝔪.N) :
    (nmOrd 𝔪 y : ℕ∞) = order n 𝔪.N (nmPart 𝔪) y := by
  have hcoh := isCoherent_nonmonomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent
    h.isNonzeroAlongAt
  apply ENat.eq_of_forall_natCast_le_iff
  intro μ
  rw [ENat.natCast_le_natCast, le_order_iff
    (fun _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
  exact (mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt hy μ).symm.trans
    ⟨fun hx => hx.2, fun hx => ⟨hy, hx⟩⟩

/-- The genuine constructed canonical first entry is presented by its actual
nonmonomial ideal, rather than a caller-supplied order tuple. -/
theorem canonical_first_superlevel_eq_orderTupleSuperlevel (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : IsInvDomain (n := n) (k + 1) 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (μ : ℕ) :
    {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
      μ ≤ (ofLex ((invFamily hn (k + 1)).inv 𝔪 T y)).1} =
      orderTupleSuperlevel (geoTransformAlong 𝔪 T).N
        [(nmPart (geoTransformAlong 𝔪 T), μ)] := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hcoh := isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent
    hd.isNonzeroAlongAt
  ext y
  rw [mem_ofPred_eq, mem_orderTupleSuperlevel_iff _ _ (by simpa using hcoh) y]
  simp only [List.map_cons, List.map_nil, cons_le_cons_iff, le_refl, and_true]
  have hfst : (ofLex ((invFamily hn (k + 1)).inv 𝔪 T y)).1 =
      nmOrd (geoTransformAlong 𝔪 T) y := rfl
  rw [hfst]
  constructor
  · rintro ⟨hy, hμ⟩
    refine ⟨hy, Or.inr ?_⟩
    rw [← natCast_nmOrd_eq_order _ hd hn hy, ENat.natCast_le_natCast]
    exact hμ
  · rintro ⟨hy, hμ | hμ⟩
    · refine ⟨hy, ?_⟩
      rw [← natCast_nmOrd_eq_order _ hd hn hy] at hμ
      exact (ENat.natCast_lt_natCast.mp hμ).le
    · refine ⟨hy, ?_⟩
      rw [← natCast_nmOrd_eq_order _ hd hn hy, ENat.natCast_le_natCast] at hμ
      exact hμ

/-- Actual canonical first-entry superlevels are globally analytic along every
genuine test tower, by internally produced nonmonomial ideal coherence. -/
theorem isComplexAnalyticSubset_canonical_first_superlevel (hn : 0 < n)
    (𝔪 : MarkedIdeal n X) (h : IsInvDomain (n := n) (k + 1) 𝔪)
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (μ : ℕ) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong 𝔪 T).N ∧
        μ ≤ (ofLex ((invFamily hn (k + 1)).inv 𝔪 T y)).1} := by
  rw [canonical_first_superlevel_eq_orderTupleSuperlevel hn 𝔪 h T hT μ]
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hcoh := isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent
    hd.isNonzeroAlongAt
  exact isComplexAnalyticSubset_orderTupleSuperlevel _ hd.isWellFormed.isClosedSubmanifold_N
    _ (by simpa using hcoh)

end Canonical

end
end Hironaka.HironakaOrderTupleAnalyticSuperlevels
