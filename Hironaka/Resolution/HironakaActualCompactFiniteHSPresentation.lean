/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantSingularCentre

/-! Original coherence and compact support internally produce finite-order presentations of genuine whole HS strata. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCompactFiniteHSPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaHolomorphicJetChartInvariance HironakaActualWholeAmbientHSSuperlevel
  HironakaActualReferenceHSSingularCentre HironakaActualHSConstantSingularCentre
  BlowupTowers AnalyticDimensionBasics
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ONLY original coherence gives one internally produced finite HS prefix on any actual compact carrier. -/
theorem exists_actual_compact_whole_hs_uniform_finite_prefix
    (A : GermIdeal n M) (hA : A.IsCoherent) (h : ℕ → ℕ) {K : Set M} (hK : IsCompact K) :
    ∃ N, actualWholeAmbientHSSuperlevel A h ∩ K = actualAmbientHSFinitePrefix A h N ∩ K := by
  choose k U hU hx hEq using exists_original_local_whole_ambient_hs_prefix A hA h
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover U hU (fun x _ => mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨t.sup k,?_⟩
  ext x
  constructor
  · rintro ⟨hh,hxK⟩
    exact ⟨actualWholeAmbientHSSuperlevel_subset_prefix A h (t.sup k) hh,hxK⟩
  · rintro ⟨hh,hxK⟩
    obtain ⟨p,hpt,hxp⟩ := mem_iUnion₂.mp (ht hxK)
    have hle : k p ≤ t.sup k := Finset.le_sup hpt
    have hp : x ∈ actualAmbientHSFinitePrefix A h (k p) :=
      actualAmbientHSFinitePrefix_antitone A h hle hh
    have hall : x ∈ actualWholeAmbientHSSuperlevel A h ∩ U p := (hEq p).symm ▸ ⟨hp,hxp⟩
    exact ⟨hall.1,hxK⟩

/-- Actual compact support and a genuine positive zeroth threshold give BOTH WHOLE ambient finite-prefix directions. -/
theorem exists_actual_compact_support_whole_ambient_finite_hs_prefix
    (A : GermIdeal n M) (hA : A.IsCoherent) (hK : IsCompact A.zeroLocus)
    (h : ℕ → ℕ) (h0 : 1 ≤ h 0) :
    ∃ N, actualWholeAmbientHSSuperlevel A h = actualAmbientHSFinitePrefix A h N := by
  obtain ⟨N,hEq⟩ := exists_actual_compact_whole_hs_uniform_finite_prefix A hA h hK
  refine ⟨N,?_⟩
  ext x
  constructor
  · intro hx
    exact actualWholeAmbientHSSuperlevel_subset_prefix A h N hx
  · intro hx
    have hx0 := (mem_actualAmbientHSFinitePrefix A h N x).mp hx 0 (Nat.zero_le N)
    have hxS := (one_le_hilbertSamuelAt_zero_iff A hA x).mp (h0.trans hx0)
    exact ((Set.ext_iff.mp hEq x).mpr ⟨hx,hxS⟩).1

/-- ONLY original analytic compact geometry produces the ENTIRE finite presentation of the SAME genuine reduced reference. -/
theorem exists_actual_compact_reduced_reference_finite_hs_prefix {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {a : M} (ha : a ∈ W) :
    ∃ N, actualReferenceHSLocus (vanishingIdeal (n := n) W) a =
      actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N := by
  let A := vanishingIdeal (n := n) W
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hz : A.zeroLocus = W := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed
  have h0 : 1 ≤ hilbertSamuelAt A a 0 :=
    (one_le_hilbertSamuelAt_zero_iff A hA a).mpr (hz.symm ▸ ha)
  exact exists_actual_compact_support_whole_ambient_finite_hs_prefix A hA (hz.symm ▸ hK)
    (hilbertSamuelAt A a) h0

/-- The produced singular maximum has a true finite original presentation and EVERY actual HS order is constant on that ENTIRE set. -/
theorem exists_actual_original_constant_maximal_singular_finite_hs_prefix
    {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W) :
    ∃ (a : X) (N : ℕ), a ∈ W \ regularLocus (n := n) W d ∧
      actualReferenceHSLocus (vanishingIdeal (n := n) W) a =
        actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N ∧
      (actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N).Nonempty ∧
      IsComplexAnalyticSubset (n := n) (actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N) ∧
      IsCompact (actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N) ∧
      actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N ⊆ W \ regularLocus (n := n) W d ∧
      ∀ x ∈ actualAmbientHSFinitePrefix (vanishingIdeal (n := n) W)
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a) N, ∀ i,
        hilbertSamuelAt (vanishingIdeal (n := n) W) x i =
          hilbertSamuelAt (vanishingIdeal (n := n) W) a i := by
  obtain ⟨a,ha,_hmax,hne,hs,hk,hsub,hconst⟩ :=
    exists_actual_original_singular_constant_maximal_hs_locus hW hK hd hpure hns
  obtain ⟨N,hEq⟩ := exists_actual_compact_reduced_reference_finite_hs_prefix hW hK ha.1
  exact ⟨a,N,ha,hEq,hEq ▸ hne,hEq ▸ hs,hEq ▸ hk,hEq ▸ hsub,hEq ▸ hconst⟩

end
end Hironaka.HironakaActualCompactFiniteHSPresentation
